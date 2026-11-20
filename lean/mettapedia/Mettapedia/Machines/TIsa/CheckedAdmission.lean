import Mettapedia.Machines.TIsa.Admission
import Mettapedia.Machines.TIsa.Continuation

/-!
# Executable admission of proposed control/data updates

The checker selects an immutable source edge, reads the current PC and input
words, checks its actual guard and footprint, and derives the next PC from the
edge. Proposals supply data values; they supply neither an arbitrary guard nor
a semantic-correctness proof. Changes outside the declared writes are ignored.

Accepted proposals realize exactly the existing guarded resource transitions.
This is the checked admission contract, not a claim that the native/C host has
already wired it into its sealed commit boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.CheckedAdmission
open Cells CellEffects Control
universe u
variable {Key : Type u} [DecidableEq Key]

def proposal (edge : Edge Key) (before : Location Key → Word) (candidate : Key → Word) : Location Key → Word
  | .inl activation => if activation = edge.activation then edge.next else before (.inl activation)
  | .inr key => candidate key

def eligible (edge : Edge Key) (keys : Finset (Location Key)) (before : Location Key → Word) (candidate : Key → Word) : Prop :=
  edge.recipe.support ⊆ keys ∧ before (.inl edge.activation) = edge.point ∧
    edge.effect.guard (edge.effect.inputs.map (fun key => before (.inr key))) (edge.effect.outputs.map candidate) = true

instance (edge : Edge Key) (keys : Finset (Location Key)) (before : Location Key → Word) (candidate : Key → Word) :
    Decidable (eligible edge keys before candidate) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def commit (edge : Edge Key) (before : Location Key → Word) (candidate : Key → Word) : Location Key → Word :=
  edge.finish before (proposal edge before candidate)

def step? (edges : List (Edge Key)) (index : Nat) (keys : Finset (Location Key))
    (before : Location Key → Word) (candidate : Key → Word) : Option (Location Key → Word) :=
  match edges[index]? with
  | none => none
  | some edge => if eligible edge keys before candidate then some (commit edge before candidate) else none

theorem step_iff (edges : List (Edge Key)) (index : Nat) (keys : Finset (Location Key))
    (before : Location Key → Word) (candidate : Key → Word) (after : Location Key → Word) :
    step? edges index keys before candidate = some after ↔
      ∃ edge, edges[index]? = some edge ∧ eligible edge keys before candidate ∧ after = commit edge before candidate := by
  cases selected : edges[index]? with
  | none => simp [step?,selected]
  | some edge =>
      by_cases yes : eligible edge keys before candidate
      · simp [step?,selected,yes,eq_comm]
      · simp [step?,selected,yes]

omit [DecidableEq Key] in
theorem proposal_guard (edge : Edge Key) (before : Location Key → Word) (candidate : Key → Word) :
    edge.recipe.guard (edge.recipe.inputs.map before) (edge.recipe.outputs.map (proposal edge before candidate)) = true ↔
      before (.inl edge.activation) = edge.point ∧
        edge.effect.guard (edge.effect.inputs.map (fun key => before (.inr key))) (edge.effect.outputs.map candidate) = true := by
  rw [Edge.guard_iff]
  simp [proposal]

theorem step_sound (edges : List (Edge Key)) (index : Nat) (keys : Finset (Location Key))
    (before : Location Key → Word) (candidate : Key → Word) (after : Location Key → Word)
    (checked : step? edges index keys before candidate = some after) :
    (edgeProgram edges).theory.rewrites (encode keys before) (encode keys after) := by
  obtain ⟨edge,selected,allowed,rfl⟩ := (step_iff edges index keys before candidate after).mp checked
  apply (edgeProgram_rewrite_iff edges keys before _).mpr
  exact ⟨edge,List.mem_of_getElem? selected,proposal edge before candidate,allowed.1,allowed.2.1,
    by simp [proposal],allowed.2.2,rfl⟩

theorem commit_from_after (edge : Edge Key) (before after : Location Key → Word) :
    commit edge before (fun key => after (.inr key)) = edge.finish before after := by
  funext location
  cases location <;> rfl

theorem step_complete (edges : List (Edge Key)) (keys : Finset (Location Key))
    (before : Location Key → Word) (result : Multiset (Cell (Location Key)))
    (step : (edgeProgram edges).theory.rewrites (encode keys before) result) :
    ∃ index candidate after, step? edges index keys before candidate = some after ∧ result = encode keys after := by
  obtain ⟨edge,member,after,included,point,_,guarded,rfl⟩ := (edgeProgram_rewrite_iff edges keys before result).mp step
  obtain ⟨index,selected⟩ := List.mem_iff_get.mp member
  let candidate := fun key => after (.inr key)
  refine ⟨index.val,candidate,edge.finish before after,?_,rfl⟩
  apply (step_iff edges index.val keys before candidate _).mpr
  exact ⟨edge,List.getElem?_eq_getElem index.isLt |>.trans (congrArg some selected),⟨included,point,guarded⟩,
    (commit_from_after edge before after).symm⟩

theorem step_rewrite_iff (edges : List (Edge Key)) (keys : Finset (Location Key))
    (before : Location Key → Word) (result : Multiset (Cell (Location Key))) :
    (edgeProgram edges).theory.rewrites (encode keys before) result ↔
      ∃ index candidate after, step? edges index keys before candidate = some after ∧ result = encode keys after := by
  constructor
  · exact step_complete edges keys before result
  · rintro ⟨index,candidate,after,checked,rfl⟩
    exact step_sound edges index keys before candidate after checked

theorem commit_other_data (edge : Edge Key) (before : Location Key → Word) (candidate : Key → Word)
    (key : Key) (outside : key ∉ edge.effect.writes) : commit edge before candidate (.inr key) = before (.inr key) := by
  simp [commit,Edge.finish,overwrite,outside]

theorem commit_other_control (edge : Edge Key) (before : Location Key → Word) (candidate : Key → Word)
    (activation : Nat) (different : activation ≠ edge.activation) :
    commit edge before candidate (.inl activation) = before (.inl activation) := by
  simp [commit,Edge.finish,different]

namespace Controls
private def addition : Recipe Nat where
  inputs := [0,1]
  outputs := [0]
  guard := fun inputs outputs => match inputs,outputs with
    | [left,right],[result] => result == left + right
    | _,_ => false
private def edge : Edge Nat := ⟨0,7,8,addition⟩
private def keys : Finset (Location Nat) := {.inl 0,.inr 0,.inr 1}
private def before : Location Nat → Word := fun _ => 7
private def good : Nat → Word := fun key => if key = 0 then 14 else 99
private def bad : Nat → Word := fun key => if key = 0 then 15 else 99

theorem correct_result : step? [edge] 0 keys before good = some (commit edge before good) := by rfl
theorem wrong_result : step? [edge] 0 keys before bad = none := by rfl
theorem missing_read : step? [edge] 0 ({.inl 0,.inr 0} : Finset (Location Nat)) before good = none := by rfl
theorem missing_opcode : step? [edge] 1 keys before good = none := by rfl
theorem wrong_pc : step? [edge] 0 keys (fun _ => (9#64)) good = none := by rfl
theorem observed : commit edge before good (.inl 0) = (8#64) ∧ commit edge before good (.inr 0) = (14#64) ∧
    commit edge before good (.inr 1) = (7#64) := by exact ⟨rfl,rfl,rfl⟩
end Controls

#print axioms step_sound
#print axioms step_complete
#print axioms step_rewrite_iff
end Mettapedia.Machines.TIsa.CheckedAdmission
