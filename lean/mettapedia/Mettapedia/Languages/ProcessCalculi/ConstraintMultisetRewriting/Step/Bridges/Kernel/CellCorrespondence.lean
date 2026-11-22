import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress

/-!
# Executable admission, occurrence firings and resource readouts compose

The occurrence implementation adds generations to the existing cell checker.
Each accepted checker call has an actual admitted firing, and every firing
reads back to one accepted call. Both directions hold from every generation
assignment. Projection to the existing resource theory preserves exactly the
declared cells. The composed correspondence adds no administrative divergence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellCorrespondence

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Machines.TIsa Cells CellEffects Control
open CellOccurrences

universe u
variable {Key : Type u} [DecidableEq Key]

abbrev target (edges : List (Edge Key)) : GSLT := Execution.theory (step edges)

def Represents (keys : Finset (Location Key)) (values : Location Key → Word) (state : State Key) : Prop :=
  state.keys = keys ∧ state.values = values

theorem accepted_has_firing (edges : List (Edge Key)) (state : State Key)
    {after : Location Key → Word} (accepted : CheckedCells.Accepted edges state.keys state.values after) :
    ∃ firing : Firing edges, ∃ admitted : (step edges).Admits (s := state) firing,
      ((step edges).result firing admitted).values = after := by
  obtain ⟨index, candidate, checked⟩ := accepted
  obtain ⟨edge, selected, eligible, endpoint⟩ :=
    (CheckedAdmission.step_iff edges index state.keys state.values candidate after).mp checked
  have within : index < edges.length := by
    by_contra beyond
    have absent : edges[index]? = none := List.getElem?_eq_none (Nat.le_of_not_gt beyond)
    rw [absent] at selected
    cases selected
  let firing : Firing edges := ⟨⟨index, within⟩, candidate⟩
  have same : firing.edge = edge :=
    Option.some.inj ((List.getElem?_eq_getElem within).symm.trans selected)
  have admitted : (step edges).Admits (s := state) firing := by
    change CheckedAdmission.eligible firing.edge state.keys state.values candidate
    rw [same]
    exact eligible
  refine ⟨firing, admitted, ?_⟩
  rw [result_values, same]
  exact endpoint.symm

theorem target_reflected (edges : List (Edge Key)) (keys : Finset (Location Key))
    {before : Location Key → Word} {current following : State Key}
    (represented : Represents keys before current) (moved : (target edges).Step current following) :
    ∃ after, (CheckedCells.source edges keys).Step before after ∧ Represents keys after following := by
  obtain ⟨firing, admitted, rfl⟩ := moved
  refine ⟨((step edges).result firing admitted).values, ?_, result_keys edges current firing admitted |>.trans represented.1, rfl⟩
  have accepted := result_cells edges current firing admitted
  change CheckedCells.Accepted edges keys before ((step edges).result firing admitted).values
  simpa only [represented.1, represented.2] using accepted

def readback (edges : List (Edge Key)) (keys : Finset (Location Key)) :
    OperationalReadback (CheckedCells.source edges keys) (target edges) where
  related := Represents keys
  readStep := fun represented moved => .inr (target_reflected edges keys represented moved)

def correspondence (edges : List (Edge Key)) (keys : Finset (Location Key)) :
    OperationalCorrespondence (CheckedCells.source edges keys) (target edges) where
  toOperationalReadback := readback edges keys
  forward := by
    intro before after current represented accepted
    change CheckedCells.Accepted edges keys before after at accepted
    have checked : CheckedCells.Accepted edges current.keys current.values after := by
      simpa only [represented.1, represented.2] using accepted
    obtain ⟨firing, admitted, endpoint⟩ := accepted_has_firing edges current checked
    exact ⟨(step edges).result firing admitted,
      ⟨.cons ⟨⟨firing, admitted, rfl⟩⟩ (.refl _)⟩,
      (result_keys edges current firing admitted).trans represented.1, endpoint⟩

def progress (edges : List (Edge Key)) (keys : Finset (Location Key)) :
    Progress.Certificate.{u,u,0} (readback edges keys) :=
  .ofReflection (target_reflected edges keys)

/-- Projection uses the original guarded cell theory and its original
admission proof. The occurrence generation is deliberately unobserved. -/
def toCells (edges : List (Edge Key)) : OperationalTranslation (target edges) (CheckedCells.target edges) where
  mapTerm state := encode state.keys state.values
  mapEquiv := by
    intro before after equal
    exact congrArg (fun state => encode state.keys state.values) equal
  mapStep := by
    rintro before after ⟨firing, admitted, rfl⟩
    have moved := CheckedCells.accepted_sound edges before.keys (result_cells edges before firing admitted)
    change (CheckedCells.target edges).Step (encode before.keys before.values)
      (encode before.keys ((step edges).result firing admitted).values)
    exact moved

theorem reachable_iff_actual_run (edges : List (Edge Key)) (keys : Finset (Location Key))
    (post : Multiset (Cell (Location Key)) → Prop) (before : Location Key → Word)
    (generations : Location Key → Nat) :
    (∃ after, (CheckedCells.source edges keys).MultiStep before after ∧ post (encode keys after)) ↔
      ∃ run : (step edges).Run (⟨keys, before, generations⟩ : State Key),
        post (encode run.last.keys run.last.values) := by
  refine ((correspondence edges keys).reachable_iff
    (fun values => post (encode keys values))
    (fun state => post (encode state.keys state.values))
    (fun represented => by rw [represented.1, represented.2])
    (show Represents keys before (⟨keys, before, generations⟩ : State Key) from ⟨rfl, rfl⟩)).trans ?_
  exact Execution.reachable_iff_run (step edges) _ _

/-- Normalization of the checked computation rules out a target execution
consisting only of occurrence bookkeeping. Every target step advances it. -/
theorem normalization_preserved (edges : List (Edge Key)) (keys : Finset (Location Key))
    {before : Location Key → Word} {current : State Key}
    (represented : Represents keys before current)
    (normalizing : Acc (fun after before => (CheckedCells.source edges keys).Step before after) before) :
    Acc (fun next state => (target edges).Step state next) current :=
  (progress edges keys).normalization_preserved normalizing represented

namespace Controls

open CheckedCells.Controls (edge keys initial proposal)

def state : State Nat := ⟨keys, initial, fun _ => 0⟩
def firing : Firing [edge] := ⟨⟨0, by decide⟩, proposal⟩

theorem admitted : (step [edge]).Admits (s := state) firing := by
  change CheckedAdmission.eligible firing.edge state.keys state.values firing.candidate
  decide

def run : (step [edge]).Run state := .cons firing admitted (.nil _)

theorem run_delivers :
    run.last.values (.inl 0) = (8#64) ∧ run.last.values (.inr 0) = (14#64) ∧
      run.last.values (.inr 1) = (7#64) := ⟨rfl, rfl, rfl⟩

theorem written_occurrence_replaced :
    ((.inr 0, 0) : Occurrence Nat) ∈ present state ∧
      ((.inr 0, 0) : Occurrence Nat) ∉ present run.last ∧
      ((.inr 0, 1) : Occurrence Nat) ∈ present run.last := by decide

theorem reader_kept : ((.inr 1, 0) : Occurrence Nat) ∈ present run.last := by decide

def sameWord : Edge Nat := { edge with
  next := 7
  effect := { inputs := [0], outputs := [0], guard := fun input output => input == output } }

def sameFiring : Firing [sameWord] := ⟨⟨0, by decide⟩, fun _ => 7⟩

theorem same_admitted : (step [sameWord]).Admits (s := state) sameFiring := by
  change CheckedAdmission.eligible sameFiring.edge state.keys state.values sameFiring.candidate
  decide

/-- Equal payloads do not make a write read-only. The old occurrence is
consumed and a fresh generation is present, even though all word values agree. -/
theorem same_word_changes_occurrence :
    (result state sameFiring).values = state.values ∧
      ((.inr 0, 0) : Occurrence Nat) ∉ present (result state sameFiring) ∧
      ((.inr 0, 1) : Occurrence Nat) ∈ present (result state sameFiring) := by
  refine ⟨?_, by decide, by decide⟩
  funext key
  cases key with
  | inl activation =>
    by_cases equal : activation = 0 <;>
      simp [result, CheckedAdmission.commit, Edge.finish,
        sameFiring, Firing.edge, sameWord, edge, state, initial, equal]
  | inr key =>
    by_cases equal : key = 0 <;>
      simp [result, CheckedAdmission.commit, CheckedAdmission.proposal, Edge.finish,
        sameFiring, Firing.edge, sameWord, edge, state, initial, overwrite, Recipe.writes, equal]

end Controls

#print axioms accepted_has_firing
#print axioms correspondence
#print axioms toCells
#print axioms reachable_iff_actual_run
#print axioms normalization_preserved
#print axioms Controls.same_word_changes_occurrence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellCorrespondence
