import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CheckedCells
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mathlib.Data.List.Dedup

/-!
# Checked cell updates with real occurrence effects

An occurrence is a cell location together with its generation. An update
consumes the old generations of exactly the written cells, keeps the other
input cells, and produces fresh generations of the written cells. Writing
the same word still replaces its occurrence.
Generations are logical occurrence indices, not a claimed native ABI field.

The immutable edge table supplies the actual input list, output list and
Boolean guard. Admission checks them using `CheckedAdmission.eligible`.
Physical enabling and the exact resulting occurrence set are derived below.
This is the ground machine-word fragment: it has no symbolic unknowns or
logical constraints. Its word values and control counter remain in the state
and its readout. It is not the general symbolic kernel's knowledge model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellOccurrences

open Mettapedia.Machines.TIsa
open Cells CellEffects Control
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe u
variable {Key : Type u} [DecidableEq Key]

abbrev Occurrence (Key : Type u) := Location Key × Nat

structure State (Key : Type u) where
  keys : Finset (Location Key)
  values : Location Key → Word
  generations : Location Key → Nat

def occurrence (state : State Key) (key : Location Key) : Occurrence Key :=
  (key, state.generations key)

omit [DecidableEq Key] in
theorem occurrence_injective (state : State Key) : Function.Injective (occurrence state) :=
  fun _ _ same => congrArg Prod.fst same

def present (state : State Key) : Finset (Occurrence Key) := state.keys.image (occurrence state)

structure Firing (edges : List (Edge Key)) where
  ordinal : Fin edges.length
  candidate : Key → Word

def Firing.edge {edges : List (Edge Key)} (firing : Firing edges) : Edge Key := edges[firing.ordinal]

def nextOccurrence (state : State Key) (key : Location Key) : Occurrence Key :=
  (key, state.generations key + 1)

def selection {edges : List (Edge Key)} (state : State Key) (firing : Firing edges) : Selection (Occurrence Key) where
  taken := firing.edge.recipe.outputs.dedup.map (occurrence state)
  read := (firing.edge.recipe.inputs.dedup.filter fun key => key ∉ firing.edge.recipe.writes).map (occurrence state)
  made := firing.edge.recipe.outputs.dedup.map (nextOccurrence state)

@[simp] theorem selection_taken {edges : List (Edge Key)} (state : State Key) (firing : Firing edges) :
    (selection state firing).taken.toFinset = firing.edge.recipe.writes.image (occurrence state) := by
  ext row
  simp [selection, Recipe.writes]

@[simp] theorem selection_read {edges : List (Edge Key)} (state : State Key) (firing : Firing edges) :
    (selection state firing).read.toFinset = firing.edge.recipe.reads.image (occurrence state) := by
  ext row
  simp [selection, Recipe.reads]

@[simp] theorem selection_made {edges : List (Edge Key)} (state : State Key) (firing : Firing edges) :
    (selection state firing).made.toFinset = firing.edge.recipe.writes.image (nextOccurrence state) := by
  ext row
  simp [selection, Recipe.writes]

theorem physical_enabled {edges : List (Edge Key)} (state : State Key) (firing : Firing edges)
    (support : firing.edge.recipe.support ⊆ state.keys) :
    Enabled (fun _ : Occurrence Key => ()) (present state) ((selection state firing).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (selection state firing).taken.toFinset ⊆ present state
    rw [selection_taken]
    apply Finset.image_subset_image
    exact fun key member => support (Finset.mem_union_left _ member)
  · change (selection state firing).read.toFinset ⊆ present state
    rw [selection_read]
    apply Finset.image_subset_image
    intro key member
    exact support (Finset.mem_union_right _ (Finset.mem_sdiff.mp member).1)
  · change Disjoint (selection state firing).taken.toFinset (selection state firing).read.toFinset
    rw [selection_taken, selection_read]
    apply Finset.disjoint_left.mpr
    intro row written read
    obtain ⟨key, member, rfl⟩ := Finset.mem_image.mp written
    obtain ⟨other, read, same⟩ := Finset.mem_image.mp read
    have equal := occurrence_injective state same
    subst other
    exact (Finset.mem_sdiff.mp read).2 member
  · change Disjoint (selection state firing).made.toFinset (present state)
    rw [selection_made]
    apply Finset.disjoint_left.mpr
    intro row made old
    obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp made
    obtain ⟨other, _, same⟩ := Finset.mem_image.mp old
    have equal := congrArg Prod.fst same
    change other = key at equal
    subst other
    have impossible := congrArg Prod.snd same
    change state.generations key = state.generations key + 1 at impossible
    omega
  · intro query member
    cases member

def result {edges : List (Edge Key)} (state : State Key) (firing : Firing edges) : State Key where
  keys := state.keys
  values := CheckedAdmission.commit firing.edge state.values firing.candidate
  generations key := if key ∈ firing.edge.recipe.writes then state.generations key + 1 else state.generations key

theorem occurrence_result {edges : List (Edge Key)} (state : State Key) (firing : Firing edges)
    (key : Location Key) :
    occurrence (result state firing) key =
      if key ∈ firing.edge.recipe.writes then nextOccurrence state key else occurrence state key := by
  by_cases written : key ∈ firing.edge.recipe.writes <;>
    simp [occurrence, result, nextOccurrence, written]

theorem present_result {edges : List (Edge Key)} (state : State Key) (firing : Firing edges)
    (support : firing.edge.recipe.support ⊆ state.keys) :
    present (result state firing) = fire (present state) ((selection state firing).commit (T := Unit)) := by
  change present (result state firing) =
    (present state \ (selection state firing).taken.toFinset) ∪ (selection state firing).made.toFinset
  rw [selection_taken, selection_made]
  ext row
  constructor
  · rintro member
    obtain ⟨key, key_mem, rfl⟩ := Finset.mem_image.mp member
    change key ∈ state.keys at key_mem
    rw [occurrence_result]
    by_cases written : key ∈ firing.edge.recipe.writes
    · rw [if_pos written]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨key, written, rfl⟩)
    · rw [if_neg written]
      apply Finset.mem_union_left
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨key, key_mem, rfl⟩, ?_⟩
      rintro old
      obtain ⟨other, old, same⟩ := Finset.mem_image.mp old
      exact written ((occurrence_injective state same) ▸ old)
  · intro member
    rcases Finset.mem_union.mp member with old | made
    · obtain ⟨old, untouched⟩ := Finset.mem_sdiff.mp old
      obtain ⟨key, key_mem, rfl⟩ := Finset.mem_image.mp old
      have missing : key ∉ firing.edge.recipe.writes :=
        fun written => untouched (Finset.mem_image.mpr ⟨key, written, rfl⟩)
      refine Finset.mem_image.mpr ⟨key, key_mem, ?_⟩
      rw [occurrence_result, if_neg missing]
    · obtain ⟨key, written, rfl⟩ := Finset.mem_image.mp made
      refine Finset.mem_image.mpr ⟨key, support (Finset.mem_union_left _ written), ?_⟩
      rw [occurrence_result, if_pos written]

/-- Closed machine cells have equality as conversion and no unknowns.
The term carrier is the actual nontrivial cell payload type. -/
def frames : Frames (fun _ : Unit => Cell (Location Key)) (fun _ _ : Unit => Unit) where
  E := Eq
  equivalence _ := eq_equivalence
  act _ cell := cell
  id _ := ()
  comp _ _ := ()
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves _ := fun equal => equal

omit [DecidableEq Key] in
theorem empty_solvable : (frames (Key := Key)).Solvable (a := ()) [] :=
  ⟨(), (), fun _ member => by cases member⟩

def effect (edges : List (Edge Key)) :
    EffectCore (frames (Key := Key)) (Occurrence Key) (State Key) (fun _ => Firing edges) where
  frame _ := ()
  knowledge _ := []
  present := present
  selection {s} firing := selection s firing
  target _ := ()
  extension _ := ()
  information _ := []
  information_refines _ := by
    intro b sigma solved
    exact Frames.models_nil _
  Shapes {s} firing := firing.edge.recipe.support ⊆ s.keys
  preparedResult {s} firing _ := result s firing
  present_preparedResult {s} firing prepared := present_result s firing prepared.1
  preparedSettle _ _ := ()
  result_refines _ _ := by
    intro b sigma solved
    exact Frames.models_nil _

def step (edges : List (Edge Key)) :
    Step (frames (Key := Key)) (Occurrence Key) (State Key) (fun _ => Firing edges) where
  toEffectCore := effect edges
  Admits {s} firing := CheckedAdmission.eligible firing.edge s.keys s.values firing.candidate
  admitted_prepares {s} firing admitted :=
    ⟨admitted.1, physical_enabled s firing admitted.1, empty_solvable⟩

theorem admitted_iff_checked (edges : List (Edge Key)) (state : State Key) (firing : Firing edges) :
    (step edges).Admits (s := state) firing ↔
      CheckedAdmission.step? edges firing.ordinal state.keys state.values firing.candidate =
        some (result state firing).values := by
  have selected : edges[firing.ordinal.val]? = some firing.edge :=
    List.getElem?_eq_getElem firing.ordinal.isLt
  simp only [CheckedAdmission.step?, selected]
  by_cases eligible : CheckedAdmission.eligible firing.edge state.keys state.values firing.candidate
  · simp [eligible, step, result]
  · simp [eligible, step]

theorem result_values (edges : List (Edge Key)) (state : State Key) (firing : Firing edges)
    (admitted : (step edges).Admits (s := state) firing) :
    ((step edges).result firing admitted).values =
      CheckedAdmission.commit firing.edge state.values firing.candidate := rfl

theorem result_cells (edges : List (Edge Key)) (state : State Key) (firing : Firing edges)
    (admitted : (step edges).Admits (s := state) firing) :
    CheckedCells.Accepted edges state.keys state.values ((step edges).result firing admitted).values :=
  ⟨firing.ordinal, firing.candidate, (admitted_iff_checked edges state firing).mp admitted⟩

theorem result_keys (edges : List (Edge Key)) (state : State Key) (firing : Firing edges)
    (admitted : (step edges).Admits (s := state) firing) :
    ((step edges).result firing admitted).keys = state.keys := rfl

#print axioms physical_enabled
#print axioms present_result
#print axioms admitted_iff_checked
#print axioms result_cells

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellOccurrences
