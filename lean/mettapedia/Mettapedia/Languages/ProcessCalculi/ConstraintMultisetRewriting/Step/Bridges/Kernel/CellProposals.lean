import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellOccurrences
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# The finite output observation of a raw cell proposal

A raw proposal is a total function on keys. Only the words at the selected
edge's output positions affect admission or the result. Canonicalization sets
all other proposal words to zero and preserves the actual check and complete
resulting state. This licenses that erasure at the declared machine interface;
it does not identify the raw firing witnesses themselves.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellProposals

open Mettapedia.Machines.TIsa Cells CellEffects Control
open CellOccurrences

universe u
variable {Key : Type u} [DecidableEq Key]

def outputWords (edge : Edge Key) (candidate : Key → Word) : List Word :=
  edge.effect.outputs.map candidate

private theorem map_agrees {α β : Type*} (keys : List α) (left right : α → β)
    (same : keys.map left = keys.map right) : ∀ key ∈ keys, left key = right key := by
  induction keys with
  | nil => simp
  | cons first rest ih =>
    have parts := List.cons.inj same
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · exact parts.1
    · exact ih parts.2 key member

theorem outputs_agree (edge : Edge Key) {left right : Key → Word}
    (same : outputWords edge left = outputWords edge right) :
    ∀ key ∈ edge.effect.writes, left key = right key := by
  intro key member
  exact map_agrees edge.effect.outputs left right same key (List.mem_toFinset.mp member)

def canonical (edge : Edge Key) (candidate : Key → Word) : Key → Word :=
  fun key => if key ∈ edge.effect.writes then candidate key else 0

theorem outputWords_canonical (edge : Edge Key) (candidate : Key → Word) :
    outputWords edge (canonical edge candidate) = outputWords edge candidate := by
  apply List.map_congr_left
  intro key member
  exact if_pos (List.mem_toFinset.mpr member)

theorem canonical_idempotent (edge : Edge Key) (candidate : Key → Word) :
    canonical edge (canonical edge candidate) = canonical edge candidate := by
  funext key
  by_cases written : key ∈ edge.effect.writes <;> simp [canonical, written]

theorem canonical_eq_iff (edge : Edge Key) (left right : Key → Word) :
    canonical edge left = canonical edge right ↔ outputWords edge left = outputWords edge right := by
  constructor
  · intro same
    exact (outputWords_canonical edge left).symm.trans
      ((congrArg (outputWords edge) same).trans (outputWords_canonical edge right))
  · intro same
    funext key
    by_cases written : key ∈ edge.effect.writes
    · simp [canonical, written, outputs_agree edge same key written]
    · exact (if_neg written).trans (if_neg written).symm

theorem eligible_iff_outputs (edge : Edge Key) (keys : Finset (Location Key))
    (before : Location Key → Word) {left right : Key → Word}
    (same : outputWords edge left = outputWords edge right) :
    CheckedAdmission.eligible edge keys before left ↔ CheckedAdmission.eligible edge keys before right := by
  unfold CheckedAdmission.eligible
  change (_ ∧ _ ∧ edge.effect.guard _ (outputWords edge left) = true) ↔
    (_ ∧ _ ∧ edge.effect.guard _ (outputWords edge right) = true)
  rw [same]

theorem commit_eq_outputs (edge : Edge Key) (before : Location Key → Word)
    {left right : Key → Word} (same : outputWords edge left = outputWords edge right) :
    CheckedAdmission.commit edge before left = CheckedAdmission.commit edge before right := by
  funext location
  cases location with
  | inl activation => rfl
  | inr key =>
    by_cases written : key ∈ edge.effect.writes
    · simpa [CheckedAdmission.commit, Edge.finish, overwrite, written, CheckedAdmission.proposal] using
        outputs_agree edge same key written
    · simp [CheckedAdmission.commit, Edge.finish, overwrite, written]

def normalize {edges : List (Edge Key)} (firing : Firing edges) : Firing edges :=
  ⟨firing.ordinal, canonical firing.edge firing.candidate⟩

theorem admission_normalize (edges : List (Edge Key)) (state : State Key) (firing : Firing edges) :
    (step edges).Admits (s := state) (normalize firing) ↔ (step edges).Admits (s := state) firing :=
  eligible_iff_outputs firing.edge state.keys state.values (outputWords_canonical firing.edge firing.candidate)

theorem result_normalize (edges : List (Edge Key)) (state : State Key) (firing : Firing edges) :
    result state (normalize firing) = result state firing := by
  change State.mk state.keys (CheckedAdmission.commit firing.edge state.values
    (canonical firing.edge firing.candidate)) _ = State.mk state.keys
      (CheckedAdmission.commit firing.edge state.values firing.candidate) _
  rw [commit_eq_outputs firing.edge state.values (outputWords_canonical firing.edge firing.candidate)]
  rfl

theorem normalize_idempotent {edges : List (Edge Key)} (firing : Firing edges) :
    normalize (normalize firing) = normalize firing := by
  cases firing with
  | mk ordinal candidate =>
    exact congrArg (Firing.mk ordinal) (canonical_idempotent edges[ordinal] candidate)

/-- The immutable table ordinal and its finite vector of output words. -/
abbrev OutputCode (edges : List (Edge Key)) :=
  (ordinal : Fin edges.length) × (Fin edges[ordinal].effect.outputs.length → Word)

def outputCode {edges : List (Edge Key)} (firing : Firing edges) : OutputCode edges :=
  ⟨firing.ordinal, fun index => firing.candidate firing.edge.effect.outputs[index]⟩

theorem outputCode_normalize {edges : List (Edge Key)} (firing : Firing edges) :
    outputCode (normalize firing) = outputCode firing := by
  apply congrArg (Sigma.mk firing.ordinal)
  funext index
  exact if_pos (List.mem_toFinset.mpr (List.getElem_mem index.isLt))

theorem normalize_eq_iff_code_eq {edges : List (Edge Key)} (first second : Firing edges) :
    normalize first = normalize second ↔ outputCode first = outputCode second := by
  constructor
  · intro same
    exact (outputCode_normalize first).symm.trans
      ((congrArg outputCode same).trans (outputCode_normalize second))
  · intro same
    rcases first with ⟨ordinal, left⟩
    rcases second with ⟨other, right⟩
    have ordinalEqual : ordinal = other := congrArg Sigma.fst same
    subst other
    have words : (fun index : Fin edges[ordinal].effect.outputs.length => left edges[ordinal].effect.outputs[index]) =
        (fun index : Fin edges[ordinal].effect.outputs.length => right edges[ordinal].effect.outputs[index]) :=
      eq_of_heq (Sigma.mk.inj same).2
    apply congrArg (Firing.mk ordinal)
    funext key
    change canonical edges[ordinal] left key = canonical edges[ordinal] right key
    by_cases written : key ∈ edges[ordinal].effect.writes
    · simp only [canonical, if_pos written]
      obtain ⟨index, atKey⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp written)
      have values := congrFun words index
      change left edges[ordinal].effect.outputs[index] = right edges[ordinal].effect.outputs[index] at values
      simpa only [show edges[ordinal].effect.outputs[index] = key from atKey] using values
    · exact (if_neg written).trans (if_neg written).symm

/-- Canonical proposal representatives are finite even when the raw key
type is infinite. No finite presentation of all raw functions is assumed. -/
theorem canonical_firings_finite (edges : List (Edge Key)) :
    Finite {firing : Firing edges // normalize firing = firing} := by
  have : Finite Word := Finite.of_injective BitVec.toFin (fun left right same => by
    cases left
    cases right
    cases same
    rfl)
  let : Fintype Word := Fintype.ofFinite Word
  have : Finite (OutputCode edges) := inferInstance
  apply Finite.of_injective (fun firing : {firing : Firing edges // normalize firing = firing} => outputCode firing.val)
  intro first second same
  apply Subtype.ext
  rw [← first.property, ← second.property]
  exact (normalize_eq_iff_code_eq first.val second.val).mpr same

/-- Each actual state has finitely many successor states. This follows
from the finite output observation, not from finiteness of raw proposals. -/
theorem successor_states_finite (edges : List (Edge Key)) (state : State Key) :
    Set.Finite {after : State Key | ∃ firing : Firing edges,
      (step edges).Admits (s := state) firing ∧ result state firing = after} := by
  have := canonical_firings_finite edges
  apply (Set.finite_range (fun firing : {firing : Firing edges // normalize firing = firing} =>
    result state firing.val)).subset
  rintro after ⟨firing, _, rfl⟩
  exact ⟨⟨normalize firing, normalize_idempotent firing⟩, result_normalize edges state firing⟩

namespace Controls

open CheckedCells.Controls (edge keys initial proposal)

def alternative : Nat → Word := Function.update proposal 2 42

theorem unused_proposals_are_distinct : proposal ≠ alternative := by
  intro same
  have atTwo := congrFun same 2
  change (99#64) = Function.update proposal 2 (42#64) 2 at atTwo
  simp only [Function.update_self] at atTwo
  exact (by decide : (99#64) ≠ (42#64)) atTwo

theorem unused_words_do_not_change_outputs : outputWords edge proposal = outputWords edge alternative := by decide

theorem unused_words_do_not_change_commit :
    CheckedAdmission.commit edge initial proposal = CheckedAdmission.commit edge initial alternative :=
  commit_eq_outputs edge initial unused_words_do_not_change_outputs

end Controls

#print axioms canonical_eq_iff
#print axioms eligible_iff_outputs
#print axioms commit_eq_outputs
#print axioms admission_normalize
#print axioms result_normalize
#print axioms normalize_eq_iff_code_eq
#print axioms canonical_firings_finite
#print axioms successor_states_finite
#print axioms Controls.unused_words_do_not_change_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellProposals
