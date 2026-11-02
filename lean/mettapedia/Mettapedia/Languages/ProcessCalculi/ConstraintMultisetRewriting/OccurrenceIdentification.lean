import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# The double-pushout identification condition is exactly the step's occurrence discipline

The rule's left side has one port per take and per read; its interface `K` is the read
ports. A selection is the match `m : L → occurrences`. The identification condition of
double-pushout rewriting says that `m` may identify two distinct ports only when both lie
in the interface. For the existing `Selection` fields this is exactly: the taken list has
no duplicates, and no taken occurrence is also read. Reads may alias (`[7, 7]`).

Rendering every read as a take (consume and republish) empties the interface, so the same
condition then demands an injective match on all ports and refuses `[7, 7]`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceIdentification

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {O : Type*} [DecidableEq O]

/-- The match of a selection on its ports: take ports on the left, read ports on the right. -/
def portMatch (selection : Selection O) : Fin selection.taken.length ⊕ Fin selection.read.length → O :=
  Sum.elim selection.taken.get selection.read.get

/-- Identification condition with the read ports as interface. -/
def IdentificationCondition (selection : Selection O) : Prop :=
  ∀ x y, x ≠ y → portMatch selection x = portMatch selection y → x.isRight ∧ y.isRight

theorem identification_iff (selection : Selection O) :
    IdentificationCondition selection ↔
      selection.taken.Nodup ∧ Disjoint selection.taken.toFinset selection.read.toFinset := by
  constructor
  · intro condition
    refine ⟨List.nodup_iff_injective_get.mpr ?_, ?_⟩
    · intro i j same
      by_contra different
      have both := condition (.inl i) (.inl j) (fun h => different (Sum.inl.inj h)) same
      simp at both
    · refine Finset.disjoint_left.mpr fun o taken read => ?_
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp read)
      have both := condition (.inl i) (.inr j) Sum.inl_ne_inr
        (by change selection.taken.get i = selection.read.get j; rw [hi, hj])
      simp at both
  · rintro ⟨distinct, apart⟩ x y different same
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            exact absurd (congrArg Sum.inl (List.nodup_iff_injective_get.mp distinct same))
              different
        | inr j =>
            exfalso
            have taken : selection.taken.get i ∈ selection.taken.toFinset :=
              List.mem_toFinset.mpr (List.get_mem _ _)
            have read : selection.taken.get i ∈ selection.read.toFinset := by
              have shared : selection.taken.get i = selection.read.get j := same
              rw [shared]
              exact List.mem_toFinset.mpr (List.get_mem _ _)
            exact Finset.disjoint_left.mp apart taken read
    | inr i =>
        cases y with
        | inl j =>
            exfalso
            have taken : selection.taken.get j ∈ selection.taken.toFinset :=
              List.mem_toFinset.mpr (List.get_mem _ _)
            have read : selection.taken.get j ∈ selection.read.toFinset := by
              have shared : selection.read.get i = selection.taken.get j := same
              rw [← shared]
              exact List.mem_toFinset.mpr (List.get_mem _ _)
            exact Finset.disjoint_left.mp apart taken read
        | inr j => exact ⟨rfl, rfl⟩

/-- Every valid step satisfies the identification condition. -/
theorem valid_identification {T S : Type*} {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    (valid : selection.Valid A label rule before) : IdentificationCondition selection :=
  (identification_iff selection).mpr ⟨valid.take_distinct, valid.occurrences.apart⟩

/-- Consume and republish: every read port becomes a take port, and the interface is empty. -/
def rendered (selection : Selection O) : Selection O :=
  ⟨selection.taken ++ selection.read, [], selection.made⟩

theorem rendered_identification_iff (selection : Selection O) :
    IdentificationCondition (rendered selection) ↔ (selection.taken ++ selection.read).Nodup := by
  rw [identification_iff]
  simp [rendered]

/-! ## Controls -/

def aliasedRead : Selection Nat := ⟨[], [7, 7], [9]⟩
def twoTakes : Selection Nat := ⟨[7, 7], [], [9]⟩
def readAndTake : Selection Nat := ⟨[7], [7], [9]⟩

theorem aliased_read_is_identified_inside_the_interface : IdentificationCondition aliasedRead :=
  (identification_iff _).mpr ⟨by decide, by decide⟩

theorem two_takes_of_one_row_are_refused : ¬ IdentificationCondition twoTakes := by
  rw [identification_iff]
  decide

theorem a_take_and_a_read_of_one_row_are_refused : ¬ IdentificationCondition readAndTake := by
  rw [identification_iff]
  decide

theorem consume_and_republish_refuses_the_aliased_read :
    ¬ IdentificationCondition (rendered aliasedRead) := by
  rw [rendered_identification_iff]
  decide


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceIdentification
