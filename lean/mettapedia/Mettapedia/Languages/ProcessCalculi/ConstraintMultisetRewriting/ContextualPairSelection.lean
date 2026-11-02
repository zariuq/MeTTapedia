import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection

/-!
# Selecting two distinct contextual declarations

Flexible-pair solving uses two distinguished ports. This executable change
of frame selects arbitrary old identities, retains their complete arities,
and leaves every other identity available. The declaration family need not
be finite. Equal identities instead belong to the same-hole solver case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]

abbrev Remaining (first second : V) := {identity : V // identity ≠ first ∧ identity ≠ second}

def split (first second : V) (different : first ≠ second) : V ≃ Bool ⊕ Remaining first second where
  toFun identity := if left : identity = first then .inl false
    else if right : identity = second then .inl true else .inr ⟨identity, left, right⟩
  invFun identity := match identity with
    | .inl false => first
    | .inl true => second
    | .inr other => other.val
  left_inv := by
    intro identity
    by_cases left : identity = first
    · simp [left]
    · by_cases right : identity = second <;> simp [left, right, Ne.symm different]
  right_inv := by
    intro identity
    cases identity with
    | inl marker => cases marker <;> simp [Ne.symm different]
    | inr other => simp [other.property.1, other.property.2]

abbrev declarations (source : V → MetaArity S) (first second : V) :
    Bool ⊕ Remaining first second → MetaArity S :=
  pairDeclarations (source first) (source second) (fun other => source other.val)

theorem first_to_port (first second : V) (different : first ≠ second) :
    split first second different first = .inl false := by simp [split]

theorem second_to_port (first second : V) (different : first ≠ second) :
    split first second different second = .inl true := by simp [split, Ne.symm different]

theorem other_to_remaining (first second identity : V) (different : first ≠ second)
    (left : identity ≠ first) (right : identity ≠ second) :
    split first second different identity = .inr ⟨identity, left, right⟩ := by simp [split, left, right]

theorem forward_preserves (source : V → MetaArity S) (first second : V)
    (different : first ≠ second) (identity : V) :
    declarations source first second (split first second different identity) = source identity := by
  by_cases left : identity = first
  · simp [declarations, pairDeclarations, sumDeclarations, split, left]
  · by_cases right : identity = second <;>
      simp [declarations, pairDeclarations, sumDeclarations, split, left, right, Ne.symm different]

theorem backward_preserves (source : V → MetaArity S) (first second : V)
    (different : first ≠ second) (identity : Bool ⊕ Remaining first second) :
    source ((split first second different).symm identity) = declarations source first second identity := by
  cases identity with
  | inl marker => cases marker <;> rfl
  | inr _ => rfl

theorem reduction (source : V → MetaArity S) (first second : V) (different : first ≠ second)
    (problem : ContextualResidual.Problem source) :
    ContextualResidual.Reduction problem
      (reindex (split first second different) (forward_preserves source first second different))
      (ContextualResidual.mapProblem
        (reindex (split first second different) (forward_preserves source first second different)) problem) :=
  ContextualFrameReindex.reduction (split first second different) (split first second different).symm
    (forward_preserves source first second different) (backward_preserves source first second different)
    (split first second different).left_inv problem

theorem remaining_cardinality [Fintype V] (first second : V) (different : first ≠ second) :
    Fintype.card (Remaining first second) + 2 = Fintype.card V := by
  have same := Fintype.card_congr (split first second different)
  simp only [Fintype.card_sum, Fintype.card_bool] at same
  omega

theorem ports_are_distinct (first second : V) (different : first ≠ second) :
    split first second different first ≠ split first second different second := by
  rw [first_to_port, second_to_port]
  exact Sum.inl_injective.ne Bool.false_ne_true

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection
