import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameReindex
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations
import Mathlib.Data.Fintype.Sum

/-!
# Selecting one contextual declaration without losing its frame

An identity is moved to the distinguished port and every other declaration
retains its original identity, arity and context. The explicit equivalence
supplies the sound and complete frame transformation used by solver cases.
Only identity equality is needed; object sorts need not be decidable or finite.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]

abbrev Remaining (chosen : V) := {identity : V // identity ≠ chosen}

def split (chosen : V) : V ≃ Unit ⊕ Remaining chosen where
  toFun identity := if same : identity = chosen then .inl () else .inr ⟨identity, same⟩
  invFun identity := match identity with | .inl () => chosen | .inr other => other.val
  left_inv := by
    intro identity
    by_cases same : identity = chosen <;> simp [same]
  right_inv := by
    intro identity
    cases identity with
    | inl marker => cases marker; simp
    | inr other => simp [other.property]

abbrev declarations (source : V → MetaArity S) (chosen : V) : Unit ⊕ Remaining chosen → MetaArity S :=
  sumDeclarations (fun _ => source chosen) (fun other => source other.val)

theorem chosen_to_port (chosen : V) : split chosen chosen = .inl () := by simp [split]

theorem other_to_remaining (chosen identity : V) (different : identity ≠ chosen) :
    split chosen identity = .inr ⟨identity, different⟩ := by simp [split, different]

theorem forward_preserves (source : V → MetaArity S) (chosen identity : V) :
    declarations source chosen (split chosen identity) = source identity := by
  by_cases same : identity = chosen <;> simp [declarations, split, same, sumDeclarations]

theorem backward_preserves (source : V → MetaArity S) (chosen : V)
    (identity : Unit ⊕ Remaining chosen) :
    source ((split chosen).symm identity) = declarations source chosen identity := by
  cases identity with
  | inl marker => cases marker; rfl
  | inr _ => rfl

theorem reduction (source : V → MetaArity S) (chosen : V) (problem : ContextualResidual.Problem source) :
    ContextualResidual.Reduction problem (reindex (split chosen) (forward_preserves source chosen))
      (ContextualResidual.mapProblem (reindex (split chosen) (forward_preserves source chosen)) problem) :=
  ContextualFrameReindex.reduction (split chosen) (split chosen).symm (forward_preserves source chosen)
    (backward_preserves source chosen) (split chosen).left_inv problem

theorem remaining_cardinality [Fintype V] (chosen : V) :
    Fintype.card (Remaining chosen) + 1 = Fintype.card V := by
  have same := Fintype.card_congr (split chosen)
  simp only [Fintype.card_sum, Fintype.card_unit] at same
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection
