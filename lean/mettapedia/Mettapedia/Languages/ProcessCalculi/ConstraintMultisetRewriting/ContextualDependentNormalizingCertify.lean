import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingReduction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableJoin

/-!
# A complete normality certificate

For a rule package without declared root computation, the executable one-step strategy finds a
directed step whenever one exists: it tries every contraction and every congruence position. A
term is therefore normal exactly when the strategy proposes nothing, and that test is a normality
checker that is sound by construction and accepts every normal term.

Because the strategy commutes with renaming, normality is invariant under every renaming, in both
directions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizing

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ContextualDependentRenaming

variable {Head : Type} {R : Rules Head}

/-- **The one-step strategy is complete** for a root-free rule package: every directed step is
found. -/
theorem step_complete (empty : R.computation = RootComputation.empty) {n : Nat} {t u : Tm Head n}
    (reduces : StrongNormalization.Reduces R t u) : step R (fun _ => none) t ≠ none := by
  induction reduces with
  | betaPi body a => simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
  | betaSigmaFst a b => simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
  | betaSigmaSnd a b => simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
  | head same => exact False.elim same
  | root rootStep => exact (ContextualDependentExecutableJoin.no_root empty rootStep).elim
  | @congPiDom _ A A' B _ ih =>
      rw [step.eq_4]
      cases h : step R (fun _ => none) A with
      | none => exact absurd h ih
      | some _ => simp
  | @congPiCod _ A B B' _ ih =>
      rw [step.eq_4]
      cases step R (fun _ => none) A with
      | some _ => simp
      | none =>
          cases h : step R (fun _ => none) B with
          | none => exact absurd h ih
          | some _ => simp
  | @congSigmaDom _ A A' B _ ih =>
      rw [step.eq_5]
      cases h : step R (fun _ => none) A with
      | none => exact absurd h ih
      | some _ => simp
  | @congSigmaCod _ A B B' _ ih =>
      rw [step.eq_5]
      cases step R (fun _ => none) A with
      | some _ => simp
      | none =>
          cases h : step R (fun _ => none) B with
          | none => exact absurd h ih
          | some _ => simp
  | @congIdTy _ A A' a b _ ih =>
      rw [step.eq_6]
      cases h : step R (fun _ => none) A with
      | none => exact absurd h ih
      | some _ => simp
  | @congIdLeft _ A a a' b _ ih =>
      rw [step.eq_6]
      cases step R (fun _ => none) A with
      | some _ => simp
      | none =>
          cases h : step R (fun _ => none) a with
          | none => exact absurd h ih
          | some _ => simp
  | @congIdRight _ A a b b' _ ih =>
      rw [step.eq_6]
      cases step R (fun _ => none) A with
      | some _ => simp
      | none =>
          cases step R (fun _ => none) a with
          | some _ => simp
          | none =>
              cases h : step R (fun _ => none) b with
              | none => exact absurd h ih
              | some _ => simp
  | @congLam _ body body' _ ih =>
      rw [step.eq_7]
      cases h : step R (fun _ => none) body with
      | none => exact absurd h ih
      | some _ => simp
  | @congAppFun _ g g' a _ ih =>
      by_cases redex : ∃ body, g = .lam body
      · obtain ⟨body, rfl⟩ := redex
        simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [step.eq_9 R _ _ g a (fun body same => redex ⟨body, same⟩)]
        cases h : step R (fun _ => none) g with
        | none => exact absurd h ih
        | some _ => simp
  | @congAppArg _ g a a' _ ih =>
      by_cases redex : ∃ body, g = .lam body
      · obtain ⟨body, rfl⟩ := redex
        simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [step.eq_9 R _ _ g a (fun body same => redex ⟨body, same⟩)]
        cases step R (fun _ => none) g with
        | some _ => simp
        | none =>
            cases h : step R (fun _ => none) a with
            | none => exact absurd h ih
            | some _ => simp
  | @congPairFst _ a a' b _ ih =>
      rw [step.eq_10]
      cases h : step R (fun _ => none) a with
      | none => exact absurd h ih
      | some _ => simp
  | @congPairSnd _ a b b' _ ih =>
      rw [step.eq_10]
      cases step R (fun _ => none) a with
      | some _ => simp
      | none =>
          cases h : step R (fun _ => none) b with
          | none => exact absurd h ih
          | some _ => simp
  | @congFst _ p p' _ ih =>
      by_cases redex : ∃ a b, p = .pair a b
      · obtain ⟨a, b, rfl⟩ := redex
        simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [step.eq_12 R _ _ p (fun a b same => redex ⟨a, b, same⟩)]
        cases h : step R (fun _ => none) p with
        | none => exact absurd h ih
        | some _ => simp
  | @congSnd _ p p' _ ih =>
      by_cases redex : ∃ a b, p = .pair a b
      · obtain ⟨a, b, rfl⟩ := redex
        simp only [step, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [step.eq_14 R _ _ p (fun a b same => redex ⟨a, b, same⟩)]
        cases h : step R (fun _ => none) p with
        | none => exact absurd h ih
        | some _ => simp
  | @congRefl _ a a' _ ih =>
      rw [step.eq_15]
      cases h : step R (fun _ => none) a with
      | none => exact absurd h ih
      | some _ => simp

/-- **Normality is decided by the one-step strategy** for a root-free rule package. -/
theorem normal_iff_step_none (empty : R.computation = RootComputation.empty) {n : Nat} (t : Tm Head n) :
    ContextualDependentExecutableJoin.Normal R t ↔ step R (fun _ => none) t = none := by
  constructor
  · intro normal
    cases computed : step R (fun _ => none) t with
    | none => rfl
    | some next =>
        exact absurd (ContextualDependentReductionBudget.step_directed R _ t next computed) (normal _)
  · intro quiet target reduces
    exact step_complete empty reduces quiet

/-- **Normality is invariant under renaming**, in both directions. -/
theorem normal_rename_iff (empty : R.computation = RootComputation.empty) {n m : Nat} (ρ : Ren n m)
    (t : Tm Head n) :
    ContextualDependentExecutableJoin.Normal R (rename ρ t) ↔ ContextualDependentExecutableJoin.Normal R t := by
  rw [normal_iff_step_none empty, normal_iff_step_none empty]
  exact (step_rename rootFree_renames t ρ).none_iff

/-! ## The certificate -/

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The normality certificate**: the one-step strategy proposes no step. Sound by its type. -/
def certifyNormal (empty : S.R.computation = RootComputation.empty) {n : Nat} (term : Tm Head n) :
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)) :=
  if quiet : step S.R (fun _ => none) term = none then
    some ⟨(normal_iff_step_none empty term).mpr quiet⟩
  else none

/-- **The normality certificate is complete**: it accepts every normal term. -/
theorem certifyNormal_complete (empty : S.R.computation = RootComputation.empty) {n : Nat} {term : Tm Head n}
    (normal : ContextualDependentNormalChecking.Normal (S := S) term) :
    (certifyNormal empty term).isSome := by
  have quiet := (normal_iff_step_none empty term).mp normal
  unfold certifyNormal
  rw [dif_pos quiet]
  rfl

/-- The certificate accepts exactly the normal terms. -/
theorem certifyNormal_isSome_iff (empty : S.R.computation = RootComputation.empty) {n : Nat} (term : Tm Head n) :
    (certifyNormal empty term).isSome ↔ ContextualDependentNormalChecking.Normal (S := S) term := by
  constructor
  · intro accepted
    cases computed : certifyNormal empty term with
    | none => rw [computed] at accepted; cases accepted
    | some certificate => exact certificate.down
  · exact certifyNormal_complete empty

end ContextualDependentNormalizing
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
