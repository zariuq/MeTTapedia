import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# Sufficient budgets for the actual dependent normalizer

The executable strategy performs directed reductions, not arbitrary head
equalities. Strong normalization therefore supplies a finite successful
budget. Once successful, larger budgets preserve the returned term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentReductionBudget

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ExecutableReduction

variable {Head : Type} (rules : Rules Head) (root : RootEvaluator rules)

theorem step_directed {n : Nat} (term : Tm Head n) :
    ∀ result : StepResult rules term, step rules root term = some result →
      StrongNormalization.Reduces rules term result.val := by
  fun_induction step rules root term <;> intro result computed <;>
    simp_all
  all_goals subst result
  case case1 =>
    rename_i n term next rootStep
    exact .root next.property
  all_goals
    solve_by_elim [StepCore.betaPi, StepCore.betaSigmaFst, StepCore.betaSigmaSnd,
      StepCore.congPiDom, StepCore.congPiCod, StepCore.congSigmaDom, StepCore.congSigmaCod,
      StepCore.congIdTy, StepCore.congIdLeft, StepCore.congIdRight, StepCore.congLam,
      StepCore.congAppFun, StepCore.congAppArg, StepCore.congPairFst, StepCore.congPairSnd,
      StepCore.congFst, StepCore.congSnd, StepCore.congRefl]

theorem success_succ {n fuel : Nat} {term : Tm Head n} {result : Result rules term}
    (accepted : normalize rules root fuel term = some result) :
    normalize rules root (fuel + 1) term = some result := by
  induction fuel generalizing term with
  | zero => cases accepted
  | succ fuel ih =>
    cases current : step rules root term with
    | none => simpa only [normalize, current] using accepted
    | some next =>
      cases later : normalize rules root fuel next.val with
      | none =>
        simp only [normalize, current, later] at accepted
        cases accepted
      | some answer =>
        have enlarged := ih later
        simp only [normalize, current, later] at accepted
        rw [normalize, current]
        dsimp only
        rw [enlarged]
        exact accepted

theorem success_mono {n fuel larger : Nat} {term : Tm Head n} {result : Result rules term}
    (accepted : normalize rules root fuel term = some result) (enough : fuel ≤ larger) :
    normalize rules root larger term = some result := by
  induction enough with
  | refl => exact accepted
  | step _ ih => exact success_succ rules root ih

theorem stopped_of_success {n fuel : Nat} {term : Tm Head n} {result : Result rules term}
    (accepted : normalize rules root fuel term = some result) : step rules root result.val = none := by
  induction fuel generalizing term with
  | zero => cases accepted
  | succ fuel ih =>
    cases current : step rules root term with
    | none =>
      simp only [normalize, current, Option.some.injEq] at accepted
      subst result
      exact current
    | some next =>
      cases later : normalize rules root fuel next.val with
      | none =>
        simp only [normalize, current, later] at accepted
        cases accepted
      | some answer =>
        have stopped := ih later
        simp only [normalize, current, later, Option.some.injEq] at accepted
        subst result
        exact stopped

theorem exists_budget_of_sn {n : Nat} {term : Tm Head n}
    (normalizing : StrongNormalization.SN rules term) :
    ∃ fuel result, normalize rules root fuel term = some result ∧ step rules root result.val = none := by
  induction normalizing with
  | intro term _ ih =>
    cases current : step rules root term with
    | none => exact ⟨1, ⟨term, .refl⟩, by simp only [normalize, current], current⟩
    | some next =>
      obtain ⟨fuel, answer, accepted, stopped⟩ := ih next.val (step_directed rules root term next current)
      refine ⟨fuel + 1, ⟨answer.val, .head next.property answer.property⟩, ?_, stopped⟩
      simp only [normalize, current, accepted]

/-- The witness budget concerns this actual executable strategy. Every
larger budget returns the same term and reconstructed reduction certificate. -/
theorem eventually_stable_of_sn {n : Nat} {term : Tm Head n}
    (normalizing : StrongNormalization.SN rules term) :
    ∃ fuel result, step rules root result.val = none ∧
      ∀ larger, fuel ≤ larger → normalize rules root larger term = some result := by
  obtain ⟨fuel, result, accepted, stopped⟩ := exists_budget_of_sn rules root normalizing
  exact ⟨fuel, result, stopped, fun _ enough => success_mono rules root accepted enough⟩

/-- Stopping is semantic normality only when the root evaluator covers all
declared root steps. The core tower discharges this condition outright. -/
theorem normal_of_stopped
    (complete : ∀ {n : Nat} (term : Tm Head n), root term = none →
      ∀ target, ¬ rules.computation.step term target)
    {n : Nat} (term : Tm Head n) : step rules root term = none →
      ∀ target, ¬ StrongNormalization.Reduces rules term target := by
  fun_induction step rules root term <;> intro stopped target reduced <;> simp_all
  all_goals cases reduced <;> simp_all [StrongNormalization.noHeadSteps]

end ContextualDependentReductionBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
