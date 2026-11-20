import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Normalizer

/-!
# The directed executable normalizer realized by actual full-step runs

A successful invocation of the existing normalizer supplies its own source
path. A complete root evaluator makes its stopping result directed-normal.
The complete path is realized by the qualified full-step compiler and keeps
the original declared type. No strong-normalization hypothesis is needed
for this theorem about an invocation that returned.

Eventual success for every typed input additionally uses the existing
TypedSN and root-completeness hypotheses. In particular this file does not
claim TypedSN for the vectors package. Directed normality is kept distinct
from ConstructorSystem.Normal of the relation containing head equalities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing
open ExecutableReduction

theorem normalize_returned_stops {Head : Type} (rules : Rules Head) (root : RootEvaluator rules)
    {n : Nat} : ∀ (fuel : Nat) {term : Tm Head n} {result : Result rules term},
      ExecutableReduction.normalize rules root fuel term = some result → step rules root result.val = none
  | 0, _, _, accepted => by cases accepted
  | fuel + 1, term, result, accepted => by
    cases current : step rules root term with
    | none =>
      simp only [ExecutableReduction.normalize, current, Option.some.injEq] at accepted
      subst accepted
      exact current
    | some next =>
      cases later : ExecutableReduction.normalize rules root fuel next.val with
      | none => simp only [ExecutableReduction.normalize, current, later] at accepted; cases accepted
      | some answer =>
        simp only [ExecutableReduction.normalize, current, later, Option.some.injEq] at accepted
        subst accepted
        exact normalize_returned_stops rules root fuel (term := next.val) (result := answer) later

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (qualified : Qualified S) (presentation : SchemaPresentation S.R)

theorem normalizer_result_realized (configuration : Configuration (S := S))
    (root : RootEvaluator S.R) (complete : Eventually.RootComplete S.R root)
    {fuel : Nat} {result : Result S.R configuration.code}
    (returned : ExecutableReduction.normalize S.R root fuel configuration.code = some result) :
    ContextualDependentExecutableJoin.Normal S.R result.val ∧
      ∃ run : (DependentFull.step S.levels Nat).toStep.Run configuration.state,
        ∃ profile : RunProfile qualified presentation configuration run,
          profile.execution.term = result.val ∧
            Typed S.R configuration.state.frame.raw profile.execution.term
              (configuration.state.label configuration.active).1.code := by
  refine ⟨ContextualDependentReductionBudget.normal_of_stopped S.R root complete result.val
    (normalize_returned_stops S.R root fuel returned), ?_⟩
  obtain ⟨run, profile, endpoint⟩ :=
    (full_runs_iff qualified presentation (configuration := configuration)).mp result.property
  exact ⟨run, profile, endpoint, full_run_typed qualified presentation profile⟩

theorem normalizer_eventually_realized (configuration : Configuration (S := S))
    (root : RootEvaluator S.R) (complete : Eventually.RootComplete S.R root)
    (sn : Eventually.TypedSN S.R) :
    ∃ fuel result, ContextualDependentExecutableJoin.Normal S.R result.val ∧
      (∀ larger, fuel ≤ larger → ExecutableReduction.normalize S.R root larger configuration.code = some result) ∧
      ∃ run : (DependentFull.step S.levels Nat).toStep.Run configuration.state,
        ∃ profile : RunProfile qualified presentation configuration run,
          profile.execution.term = result.val ∧
            Typed S.R configuration.state.frame.raw profile.execution.term
              (configuration.state.label configuration.active).1.code := by
  obtain ⟨fuel, result, normal, _, stable⟩ :=
    Eventually.typed_normalize_eventually S.R root sn complete configuration.state.frame.formed
      (configuration.state.label configuration.active).2.typed
  exact ⟨fuel, result, normal, stable,
    (normalizer_result_realized qualified presentation configuration root complete (stable fuel le_rfl)).2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.normalizer_result_realized
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.normalizer_eventually_realized
