import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaStability
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaEthicsTrustTriangleExample
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.WMGrounding
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.BodhisattvaExample
import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample

/-!
# GodelClaw Ethics Examples

Concrete entry points for the ethics meta-stability story.

This file now serves two roles:

- thin wrappers around the proved trust-triangle meta-goal examples, and
- one explicit end-to-end capstone theorem showing the bigger architecture in a
  single place.

The goal is to make the big picture discoverable without forcing readers to hop
across half a dozen files.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
open MeasureTheory

/-- Concrete approximate caring-core example:

a two-step proof-backed rewrite path improves utility while the protected caring
query stays within the cumulative shell bound. -/
abbrev trustTriangle_protectedCaringGoal_path_example :=
  trustTriangle_metaGoal_path_example

/-- Concrete exact caring-core example:

if the rewrite stays outside a closed trust-triangle core, the protected caring
query is preserved exactly while the proof-backed modification improves utility. -/
abbrev trustTriangle_protectedCaringGoal_exact_example :=
  trustTriangle_exact_metaGoal_closure_example

/-- Big-picture exact capstone for one full trust-triangle example.

This packages the stack in one theorem:

1. the top-down theory-guided decision problem recommends safe escalation,
2. the theory marks that option admissible,
3. the rendered active goal lands on the named protected WM query,
4. the non-maleficence and consent constraints each have source satisfaction
   plus public WM grounding,
5. the active goal already has positive WM support,
6. and under proof-backed self-modification that active goal is preserved
   exactly while expected utility improves.

This is the "one example in full" entry point for the current liberated
meta-ethics stack. -/
theorem trustTriangle_full_stack_exact_example
    (wt wc₁ wc₂ : ℝ)
    (hwt : |wt| < 1 / 2) (hwc₁ : |wc₁| < 1 / 2) (hwc₂ : |wc₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    trustTriangleTheoryGuidedDecisionProblem.Recommends .safeEscalation ∧
      trustTriangleTheoryGuidedDecisionProblem.comparisonBudget = 21 ∧
      trustTriangleMetaTheory.conflictDiscipline.admissible
        trustTrianglePracticalProblem.choicePoint safeEscalationFormula ∧
      trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder =
        bodhisattvaEpistemicUniversalLoveQuery ∧
      trustTriangleStructuredESOModel.SatStructured avoidHarmfulDisclosureClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
        bodhisattvaNonMaleficenceQuery ∧
      trustTriangleStructuredESOModel.SatStructured avoidCoerciveOverrideClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
        bodhisattvaConsentQuery ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
        (trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder) ∧
      let oldW : MassState (ConstraintQuery Nat) :=
        {infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁}
      let newW : MassState (ConstraintQuery Nat) :=
        {infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂}
      Mettapedia.UniversalAI.GodelMachine.expectedUtilityFromStart (toyMachine 1) >
          Mettapedia.UniversalAI.GodelMachine.expectedUtilityFromStart (toyMachine 0) ∧
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength oldW
            (trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder) =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength newW
            (trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder) := by
  have hRec := trustTriangleTheoryGuidedDecisionProblem_recommends_safeEscalation
  rcases trustTriangle_metaEthical_capstone with ⟨_, hAdm, hGoalEq⟩
  rcases trustTriangle_nonMaleficence_primaryWMGrounding with ⟨hNoHarmSat, hNoHarmWM⟩
  rcases trustTriangle_consent_primaryWMGrounding with ⟨hConsentSat, hConsentWM⟩
  rcases trustTriangle_metaEthical_correctness_capstone with ⟨_, _, hGoalWM⟩
  rcases trustTriangle_bodhisattva_exact_example wt wc₁ wc₂ hwt hwc₁ hwc₂ μ₁ μ₂ hμ₁ hμ₂ with
    ⟨hUtility, hEUL, _, _, _⟩
  refine ⟨hRec, trustTriangleTheoryGuidedDecisionProblem_comparisonBudget_eq,
    hAdm, hGoalEq, hNoHarmSat, hNoHarmWM, hConsentSat, hConsentWM, hGoalWM, ?_⟩
  refine ⟨hUtility, ?_⟩
  simpa [hGoalEq] using hEUL

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
