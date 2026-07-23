import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Attention
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.RankReachability
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.BeliefInstantiation
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.DerivedCadence
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Consolidation

/-!
# Two-timescale adaptation crown and provenance

This module packages the theorem rungs without broadening their scope.  The
hidden linearity assumption is discharged for concrete linear attention and
the controlled belief register, and explicitly bounded rather than asserted
for softmax.  Cadence is derived from counted updates and exact evidence loss;
the former symmetric quadratic is retained only as a refuted approximation.
Validation on trained transformers remains an empirical target.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

/-! ## Machine-readable provenance -/

inductive TwoTimescaleContributionKind
  | directLift
  | newContent
  | scopeBoundary
  | empiricalTarget
  deriving DecidableEq, Repr

structure TwoTimescaleContribution where
  kind : TwoTimescaleContributionKind
  statement : String
  source : String
  deriving DecidableEq, Repr

def twoTimescaleContributions : List TwoTimescaleContribution :=
  [ ⟨.newContent, "faithfulness iff fast effect is weight-update reachable",
      "TwoTimescaleAdaptation.Model"⟩
  , ⟨.newContent, "transverse state effect has exact unit irreducible loss",
      "TwoTimescaleAdaptation.Model"⟩
  , ⟨.newContent, "ceiling-division capacity deadline and exact loss",
      "TwoTimescaleAdaptation.Cadence"⟩
  , ⟨.scopeBoundary, "interior quadratic cadence is a declared approximation",
      "TwoTimescaleAdaptation.Cadence"⟩
  , ⟨.newContent, "linear-attention additivity derived from outer-product accumulation",
      "TwoTimescaleAdaptation.Attention"⟩
  , ⟨.newContent, "adapter factorization reachability iff matrix rank fits budget",
      "TwoTimescaleAdaptation.RankReachability"⟩
  , ⟨.scopeBoundary, "softmax normalization breaks exact context additivity",
      "TwoTimescaleAdaptation.Attention"⟩
  , ⟨.newContent, "counts-primal and Gaussian belief registers instantiate additive fast state",
      "TwoTimescaleAdaptation.BeliefInstantiation"⟩
  , ⟨.newContent, "counted updates plus exact hinge loss yield a deadline optimum",
      "TwoTimescaleAdaptation.DerivedCadence"⟩
  , ⟨.scopeBoundary, "quadratic interior optimum refuted as the derived cadence",
      "TwoTimescaleAdaptation.DerivedCadence"⟩
  , ⟨.directLift, "one reused contribution gives exact ledger excess",
      "ContinualLearning.EvidenceLedger"⟩
  , ⟨.newContent, "zero-discount reused carry restores calibration",
      "TwoTimescaleAdaptation.Consolidation"⟩
  , ⟨.directLift, "zero interference energy iff curvature commutation",
      "ForgettingGeometry.InterferenceGram"⟩
  , ⟨.newContent, "nonzero-step consolidation commutation iff curvature commutation",
      "TwoTimescaleAdaptation.Consolidation"⟩
  , ⟨.directLift, "matched progress plus H5 controls source forgetting",
      "PredictiveCoding.FrozenAdapterConditionalAdvantage"⟩
  , ⟨.directLift, "unit trust bounds derive the H5 branch condition",
      "UtilizationAtlas.PCPlasticity"⟩
  , ⟨.newContent, "pure-fast sufficiency and overload/unreachability complement",
      "TwoTimescaleAdaptation.Model"⟩
  , ⟨.scopeBoundary, "pressure to consolidate does not imply weight reachability",
      "TwoTimescaleAdaptation.Model"⟩
  , ⟨.scopeBoundary, "quadratic cadence is a declared cost model",
      "TwoTimescaleAdaptation.Cadence"⟩
  , ⟨.empiricalTarget, "trained transformer accuracy and measured cadence loss",
      "future experiment"⟩ ]

def twoTimescaleContributionCount (kind : TwoTimescaleContributionKind) : ℕ :=
  twoTimescaleContributions.countP fun contribution => contribution.kind = kind

theorem twoTimescaleContributionCounts_exact :
    (twoTimescaleContributionCount .directLift,
      twoTimescaleContributionCount .newContent,
      twoTimescaleContributionCount .scopeBoundary,
      twoTimescaleContributionCount .empiricalTarget) = (4, 10, 5, 1) := by
  decide

/-! ## Seven-rung proof-bearing crown -/

structure TwoTimescaleAdaptationCertificate : Prop where
  t1Faithfulness :
    ∀ (slow : Fin 1 → ℝ) (fast : Fin 2 → ℝ),
      (∃ delta : Fin 1 → ℝ,
        FaithfulConsolidation slowAxisFastFullModel slow fast delta) ↔
        slowAxisFastFullModel.fastEffect fast ∈
          LinearMap.range slowAxisFastFullModel.slowEffect
  t1Loss :
    ∀ delta : Fin 1 → ℝ,
      effectSquaredError (firstAxisMap delta) secondAxisEffect =
        (delta 0) ^ 2 + 1
  t2Deadline :
    ∀ capacity arrivalRate time : ℕ, 0 < arrivalRate →
      saturationDeadline capacity arrivalRate ≤ time →
        admittedEvidence capacity arrivalRate time = capacity ∧
          lostEvidence capacity arrivalRate time =
            arrivedEvidence arrivalRate time - capacity
  t3Cadence :
    ∀ arrivalRate capacity updateCost lossCost deadline : ℝ,
      0 < arrivalRate → 0 < updateCost → 0 < deadline →
      capacity = arrivalRate * deadline → updateCost < lossCost * capacity →
        (∀ period : ℝ, 0 < period →
          derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline ≤
            derivedCadenceObjective arrivalRate capacity updateCost lossCost period) ∧
          (∀ period : ℝ, 0 < period → (
            derivedCadenceObjective arrivalRate capacity updateCost lossCost period =
                derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline ↔
              period = deadline))
  t3QuadraticBoundary :
    quadraticCadenceModelStatus = .declaredApproximation ∧
      optimalConsolidationPeriod 2 8 (1 / 4) = 2 ∧
      derivedCadenceObjective 2 8 (1 / 4) 1 4 <
        derivedCadenceObjective 2 8 (1 / 4) 1 2
  t4NoDoubleCount :
    ∀ prior consolidated fresh : GaussianEvidence (Fin 1),
      (ledgerAfterConsolidation prior consolidated fresh 1).precision =
          ((prior.update consolidated).update fresh).precision +
            consolidated.precision ∧
        (ledgerAfterConsolidation prior consolidated fresh 1).naturalParameter =
          ((prior.update consolidated).update fresh).naturalParameter +
            consolidated.naturalParameter
  t4Reset :
    ∀ prior consolidated fresh : GaussianEvidence (Fin 1),
      ledgerAfterConsolidation prior consolidated fresh 0 =
        (prior.update consolidated).update fresh
  t5Order :
    ∀ (step : ℝ) (first second : Matrix (Fin 2) (Fin 2) ℝ), step ≠ 0 →
      (CurvatureConsolidationsCommute step first second ↔
        pairwiseInterferenceEnergy first second = 0)
  t6Retention :
    ∀ sourceCenter targetCenter initial candidateStep referenceStep : ℝ,
      MatchedTargetProgress targetCenter initial
          ((scalarPeriodTask targetCenter).update candidateStep
            (scalarPeriodParameter initial) 0)
          ((scalarPeriodTask targetCenter).update referenceStep
            (scalarPeriodParameter initial) 0) →
        UnitTrustBound candidateStep → UnitTrustBound referenceStep →
          PriorCapabilityNoWorse sourceCenter initial
            ((scalarPeriodTask targetCenter).update candidateStep
              (scalarPeriodParameter initial) 0)
            ((scalarPeriodTask targetCenter).update referenceStep
              (scalarPeriodParameter initial) 0)
  t7Boundary :
    ∀ (capacity load : ℕ) (task : ℕ → (Fin 2 → ℝ))
      (required : Fin 2 → ℝ),
      IsStationaryTask task required →
        (¬ PureFastStateRegime fastAxisSlowFullModel capacity load task required ↔
          ConsolidationPressure fastAxisSlowFullModel capacity load required)
  t7CapabilityBoundary :
    ConsolidationPressure bothAxisLimitedModel 10 5 secondAxisEffect ∧
      ¬ WeightConsolidationCanServe bothAxisLimitedModel secondAxisEffect
  t7Necessity :
    FeasibleWeightConsolidationNecessary
      fastAxisSlowFullModel 10 5 secondAxisEffect

theorem twoTimescaleAdaptation_crown : TwoTimescaleAdaptationCertificate where
  t1Faithfulness := fun slow fast =>
    exists_faithfulConsolidation_iff_mem_range slowAxisFastFullModel slow fast
  t1Loss := slowAxis_consolidationLoss_exact
  t2Deadline := admitted_and_lost_at_or_after_deadline
  t3Cadence := derivedCadenceObjective_unique_minimum_at_deadline
  t3QuadraticBoundary := ⟨quadraticCadenceModel_is_declaredApproximation,
    quadraticCadence_refuted_as_derived_fixture.1,
    quadraticCadence_refuted_as_derived_fixture.2.2.2⟩
  t4NoDoubleCount := naiveConsolidateThenContinue_exact_excess
  t4Reset := discountedReset_restores_calibration
  t5Order := fun step first second hstep =>
    curvatureConsolidations_commute_iff_zero_interference
      (Index := Fin 2) step first second hstep
  t6Retention := quadraticPeriodRetention_of_matchedProgress_unitTrust
  t7Boundary := fun capacity load task required hstationary =>
    stationary_not_pureFastStateRegime_iff_pressure
      fastAxisSlowFullModel capacity load task required hstationary
  t7CapabilityBoundary :=
    consolidationPressure_not_enough_without_weightReachability
  t7Necessity := secondAxis_feasibleConsolidationNecessary_fixture

/-! ## Hidden-assumption discharge crown -/

structure TwoTimescaleAssumptionDischargeCertificate : Prop where
  linearAttentionAdditive :
    ∀ (query : Fin 2 → ℝ)
      (left right : List (LinearAttentionItem (Fin 2) (Fin 2))),
      linearAttentionContextEffect query (left ++ right) =
        linearAttentionContextEffect query left +
          linearAttentionContextEffect query right
  rankReachability :
    ∀ (r : ℕ) (required : Matrix (Fin 2) (Fin 2) ℝ),
      RankBudgetReachable r required ↔ required.rank ≤ r
  rankNegative :
    ∀ slow : Matrix (Fin 1) (Fin 2) ℝ,
      ¬ ∃ delta : Matrix (Fin 1) (Fin 2) ℝ,
        FaithfulConsolidation rankOneSlowFullFastModel slow
          (1 : Matrix (Fin 2) (Fin 2) ℝ) delta
  softmaxCounterexample :
    scalarSoftmaxAttention [(0, 1)] = 1 ∧
      scalarSoftmaxAttention [(0, 3)] = 3 ∧
      scalarSoftmaxAttention ([(0, 1)] ++ [(0, 3)]) = 2 ∧
      scalarSoftmaxAttention ([(0, 1)] ++ [(0, 3)]) ≠
        scalarSoftmaxAttention [(0, 1)] + scalarSoftmaxAttention [(0, 3)]
  softmaxErrorBound :
    ∀ leftMass rightMass leftValue rightValue : ℝ,
      0 < leftMass → 0 < rightMass →
        |normalizedContextMerge leftMass rightMass leftValue rightValue -
            (leftValue + rightValue)| ≤ |leftValue| + |rightValue|
  countsPrimal :
    ∀ left right : List Mettapedia.PLN.Evidence.BinEvNat,
      accumulatedCountRegister (left ++ right) =
        accumulatedCountRegister left + accumulatedCountRegister right
  beliefExact :
    ∀ left right : GaussianEvidence (Fin 1),
      (beliefRegisterLinearEffectModel (Fin 1)).fastEffect
          (gaussianEvidenceCoordinates (left.add right)) =
        gaussianEvidenceCoordinates left + gaussianEvidenceCoordinates right
  countedCadence :
    ∀ (count : ℕ) (arrivalRate capacity updateCost lossCost period : ℝ),
      0 < count → period ≠ 0 →
        countedCadenceAverageCost count arrivalRate capacity updateCost lossCost period =
          derivedCadenceObjective arrivalRate capacity updateCost lossCost period
  quadraticRefuted :
    optimalConsolidationPeriod 2 8 (1 / 4) = 2 ∧
      cadenceObjective 2 8 (1 / 4) 2 -
          derivedCadenceObjective 2 8 (1 / 4) 1 2 = 15 / 8 ∧
      cadenceObjective 2 8 (1 / 4) 4 -
          derivedCadenceObjective 2 8 (1 / 4) 1 4 = 63 / 16 ∧
      derivedCadenceObjective 2 8 (1 / 4) 1 4 <
        derivedCadenceObjective 2 8 (1 / 4) 1 2

theorem twoTimescaleAssumptionDischarge_crown :
    TwoTimescaleAssumptionDischargeCertificate where
  linearAttentionAdditive := linearAttentionContextEffect_append
  rankReachability := rankBudgetReachable_iff_rank_le
  rankNegative := rankOneAdapter_identityContext_no_faithfulConsolidation
  softmaxCounterexample := scalarSoftmaxAttention_not_additive_fixture
  softmaxErrorBound := abs_normalizedContextMerge_sub_add_le
  countsPrimal := accumulatedCountRegister_append
  beliefExact := beliefRegister_fastEffect_add_exact
  countedCadence := countedCadenceAverageCost_eq_derived
  quadraticRefuted := quadraticCadence_refuted_as_derived_fixture

#print axioms twoTimescaleContributionCounts_exact
#print axioms twoTimescaleAdaptation_crown
#print axioms twoTimescaleAssumptionDischarge_crown

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
