import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNAlgorithmicAbductionBridge

/-!
# Induction / Abduction Rule-Family Profile

This file exposes a compact proof-carrying handle for the current
Induction/Abduction jewel.  It does not add a new rule semantics: induction and
abduction continue to route through Bayes inversion plus the existing deduction
credal interval, and algorithmic-prior explanation ranking continues to require
separated prior-weighted intervals.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.KR.ConceptGeometry.IntensionalInheritance

/-- Reader-facing theorem profile for the Induction/Abduction rule family.

The positive fields show the intended point and interval behavior; the negative
fields keep point-only and catalog-shortcut reasoning from being laundered into
robust inference. -/
structure InductionAbductionRuleFamilyProfile where
  inductionCatalogScopeCanary :
    bayesInversion (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (1 / 2 : ℝ) ∧
      bayesInversion (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ≠
        (1 / 2 : ℝ) ∧
      bayesInversion (0 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (0 : ℝ)
  abductionCatalogScopeCanary :
    bayesInversion (1 / 2 : ℝ) (3 / 4 : ℝ) (3 / 4 : ℝ) =
        (1 / 2 : ℝ) ∧
      bayesInversion (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≠
        (1 / 2 : ℝ) ∧
      bayesInversion (0 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) =
        (0 : ℝ)
  asymmetricITVCanary :
    inductionAsymmetryITV.lower = (0 : ℝ) ∧
      inductionAsymmetryITV.upper = (1 : ℝ) ∧
      inductionAsymmetryITV.width = (1 : ℝ) ∧
      abductionAsymmetryITV.lower = (1 / 2 : ℝ) ∧
      abductionAsymmetryITV.upper = (1 : ℝ) ∧
      abductionAsymmetryITV.width = (1 / 2 : ℝ) ∧
      inductionAsymmetryITV.lower < abductionAsymmetryITV.lower
  pointValuesInsideAsymmetryITVs :
    inductionAsymmetryITV.lower ≤
        plnInductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ∧
      plnInductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≤
        inductionAsymmetryITV.upper ∧
      abductionAsymmetryITV.lower ≤
        plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≤
        abductionAsymmetryITV.upper
  intervalOverlapSymm :
    ∀ {x y : ITV},
      abductionIntervalsOverlap x y → abductionIntervalsOverlap y x
  intervalRankExcludesOverlap :
    ∀ {better worse : ITV},
      abductionIntervalStrictlyRanks better worse →
        ¬ abductionIntervalsOverlap better worse
  unresolvedIntervalsOverlap :
    ∀ {x y : ITV},
      ¬ abductionIntervalStrictlyRanks x y →
        ¬ abductionIntervalStrictlyRanks y x →
          abductionIntervalsOverlap x y
  intervalRankPointSound :
    ∀ {better worse : ITV} {betterPoint worsePoint : ℝ},
      abductionIntervalStrictlyRanks better worse →
        better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper →
          worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper →
            worsePoint < betterPoint
  abductionSearchSeparatedCanary :
    abductionSearchWeakITV.lower = (0 : ℝ) ∧
      abductionSearchWeakITV.upper = (1 / 2 : ℝ) ∧
      abductionSearchStrongITV.lower = (2 / 3 : ℝ) ∧
      abductionSearchStrongITV.upper = (1 : ℝ) ∧
      abductionIntervalStrictlyRanks
        abductionSearchStrongITV abductionSearchWeakITV ∧
      plnAbductionStrength
        (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ) =
        (1 / 4 : ℝ) ∧
      plnAbductionStrength
        (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (5 / 6 : ℝ)
  pointDifferenceNotIntervalRankCanary :
    plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (1 / 2 : ℝ) ∧
      plnAbductionStrength
        (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      abductionSearchOpenITV.lower = (0 : ℝ) ∧
      abductionSearchOpenITV.upper = (1 : ℝ) ∧
      abductionSearchBetterPointITV.lower = (1 / 2 : ℝ) ∧
      abductionSearchBetterPointITV.upper = (1 : ℝ) ∧
      abductionIntervalsOverlap
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ abductionIntervalStrictlyRanks
          abductionSearchBetterPointITV abductionSearchOpenITV ∧
      ¬ abductionIntervalStrictlyRanks
          abductionSearchOpenITV abductionSearchBetterPointITV
  priorWeightedOverlapSymm :
    ∀ {xPrior yPrior : ℝ} {x y : ITV},
      priorWeightedIntervalsOverlap xPrior yPrior x y →
        priorWeightedIntervalsOverlap yPrior xPrior y x
  priorWeightedRankExcludesOverlap :
    ∀ {betterPrior worsePrior : ℝ} {better worse : ITV},
      priorWeightedIntervalStrictlyRanks
          betterPrior worsePrior better worse →
        ¬ priorWeightedIntervalsOverlap betterPrior worsePrior better worse
  priorWeightedUnresolvedOverlap :
    ∀ {xPrior yPrior : ℝ} {x y : ITV},
      ¬ priorWeightedIntervalStrictlyRanks xPrior yPrior x y →
        ¬ priorWeightedIntervalStrictlyRanks yPrior xPrior y x →
          priorWeightedIntervalsOverlap xPrior yPrior x y
  priorWeightedRankPointSound :
    ∀ {betterPrior worsePrior : ℝ} {better worse : ITV}
      {betterPoint worsePoint : ℝ},
      0 ≤ betterPrior →
        0 ≤ worsePrior →
          priorWeightedIntervalStrictlyRanks
              betterPrior worsePrior better worse →
            better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper →
              worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper →
                priorWeightedPoint worsePrior worsePoint <
                  priorWeightedPoint betterPrior betterPoint
  priorWeightedIntervalWellOrdered :
    ∀ {prior : ℝ} {itv : ITV},
      0 ≤ prior →
        priorWeightedLower prior itv ≤ priorWeightedUpper prior itv
  priorWeightedPointMemInterval :
    ∀ {prior point : ℝ} {itv : ITV},
      0 ≤ prior →
        itv.lower ≤ point ∧ point ≤ itv.upper →
          priorWeightedLower prior itv ≤ priorWeightedPoint prior point ∧
            priorWeightedPoint prior point ≤ priorWeightedUpper prior itv
  priorWeightedEndpointsBounded :
    ∀ {prior : ℝ} {itv : ITV},
      prior ∈ Set.Icc (0 : ℝ) 1 →
        priorWeightedLower prior itv ∈ Set.Icc (0 : ℝ) 1 ∧
          priorWeightedUpper prior itv ∈ Set.Icc (0 : ℝ) 1
  priorWeightedPointBounded :
    ∀ {prior point : ℝ},
      prior ∈ Set.Icc (0 : ℝ) 1 →
        point ∈ Set.Icc (0 : ℝ) 1 →
          priorWeightedPoint prior point ∈ Set.Icc (0 : ℝ) 1
  universalMixturePriorBounded :
    ∀ (ξ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
      (ctx hypothesis :
        Mettapedia.UniversalAI.UniversalPrediction.BinString),
      priorFromConditional ξ ctx hypothesis ∈ Set.Icc (0 : ℝ) 1
  universalMixtureIntervalWellOrdered :
    ∀ (ξ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
      (ctx hypothesis :
        Mettapedia.UniversalAI.UniversalPrediction.BinString)
      (itv : ITV),
      universalMixtureAbductionLower ξ ctx hypothesis itv ≤
        universalMixtureAbductionUpper ξ ctx hypothesis itv
  universalMixturePointMemInterval :
    ∀ (ξ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
      (ctx hypothesis :
        Mettapedia.UniversalAI.UniversalPrediction.BinString)
      (itv : ITV) {point : ℝ},
      itv.lower ≤ point ∧ point ≤ itv.upper →
        universalMixtureAbductionLower ξ ctx hypothesis itv ≤
            priorWeightedPoint (priorFromConditional ξ ctx hypothesis) point ∧
          priorWeightedPoint (priorFromConditional ξ ctx hypothesis) point ≤
            universalMixtureAbductionUpper ξ ctx hypothesis itv
  universalMixtureEndpointsBounded :
    ∀ (ξ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
      (ctx hypothesis :
        Mettapedia.UniversalAI.UniversalPrediction.BinString)
      (itv : ITV),
      universalMixtureAbductionLower ξ ctx hypothesis itv ∈ Set.Icc (0 : ℝ) 1 ∧
        universalMixtureAbductionUpper ξ ctx hypothesis itv ∈ Set.Icc (0 : ℝ) 1
  universalMixturePointBounded :
    ∀ (ξ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
      (ctx hypothesis :
        Mettapedia.UniversalAI.UniversalPrediction.BinString)
      {point : ℝ},
      point ∈ Set.Icc (0 : ℝ) 1 →
        priorWeightedPoint (priorFromConditional ξ ctx hypothesis) point ∈
          Set.Icc (0 : ℝ) 1
  xiKpfMachinePriorComparability :
    ∀ (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
      (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
        Mettapedia.UniversalAI.UniversalPrediction.Semimeasure),
      ∃ c d : ℕ,
        ∀ ctx hyp : Mettapedia.UniversalAI.UniversalPrediction.BinString,
          xiKpfMachineFactor c d *
              priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := V) ν)
                ctx hyp ≤
            priorFromConditional
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := U) ν)
              ctx hyp
  xiKpfMachineMarginIntervalRank :
    ∀ (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
      (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
        Mettapedia.UniversalAI.UniversalPrediction.Semimeasure),
      ∃ cUV dUV cVU dVU : ℕ,
        ∀ (ctx betterHypothesis worseHypothesis :
            Mettapedia.UniversalAI.UniversalPrediction.BinString)
          (better worse : ITV),
          0 ≤ worse.upper → 0 ≤ better.lower →
          ((priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := V) ν)
                ctx worseHypothesis /
                xiKpfMachineFactor cVU dVU) * worse.upper <
              (xiKpfMachineFactor cUV dUV *
                priorFromConditional
                  (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                    (U := V) ν)
                  ctx betterHypothesis) * better.lower) →
          universalMixtureAbductionUpper
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := U) ν)
              ctx worseHypothesis worse <
            universalMixtureAbductionLower
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := U) ν)
              ctx betterHypothesis better
  xiKpfMachineMarginPointRank :
    ∀ (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
      [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
      (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
        Mettapedia.UniversalAI.UniversalPrediction.Semimeasure),
      ∃ cUV dUV cVU dVU : ℕ,
        ∀ (ctx betterHypothesis worseHypothesis :
            Mettapedia.UniversalAI.UniversalPrediction.BinString)
          (better worse : ITV) {betterPoint worsePoint : ℝ},
          0 ≤ worse.upper → 0 ≤ better.lower →
          ((priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := V) ν)
                ctx worseHypothesis /
                xiKpfMachineFactor cVU dVU) * worse.upper <
              (xiKpfMachineFactor cUV dUV *
                priorFromConditional
                  (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                    (U := V) ν)
                  ctx betterHypothesis) * better.lower) →
          better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper →
          worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper →
          priorWeightedPoint
              (priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := U) ν)
                ctx worseHypothesis)
              worsePoint <
            priorWeightedPoint
              (priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := U) ν)
                ctx betterHypothesis)
              betterPoint
  algorithmicPriorSeparatedCanary :
    descriptionLengthPrior 1 = (1 / 2 : ℝ) ∧
      descriptionLengthPrior 4 = (1 / 16 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (5 / 6 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) <
        plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 8 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (5 / 96 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) ∧
      priorWeightedLower (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 4 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 2 : ℝ) ∧
      priorWeightedLower (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 24 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 16 : ℝ) ∧
      priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 4)
        abductionSearchBetterPointITV abductionSearchStrongITV
  algorithmicPriorPointFlipNotIntervalRankCanary :
    plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
      (1 / 2 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) <
        plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) =
        (1 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 16 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
      priorWeightedIntervalsOverlap
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 2) (descriptionLengthPrior 1)
        abductionSearchBetterPointITV abductionSearchOpenITV

/-- Compact public handle for the Induction/Abduction rule-family surface. -/
noncomputable def inductionAbductionRuleFamilyProfile :
    InductionAbductionRuleFamilyProfile where
  inductionCatalogScopeCanary :=
    plnInductionBayesPremise_catalog_scope_canary
  abductionCatalogScopeCanary :=
    plnAbductionBayesPremise_catalog_scope_canary
  asymmetricITVCanary :=
    plnInductionAbductionITV_asymmetric_canary
  pointValuesInsideAsymmetryITVs :=
    plnInductionAbduction_point_values_mem_asymmetry_ITVs
  intervalOverlapSymm := by
    intro x y
    exact abductionIntervalsOverlap_symm
  intervalRankExcludesOverlap := by
    intro better worse
    exact not_abductionIntervalsOverlap_of_strictlyRanks
  unresolvedIntervalsOverlap := by
    intro x y
    exact abductionIntervalsOverlap_of_not_strictlyRanks
  intervalRankPointSound := by
    intro better worse betterPoint worsePoint
    exact abductionIntervalStrictlyRanks_point_lt
  abductionSearchSeparatedCanary :=
    plnAbductionSearch_strict_interval_ranking_canary
  pointDifferenceNotIntervalRankCanary :=
    plnAbductionSearch_point_difference_not_interval_ranking_canary
  priorWeightedOverlapSymm := by
    intro xPrior yPrior x y
    exact priorWeightedIntervalsOverlap_symm
  priorWeightedRankExcludesOverlap := by
    intro betterPrior worsePrior better worse
    exact not_priorWeightedIntervalsOverlap_of_strictlyRanks
  priorWeightedUnresolvedOverlap := by
    intro xPrior yPrior x y
    exact priorWeightedIntervalsOverlap_of_not_strictlyRanks
  priorWeightedRankPointSound := by
    intro betterPrior worsePrior better worse betterPoint worsePoint
    exact priorWeightedIntervalStrictlyRanks_point_lt
  priorWeightedIntervalWellOrdered := by
    intro prior itv
    exact priorWeightedLower_le_upper_of_nonneg
  priorWeightedPointMemInterval := by
    intro prior point itv
    exact priorWeightedPoint_mem_interval_of_mem
  priorWeightedEndpointsBounded := by
    intro prior itv
    exact priorWeightedEndpoints_mem_unit_of_prior_mem_unit
  priorWeightedPointBounded := by
    intro prior point
    exact priorWeightedPoint_mem_unit_of_mem_unit
  universalMixturePriorBounded :=
    priorFromConditional_mem_unit
  universalMixtureIntervalWellOrdered :=
    universalMixtureAbduction_lower_le_upper
  universalMixturePointMemInterval :=
    universalMixtureAbduction_point_mem_interval
  universalMixtureEndpointsBounded :=
    universalMixtureAbduction_endpoints_mem_unit
  universalMixturePointBounded := by
    intro ξ ctx hypothesis point
    exact universalMixtureAbduction_point_mem_unit ξ ctx hypothesis
  xiKpfMachinePriorComparability :=
    xiKpfPriorFromConditional_mul_le_of_invariance
  xiKpfMachineMarginIntervalRank :=
    xiKpfAbduction_interval_rank_of_machine_margin
  xiKpfMachineMarginPointRank :=
    xiKpfAbduction_point_rank_of_machine_margin
  algorithmicPriorSeparatedCanary :=
    algorithmicPriorAbduction_strict_interval_rank_canary
  algorithmicPriorPointFlipNotIntervalRankCanary :=
    algorithmicPriorAbduction_point_flip_not_interval_rank_canary

end Mettapedia.PLN.RuleFamilies.FirstOrder
