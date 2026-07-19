import Mathlib.Tactic
import Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition
import Mettapedia.Examples.PLN.MapleCourtOverlapDemo

/-!
# Dependence-aware chain-composition examples

Positive and negative fixtures for the W1 two-hop composition surface.
-/

namespace Mettapedia.Examples.PLN.DependenceAwareChainComposition

open scoped BigOperators ENNReal NNReal
open Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
open Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet

noncomputable section

def halfSourceProfile : SourceProfile where
  prob := fun _ => (1 / 2 : ℝ≥0)
  prob_le_one := by intro _; norm_num

def halfLink (support : Finset ℕ) : ChainLinkCert :=
  ChainLinkCert.point support (1 / 2 : ℝ) (9 / 10 : ℝ)
    (by norm_num) (by norm_num)

def quarterLink (support : Finset ℕ) : ChainLinkCert :=
  ChainLinkCert.point support (1 / 4 : ℝ) (9 / 10 : ℝ)
    (by norm_num) (by norm_num)

/-! ## Positive case: disjoint source supports -/

def disjointLeft : ChainLinkCert := halfLink ({0} : Finset ℕ)

def disjointRight : ChainLinkCert := halfLink ({1} : Finset ℕ)

def disjointTwoHop : TwoHopChainDatum where
  left := disjointLeft
  right := disjointRight
  productExactness := TwoHopProductExactness.of_linkStrengths disjointLeft disjointRight
  sourceProfile := halfSourceProfile
  sourceCoupling := TwoHopSourceCoupling.fromSourceUnion

theorem disjoint_sources_union_three_quarters :
    sourceUnionStrength halfSourceProfile ({0} : Finset ℕ) ({1} : Finset ℕ) =
      (3 / 4 : ℝ) := by
  rw [sourceUnionStrength_eq_noisyOr_of_disjoint
    (profile := halfSourceProfile) (S := ({0} : Finset ℕ))
    (T := ({1} : Finset ℕ)) (by decide)]
  rw [sourceStrength, sourceStrength]
  rw [sourceEvent_measureReal, sourceEvent_measureReal]
  norm_num [halfSourceProfile, noisyOrFrequency]

theorem disjoint_twoHop_estimate_mem_credalEnvelope :
    (chainCredalEnvelope disjointTwoHop).lower ≤
        twoHopComposedEstimate disjointTwoHop ∧
      twoHopComposedEstimate disjointTwoHop ≤
        (chainCredalEnvelope disjointTwoHop).upper :=
  twoHopChainComposition_mem_credalEnvelope disjointTwoHop

theorem disjoint_chain_envelope_not_vacuous :
    (chainCredalEnvelope disjointTwoHop).lower ≠ 0 := by
  apply chainCredalEnvelope_lower_ne_zero_of_product_pos
  change 0 < (1 / 2 : ℝ) * (1 / 2 : ℝ)
  norm_num

/-! ## Negative case: overlapping source supports -/

def overlapLeft : ChainLinkCert := quarterLink ({0, 2} : Finset ℕ)

def overlapRight : ChainLinkCert := quarterLink ({1, 2} : Finset ℕ)

def overlapTwoHop : TwoHopChainDatum where
  left := overlapLeft
  right := overlapRight
  productExactness := TwoHopProductExactness.of_linkStrengths overlapLeft overlapRight
  sourceProfile := halfSourceProfile
  sourceCoupling := TwoHopSourceCoupling.fromSourceUnion

theorem overlap_sources_union_three_eighths :
    sourceUnionStrength halfSourceProfile
        ({0, 2} : Finset ℕ) ({1, 2} : Finset ℕ) =
      (3 / 8 : ℝ) := by
  rw [sourceUnionStrength_eq_add_sub_overlap]
  rw [sourceStrength, sourceStrength]
  rw [sourceEvent_measureReal, sourceEvent_measureReal]
  norm_num [halfSourceProfile]

theorem overlap_sources_not_independent_noisyOr :
    sourceUnionStrength halfSourceProfile
        ({0, 2} : Finset ℕ) ({1, 2} : Finset ℕ) ≠
      noisyOrFrequency (fun _ : Fin 2 => (1 / 4 : ℝ)) := by
  rw [overlap_sources_union_three_eighths]
  norm_num [noisyOrFrequency]

theorem overlap_twoHop_estimate_mem_credalEnvelope :
    (chainCredalEnvelope overlapTwoHop).lower ≤
        twoHopComposedEstimate overlapTwoHop ∧
      twoHopComposedEstimate overlapTwoHop ≤
        (chainCredalEnvelope overlapTwoHop).upper :=
  twoHopChainComposition_mem_credalEnvelope overlapTwoHop

theorem mapleCourt_overlap_canary_available :
    Mettapedia.Examples.PLN.MapleCourtOverlapDemo.naiveTotal ≠
      Mettapedia.Examples.PLN.MapleCourtOverlapDemo.correctedTotal :=
  Mettapedia.Examples.PLN.MapleCourtOverlapDemo.naive_overcounts

/-! ## W3 positive case: three-hop disjoint source supports -/

def threeHopDisjointSupports : Fin 3 → Finset ℕ
  | 0 => ({0} : Finset ℕ)
  | 1 => ({1} : Finset ℕ)
  | 2 => ({2} : Finset ℕ)

def threeHopDisjointLinks : Fin 3 → ChainLinkCert :=
  fun i => halfLink (threeHopDisjointSupports i)

theorem threeHopDisjointLinks_sourceSupports :
    (fun i : Fin 3 => (threeHopDisjointLinks i).sourceSupport) =
      threeHopDisjointSupports := by
  funext i
  simp [threeHopDisjointLinks, halfLink, ChainLinkCert.point]

theorem threeHopDisjointSupports_pairwiseDisjoint :
    Pairwise (fun i j => Disjoint (threeHopDisjointSupports i) (threeHopDisjointSupports j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide

def threeHopDisjointChain : PathChainDatum 2 where
  links := threeHopDisjointLinks
  productExactness := PathProductExactness.of_links threeHopDisjointLinks
  sourceProfile := halfSourceProfile
  sourceCoupling := PathSourceCoupling.fromSourceUnion

theorem threeHop_disjoint_product_one_eighth :
    threeHopDisjointChain.productExactness.productStrength = (1 / 8 : ℝ) := by
  change pathProductStrength threeHopDisjointLinks = (1 / 8 : ℝ)
  norm_num [pathProductStrength, threeHopDisjointLinks, halfLink, ChainLinkCert.point]

theorem threeHop_disjoint_sources_union_seven_eighths :
    sourceSupportsUnionStrength halfSourceProfile threeHopDisjointSupports =
      (7 / 8 : ℝ) := by
  rw [sourceSupportsUnionStrength_eq_noisyOr_of_pairwiseDisjoint
    (profile := halfSourceProfile) (supports := threeHopDisjointSupports)
    threeHopDisjointSupports_pairwiseDisjoint]
  have hfreq :
      (fun i : Fin 3 => sourceStrength halfSourceProfile (threeHopDisjointSupports i)) =
        (fun _ : Fin 3 => (1 / 2 : ℝ)) := by
    funext i
    fin_cases i <;>
      norm_num [sourceStrength, sourceEvent_measureReal, halfSourceProfile,
        threeHopDisjointSupports]
  rw [hfreq]
  norm_num [noisyOrFrequency]

theorem threeHop_chainComposition_mem_credalEnvelope :
    (pathCredalEnvelope threeHopDisjointChain).lower ≤
        chainCompositionEstimate threeHopDisjointChain ∧
      chainCompositionEstimate threeHopDisjointChain ≤
        (pathCredalEnvelope threeHopDisjointChain).upper :=
  chainComposition_mem_credalEnvelope threeHopDisjointChain

/-! ## W3 negative case: shared source support must be tracked -/

def sharedThreeHopSupports (_ : Fin 3) : Finset ℕ := {0}

def sharedThreeHopLinks : Fin 3 → ChainLinkCert :=
  fun i => halfLink (sharedThreeHopSupports i)

theorem sharedThreeHopLinks_sourceSupports :
    (fun i : Fin 3 => (sharedThreeHopLinks i).sourceSupport) =
      sharedThreeHopSupports := by
  funext i
  simp [sharedThreeHopLinks, halfLink, ChainLinkCert.point]

theorem sharedThreeHopSupports_allEqual :
    ∀ i j, sharedThreeHopSupports i = sharedThreeHopSupports j := by
  intro _ _
  rfl

def sharedThreeHopChain : PathChainDatum 2 where
  links := sharedThreeHopLinks
  productExactness := PathProductExactness.of_links sharedThreeHopLinks
  sourceProfile := halfSourceProfile
  sourceCoupling := PathSourceCoupling.fromSourceUnion

theorem shared_threeHop_sources_union_half :
    sourceSupportsUnionStrength halfSourceProfile sharedThreeHopSupports =
      (1 / 2 : ℝ) := by
  rw [sourceSupportsUnionStrength_eq_max_of_allEqual
    (profile := halfSourceProfile) (supports := sharedThreeHopSupports)
    sharedThreeHopSupports_allEqual]
  norm_num [maxFrequency, sourceStrength, sourceEvent_measureReal,
    halfSourceProfile, sharedThreeHopSupports]

theorem shared_threeHop_naive_independent_noisyOr_seven_eighths :
    noisyOrFrequency (fun _ : Fin 3 => (1 / 2 : ℝ)) = (7 / 8 : ℝ) := by
  norm_num [noisyOrFrequency]

theorem shared_threeHop_tracked_envelope_upper_five_eighths :
    (pathCredalEnvelope sharedThreeHopChain).upper = (5 / 8 : ℝ) := by
  have hprod : pathProductStrength sharedThreeHopLinks = (1 / 8 : ℝ) := by
    norm_num [pathProductStrength, sharedThreeHopLinks, halfLink, ChainLinkCert.point]
  have hfreq :
      pathChainFrequencies sharedThreeHopChain =
        (fun i : Fin 2 => if i = 0 then (1 / 8 : ℝ) else (1 / 2 : ℝ)) := by
    funext i
    fin_cases i
    · simp [pathChainFrequencies, sharedThreeHopChain,
        PathProductExactness.of_links, hprod]
    · simp [pathChainFrequencies, sharedThreeHopChain,
        PathSourceCoupling.correctedStrength]
      rw [sharedThreeHopLinks_sourceSupports]
      simpa using shared_threeHop_sources_union_half
  rw [pathCredalEnvelope, frechetUnionITV_upper, frechetUnionUpper]
  change min 1 (sumFrequency (pathChainFrequencies sharedThreeHopChain)) =
    (5 / 8 : ℝ)
  rw [hfreq]
  norm_num [sumFrequency]

theorem shared_threeHop_independent_noisyOr_violates_tracked_envelope :
    (pathCredalEnvelope sharedThreeHopChain).upper <
      noisyOrFrequency (fun _ : Fin 3 => (1 / 2 : ℝ)) := by
  rw [shared_threeHop_tracked_envelope_upper_five_eighths,
    shared_threeHop_naive_independent_noisyOr_seven_eighths]
  norm_num

theorem shared_threeHop_untracked_estimate_not_mem_credalEnvelope :
    ¬ ((pathCredalEnvelope sharedThreeHopChain).lower ≤
          noisyOrFrequency (fun _ : Fin 3 => (1 / 2 : ℝ)) ∧
        noisyOrFrequency (fun _ : Fin 3 => (1 / 2 : ℝ)) ≤
          (pathCredalEnvelope sharedThreeHopChain).upper) := by
  intro hmem
  exact not_lt_of_ge hmem.2
    shared_threeHop_independent_noisyOr_violates_tracked_envelope

/-! ## W4 horizon examples -/

def halfHorizonPolicy : HorizonPolicy where
  threshold := (1 / 2 : ℝ)
  threshold_mem_unit := by norm_num

theorem threeHop_disjoint_confidence_product_729_1000 :
    pathChainConfidence threeHopDisjointChain = (729 / 1000 : ℝ) := by
  change pathConfidenceProduct threeHopDisjointLinks = (729 / 1000 : ℝ)
  norm_num [pathConfidenceProduct, threeHopDisjointLinks, halfLink,
    ChainLinkCert.point]

theorem threeHop_disjoint_tracked_envelope_width_one_eighth :
    chainEnvelopeWidth (pathCredalEnvelope threeHopDisjointChain) =
      (1 / 8 : ℝ) := by
  have hprod : pathProductStrength threeHopDisjointLinks = (1 / 8 : ℝ) := by
    simpa [threeHopDisjointChain, PathProductExactness.of_links]
      using threeHop_disjoint_product_one_eighth
  have hfreq :
      pathChainFrequencies threeHopDisjointChain =
        (fun i : Fin 2 => if i = 0 then (1 / 8 : ℝ) else (7 / 8 : ℝ)) := by
    funext i
    fin_cases i
    · simp [pathChainFrequencies, threeHopDisjointChain,
        PathProductExactness.of_links, hprod]
    · simp [pathChainFrequencies, threeHopDisjointChain,
        PathSourceCoupling.correctedStrength]
      rw [threeHopDisjointLinks_sourceSupports]
      simpa using threeHop_disjoint_sources_union_seven_eighths
  rw [chainEnvelopeWidth, pathCredalEnvelope, frechetUnionITV_lower,
    frechetUnionITV_upper, frechetUnionUpper]
  change min 1 (sumFrequency (pathChainFrequencies threeHopDisjointChain)) -
      maxFrequency 1 (pathChainFrequencies threeHopDisjointChain) =
    (1 / 8 : ℝ)
  rw [hfreq]
  have hsum :
      sumFrequency
          (fun i : Fin 2 => if i = 0 then (1 / 8 : ℝ) else (7 / 8 : ℝ)) =
        (1 : ℝ) := by
    unfold sumFrequency
    norm_num
  have hmax :
      maxFrequency 1
          (fun i : Fin 2 => if i = 0 then (1 / 8 : ℝ) else (7 / 8 : ℝ)) =
        (7 / 8 : ℝ) := by
    apply le_antisymm
    · unfold maxFrequency
      apply Finset.sup'_le
      intro i _hi
      fin_cases i <;> norm_num
    · have h := frequency_le_maxFrequency
        (fun i : Fin 2 => if i = 0 then (1 / 8 : ℝ) else (7 / 8 : ℝ))
        (1 : Fin 2)
      norm_num at h
      exact h
  rw [hsum, hmax]
  norm_num

theorem threeHop_disjoint_chainInformative :
    chainInformative halfHorizonPolicy threeHopDisjointChain := by
  rw [chainInformative_iff]
  constructor
  · rw [threeHop_disjoint_confidence_product_729_1000]
    norm_num [halfHorizonPolicy]
  · rw [threeHop_disjoint_tracked_envelope_width_one_eighth]
    norm_num

def lowConfidenceHalfLink (support : Finset ℕ) : ChainLinkCert :=
  ChainLinkCert.point support (1 / 2 : ℝ) (1 / 10 : ℝ)
    (by norm_num) (by norm_num)

def lowConfidenceThreeHopLinks : Fin 3 → ChainLinkCert :=
  fun i => lowConfidenceHalfLink (threeHopDisjointSupports i)

def lowConfidenceThreeHopChain : PathChainDatum 2 where
  links := lowConfidenceThreeHopLinks
  productExactness := PathProductExactness.of_links lowConfidenceThreeHopLinks
  sourceProfile := halfSourceProfile
  sourceCoupling := PathSourceCoupling.fromSourceUnion

theorem lowConfidence_threeHop_confidence_product_one_thousandth :
    pathChainConfidence lowConfidenceThreeHopChain = (1 / 1000 : ℝ) := by
  change pathConfidenceProduct lowConfidenceThreeHopLinks = (1 / 1000 : ℝ)
  norm_num [pathConfidenceProduct, lowConfidenceThreeHopLinks,
    lowConfidenceHalfLink, ChainLinkCert.point]

theorem lowConfidence_threeHop_chainVacuous :
    chainVacuous halfHorizonPolicy lowConfidenceThreeHopChain := by
  apply chainVacuous_of_confidence_lt
  rw [lowConfidence_threeHop_confidence_product_one_thousandth]
  norm_num [halfHorizonPolicy]

theorem lowConfidence_threeHop_not_chainInformative :
    ¬ chainInformative halfHorizonPolicy lowConfidenceThreeHopChain := by
  apply not_chainInformative_of_confidence_lt
  rw [lowConfidence_threeHop_confidence_product_one_thousandth]
  norm_num [halfHorizonPolicy]

theorem lowConfidence_threeHop_horizon_width_one :
    chainEnvelopeWidth
        (horizonEnvelope halfHorizonPolicy lowConfidenceThreeHopChain) = 1 := by
  apply horizonEnvelope_width_eq_one_of_confidence_lt
  rw [lowConfidence_threeHop_confidence_product_one_thousandth]
  norm_num [halfHorizonPolicy]

/-! ## W2 scalar-adapter examples -/

/-- A one-row calibration sample whose independence branch is true. -/
def onePositiveChainCalibrationSample : Fin 1 → SelectorSample :=
  fun _ =>
    { x := 1
      y := 0
      latentAssumption := true
      x_mem_unit := by norm_num
      y_mem_unit := by norm_num }

def weightOneSelector : EnvelopeSelector where
  weight := 1
  weight_mem_unit := by norm_num

theorem one_positive_chain_sample_weight_one_calibrated :
    empiricalCalibrationCondition onePositiveChainCalibrationSample
      weightOneSelector.weight := by
  norm_num [empiricalCalibrationCondition, onePositiveChainCalibrationSample,
    weightOneSelector, SelectorSample.gapWeight,
    SelectorSample.assumptionIndicator]

theorem weightOne_composedSelector_sound :
    (∀ d, ScalarEstimatorSoundOnTwoHop
      (calibratedComposedSelectorEstimator weightOneSelector) d) ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
        meanSquaredLossFixed onePositiveChainCalibrationSample
            weightOneSelector.weight ≤
          meanSquaredLossFixed onePositiveChainCalibrationSample r :=
  calibratedComposedSelector_sound (by norm_num)
    onePositiveChainCalibrationSample weightOneSelector
    one_positive_chain_sample_weight_one_calibrated

def confidenceOnlyUnitEstimator : ConfidenceOnlyEstimator where
  estimateConfidenceTwoHop := fun _ => 1
  estimateConfidence_mem_unit := by intro _; norm_num

def halfStrengthShrinker (s : ℝ) : ℝ :=
  s / 2

theorem halfStrengthShrinker_le_self :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, halfStrengthShrinker s ≤ s := by
  intro s hs
  unfold halfStrengthShrinker
  nlinarith [hs.1]

theorem disjoint_naiveProductStrength_one_quarter :
    naiveProductStrength disjointTwoHop = (1 / 4 : ℝ) := by
  change (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4
  norm_num

theorem disjoint_chain_envelope_lower_three_quarters :
    (chainCredalEnvelope disjointTwoHop).lower = (3 / 4 : ℝ) := by
  have hfreq :
      chainFrequencies disjointTwoHop =
        (fun i : Fin 2 => if i = 0 then (1 / 4 : ℝ) else (3 / 4 : ℝ)) := by
    funext i
    fin_cases i
    · simp [chainFrequencies, disjointTwoHop,
        TwoHopProductExactness.of_linkStrengths, disjointLeft, disjointRight,
        halfLink, ChainLinkCert.point]
      norm_num
    · simp [chainFrequencies, disjointTwoHop,
        TwoHopSourceCoupling.correctedStrength]
      rw [show disjointLeft.sourceSupport = ({0} : Finset ℕ) by rfl,
        show disjointRight.sourceSupport = ({1} : Finset ℕ) by rfl]
      simpa using disjoint_sources_union_three_quarters
  rw [chainCredalEnvelope, frechetUnionITV_lower]
  change maxFrequency 1 (chainFrequencies disjointTwoHop) = (3 / 4 : ℝ)
  rw [hfreq]
  apply le_antisymm
  · unfold maxFrequency
    apply Finset.sup'_le
    intro i _hi
    fin_cases i <;> norm_num
  · have h := frequency_le_maxFrequency
      (fun i : Fin 2 => if i = 0 then (1 / 4 : ℝ) else (3 / 4 : ℝ))
      (1 : Fin 2)
    norm_num at h
    exact h

theorem disjoint_underconfidence_gap :
    naiveProductStrength disjointTwoHop <
      (chainCredalEnvelope disjointTwoHop).lower := by
  rw [disjoint_naiveProductStrength_one_quarter,
    disjoint_chain_envelope_lower_three_quarters]
  norm_num

theorem confidenceOnly_not_sound_on_disjoint_underconfidence :
    ¬ ScalarEstimatorSoundOnTwoHop confidenceOnlyUnitEstimator.toScalar
      disjointTwoHop :=
  confidenceOnlyEstimator_not_sound_on_strengthViolation disjointTwoHop
    confidenceOnlyUnitEstimator disjoint_underconfidence_gap

theorem oneSidedShrinker_not_sound_on_disjoint_underconfidence :
    ¬ ((chainCredalEnvelope disjointTwoHop).lower ≤
          halfStrengthShrinker (naiveProductStrength disjointTwoHop) ∧
        halfStrengthShrinker (naiveProductStrength disjointTwoHop) ≤
          (chainCredalEnvelope disjointTwoHop).upper) :=
  oneSidedStrengthShrinker_not_sound_on_underconfidence disjointTwoHop
    halfStrengthShrinker halfStrengthShrinker_le_self
    disjoint_underconfidence_gap

end

end Mettapedia.Examples.PLN.DependenceAwareChainComposition
