import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.WalleyConstructorProfiles

namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Confidence revision chart laws -/

/-- Algebraic chart laws for confidence displays under additive evidence-weight
revision.  This profile records the current positive facts, canaries, and the
explicit-gate rigidity theorem for confidence-odds additivity on the
nonnegative evidence-weight axis.  It does not claim that arbitrary
reconstructive confidence charts are PLN. -/
structure ConfidenceRevisionChartProfile where
  confidenceOddsPLNWeight :
    ∀ {k n : ℝ} (hk : 0 < k) (_hn : 0 ≤ n),
      confidenceOdds ((plnOddsCoordinate k hk).encode n) = n / k
  confidenceOddsPLNRevisionAdditive :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k) (_h1 : 0 ≤ n1) (_h2 : 0 ≤ n2),
      confidenceOdds ((plnOddsCoordinate k hk).encode (n1 + n2)) =
        confidenceOdds ((plnOddsCoordinate k hk).encode n1) +
          confidenceOdds ((plnOddsCoordinate k hk).encode n2)
  transportedRevisionOfEncodedWeights :
    ∀ (χ : Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate)
      {w1 w2 : ℝ}, 0 ≤ w1 → 0 ≤ w2 →
        transportedConfidenceRevision χ (χ.encode w1) (χ.encode w2) =
          χ.encode (w1 + w2)
  transportedRevisionAssociativeOnNonnegativeWeights :
    ∀ (χ : Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate)
      {c1 c2 c3 : ℝ},
      0 ≤ χ.decode c1 → 0 ≤ χ.decode c2 → 0 ≤ χ.decode c3 →
        transportedConfidenceRevision χ
            (transportedConfidenceRevision χ c1 c2) c3 =
          transportedConfidenceRevision χ c1
            (transportedConfidenceRevision χ c2 c3)
  walleyWidthComplementEqualsPLNChart :
    ∀ {s n : ℝ} (hs : 0 < s) (_hn : 0 ≤ n),
      1 - walleyPredictiveWidth n s =
        (plnOddsCoordinate s hs).encode n
  walleyWidthComplementConfidenceOdds :
    ∀ {s n : ℝ} (_hs : 0 < s) (_hn : 0 ≤ n),
      confidenceOdds (1 - walleyPredictiveWidth n s) = n / s
  confidenceOddsWeightIdentityForcesPLN :
    ∀ {χ : Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k n : ℝ} (hk : 0 < k) (_hn : 0 ≤ n),
      χ.encode n ≠ 1 →
        confidenceOdds (χ.encode n) = n / k →
          χ.encode n = (plnOddsCoordinate k hk).encode n
  canonicalOddsAdditiveForcesPLN :
    ∀ {χ : Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ,
        0 ≤ x → 0 ≤ y →
        confidenceOdds (χ.encode (x + y)) =
          confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y)) →
      ContinuousOn
        (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)) →
      confidenceOdds (χ.encode 1) = 1 / k →
      (∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1) →
      ∀ {n : ℝ}, 0 ≤ n →
        χ.encode n = (plnOddsCoordinate k hk).encode n
  canonicalOddsMonotoneAdditiveForcesPLN :
    ∀ {χ : Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ,
        0 ≤ x → 0 ≤ y →
        confidenceOdds (χ.encode (x + y)) =
          confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y)) →
      MonotoneOn
        (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)) →
      confidenceOdds (χ.encode 1) = 1 / k →
      (∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1) →
      ∀ {n : ℝ}, 0 ≤ n →
        χ.encode n = (plnOddsCoordinate k hk).encode n
  plnOddsCoordinateSatisfiesCanonicalGates :
    ∀ {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
          confidenceOdds ((plnOddsCoordinate k hk).encode x) +
            confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
      ContinuousOn
        (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
        (Set.Ici (0 : ℝ)) ∧
      confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
      (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1)
  plnOddsCoordinateSatisfiesMonotoneCanonicalGates :
    ∀ {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
          confidenceOdds ((plnOddsCoordinate k hk).encode x) +
            confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
      MonotoneOn
        (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
        (Set.Ici (0 : ℝ)) ∧
      confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
      (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1)
  plnRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k) (_h1 : 0 ≤ n1) (_h2 : 0 ≤ n2),
      (plnOddsCoordinate k hk).encode (n1 + n2) =
        plnConfidenceRevision
          ((plnOddsCoordinate k hk).encode n1)
          ((plnOddsCoordinate k hk).encode n2)
  expCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (expCoordinate k hk).decode ((expCoordinate k hk).encode w) = w
  expRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k),
      (expCoordinate k hk).encode (n1 + n2) =
        expConfidenceRevision ((expCoordinate k hk).encode n1)
          ((expCoordinate k hk).encode n2)
  tanhCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (tanhCoordinate k hk).decode ((tanhCoordinate k hk).encode w) = w
  tanhRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k),
      (tanhCoordinate k hk).encode (n1 + n2) =
        tanhConfidenceRevision ((tanhCoordinate k hk).encode n1)
          ((tanhCoordinate k hk).encode n2)
  arctanCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (arctanCoordinate k hk).decode ((arctanCoordinate k hk).encode w) = w
  expRevisionDiffersFromPLN :
    expConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2)
  plnRevisionConfidenceOddsAdditiveAtHalf :
    confidenceOdds (plnConfidenceRevision (1 / 2) (1 / 2)) =
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2)
  expRevisionNotConfidenceOddsAdditiveAtHalf :
    confidenceOdds (expConfidenceRevision (1 / 2) (1 / 2)) ≠
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2)
  tanhRevisionDiffersFromPLN :
    tanhConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2)

/-- Current confidence-revision chart package.  PLN has additive confidence
odds and the Mobius transported law; exponential has the noisy-OR transported
law; tanh has the Einstein-style transported law; arctan is a reconstructive
non-Mobius chart.  Rigidity is included only under the explicit additive,
continuous or monotone, normalized, nonsingular confidence-odds hypotheses on
the nonnegative evidence-weight axis, together with PLN non-vacuity witnesses. -/
noncomputable def confidenceRevisionChartProfile : ConfidenceRevisionChartProfile where
  confidenceOddsPLNWeight := by
    intro k n hk hn
    exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk hn
  confidenceOddsPLNRevisionAdditive := by
    intro k n1 n2 hk h1 h2
    exact confidenceOdds_pln_revision_additive hk h1 h2
  transportedRevisionOfEncodedWeights := by
    intro χ w1 w2 h1 h2
    exact transportedConfidenceRevision_of_encoded_weights χ h1 h2
  transportedRevisionAssociativeOnNonnegativeWeights := by
    intro χ c1 c2 c3 h1 h2 h3
    exact transportedConfidenceRevision_assoc_of_nonneg χ h1 h2 h3
  walleyWidthComplementEqualsPLNChart := by
    intro s n hs hn
    exact walley_width_complement_eq_plnOddsCoordinate_encode hs hn
  walleyWidthComplementConfidenceOdds := by
    intro s n hs hn
    exact confidenceOdds_walley_width_complement_eq_weight_div hs hn
  confidenceOddsWeightIdentityForcesPLN := by
    intro χ k n hk hn hnot hχ
    exact confidenceOdds_weight_identity_forces_pln_encode hk hn hnot hχ
  canonicalOddsAdditiveForcesPLN := by
    intro χ k hk hadd hcont hnorm hnot n hn
    exact canonical_odds_additive_forces_pln hk hadd hcont hnorm hnot hn
  canonicalOddsMonotoneAdditiveForcesPLN := by
    intro χ k hk hadd hmono hnorm hnot n hn
    exact canonical_odds_monotone_additive_forces_pln hk hadd hmono hnorm hnot hn
  plnOddsCoordinateSatisfiesCanonicalGates := by
    intro k hk
    exact plnOddsCoordinate_satisfies_canonical_gates hk
  plnOddsCoordinateSatisfiesMonotoneCanonicalGates := by
    intro k hk
    exact plnOddsCoordinate_satisfies_monotone_canonical_gates hk
  plnRevisionClosedForm := by
    intro k n1 n2 hk h1 h2
    exact plnConfidence_revision_closedForm hk h1 h2
  expCoordinateReconstructs := by
    intro k hk w hw
    exact expCoordinate_decode_encode k hk hw
  expRevisionClosedForm := by
    intro k n1 n2 hk
    exact expCoordinate_revision_closedForm hk
  tanhCoordinateReconstructs := by
    intro k hk w hw
    exact tanhCoordinate_decode_encode k hk hw
  tanhRevisionClosedForm := by
    intro k n1 n2 hk
    exact tanhCoordinate_revision_closedForm hk
  arctanCoordinateReconstructs := by
    intro k hk w hw
    exact arctanCoordinate_decode_encode k hk hw
  expRevisionDiffersFromPLN :=
    expRevision_differs_from_plnRevision_at_half
  plnRevisionConfidenceOddsAdditiveAtHalf :=
    plnRevision_confidenceOdds_additive_at_half
  expRevisionNotConfidenceOddsAdditiveAtHalf :=
    expRevision_not_confidenceOdds_additive_at_half
  tanhRevisionDiffersFromPLN :=
    tanhRevision_differs_from_plnRevision_at_half

/-- Abstract torsor profile for fully lossless confidence charts with a fixed
display type.  This deliberately uses the stronger equivalence-based chart
type rather than the weaker `EvidenceWeightCoordinate`, whose contract is only
left-inverse reconstruction on nonnegative weights. -/
structure ConfidenceChartTorsorProfile where
  chartDifferenceTransitive :
    ∀ {Display : Type} (χ ψ : EvidenceWeightChartIso Display),
      reparametrizeChart (chartDifference χ ψ) χ = ψ
  chartActionFree :
    ∀ {Display : Type} (χ : EvidenceWeightChartIso Display)
      {σ τ : Equiv.Perm Display},
      reparametrizeChart σ χ = reparametrizeChart τ χ → σ = τ
  chartDifferenceUnique :
    ∀ {Display : Type} (χ ψ : EvidenceWeightChartIso Display)
      (σ : Equiv.Perm Display),
      reparametrizeChart σ χ = ψ ↔ σ = chartDifference χ ψ
  chartSelfDifferenceIdentity :
    ∀ {Display : Type} (χ : EvidenceWeightChartIso Display),
      chartDifference χ χ = Equiv.refl Display
  orderedChartDifferenceTransitive :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display),
      reparametrizeOrderedChart (orderedChartDifference χ ψ) χ = ψ
  orderedChartActionFree :
    ∀ {Display : Type} [LE Display]
      (χ : OrderedEvidenceWeightChartIso Display)
      {σ τ : Display ≃o Display},
      reparametrizeOrderedChart σ χ = reparametrizeOrderedChart τ χ → σ = τ
  orderedChartDifferenceUnique :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display)
      (σ : Display ≃o Display),
      reparametrizeOrderedChart σ χ = ψ ↔ σ = orderedChartDifference χ ψ
  orderedChartSelfDifferenceIdentity :
    ∀ {Display : Type} [LE Display]
      (χ : OrderedEvidenceWeightChartIso Display),
      orderedChartDifference χ χ = OrderIso.refl Display
  orderedChartActionForgetsToEquivAction :
    ∀ {Display : Type} [LE Display]
      (σ : Display ≃o Display) (χ : OrderedEvidenceWeightChartIso Display),
      (reparametrizeOrderedChart σ χ).toChartIso =
        reparametrizeChart σ.toEquiv χ.toChartIso
  orderedChartDifferenceForgetsToEquivDifference :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display),
      (orderedChartDifference χ ψ).toEquiv =
        chartDifference χ.toChartIso ψ.toChartIso
  rawPermutationNeedNotBeMonotone :
    ¬ Monotone (Equiv.swap false true : Equiv.Perm Bool)

/-- Fully lossless confidence charts form a torsor under display-space
reparametrizations: differences between charts are canonical, but no chart is
distinguished without an extra law such as Walley width complement or
canonical confidence-odds additivity. -/
noncomputable def confidenceChartTorsorProfile : ConfidenceChartTorsorProfile where
  chartDifferenceTransitive :=
    reparametrizeChart_chartDifference
  chartActionFree :=
    reparametrizeChart_free
  chartDifferenceUnique :=
    chartDifference_unique
  chartSelfDifferenceIdentity :=
    chartDifference_self
  orderedChartDifferenceTransitive :=
    reparametrizeOrderedChart_orderedChartDifference
  orderedChartActionFree :=
    reparametrizeOrderedChart_free
  orderedChartDifferenceUnique :=
    orderedChartDifference_unique
  orderedChartSelfDifferenceIdentity :=
    orderedChartDifference_self
  orderedChartActionForgetsToEquivAction :=
    reparametrizeOrderedChart_toChartIso
  orderedChartDifferenceForgetsToEquivDifference :=
    orderedChartDifference_toEquiv
  rawPermutationNeedNotBeMonotone :=
    boolSwap_not_monotone

/-- Generic ITVs expose the ambient degrees of freedom: width, credibility,
and point-projection selector are not mutually forced. -/
structure GenericITVProfile where
  widthDoesNotForceCredibility :
    ∃ itv₀ itv₁ : ITV,
      itv₀.width = itv₁.width ∧ itv₀.credibility ≠ itv₁.credibility
  credibilityDoesNotForceWidth :
    ∃ itv₀ itv₁ : ITV,
      itv₀.credibility = itv₁.credibility ∧ itv₀.width ≠ itv₁.width
  pointProjectionNotForced :
    ∃ itv : ITV,
      Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv

/-- The generic ITV profile is fully witnessed by explicit canaries. -/
def genericITVProfile : GenericITVProfile where
  widthDoesNotForceCredibility :=
    generic_itv_width_does_not_force_credibility
  credibilityDoesNotForceWidth :=
    generic_itv_credibility_does_not_force_width
  pointProjectionNotForced :=
    generic_itv_does_not_force_point_projection

/-- Strength projection profile: a generic interval does not choose one point
projection, while the current midpoint view is an ordered, unit-bounded
projection of any typed ITV and an average of the forced envelope in the credal
projection tower. -/
structure StrengthProjectionProfile where
  lowerMidpointUpperNotForced :
    ∃ itv : ITV,
      Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv
  typedITVLowerLeMidpoint :
    ∀ {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem),
      x.lower ≤ x.midpoint
  typedITVMidpointLeUpper :
    ∀ {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem),
      x.midpoint ≤ x.upper
  typedITVMidpointInUnit :
    ∀ {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem),
      x.midpoint ∈ Set.Icc (0 : ℝ) 1
  credalTowerMidpointAverage :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.midpointDisplay =
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            t.credal t.gamble +
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            t.credal t.gamble) / 2
  credalTowerLowerLeMidpoint :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.lower ≤ t.midpointDisplay
  credalTowerMidpointLeUpper :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.midpointDisplay ≤ t.toTypedITV.upper
  typedSTVSameStrengthDifferentConfidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display
  typedSTVSameConfidenceDifferentStrength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength
  improperPosteriorIsMLE :
    ∀ (e : Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts),
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.improper e =
        e.mleStrength
  posteriorMeanInUnit :
    ∀ (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
      (e : Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts),
      0 <
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorDenom ctx e →
        0 ≤
            Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ∧
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ≤ 1
  priorChoiceCanChangeDisplayedStrength :
    Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive.mleStrength = 1 ∧
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive =
        (2 / 3 : ℝ) ∧
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive.mleStrength ≠
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive
  natMleIsHaldane :
    ∀ (nPos nNeg : ℕ),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength =
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane nPos nNeg
  natUniformIsLaplace :
    ∀ (nPos nNeg : ℕ),
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predLaplace nPos nNeg
  natJeffreysIsKT :
    ∀ (nPos nNeg : ℕ),
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predJeffreys nPos nNeg
  natPriorMatters :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1).mleStrength = 0 ∧
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
          (1 / 3 : ℝ)
  laplaceDifferenceBound :
    ∀ (nPos nNeg : ℕ), nPos + nNeg ≠ 0 →
      |(Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
        2 / ((nPos : ℝ) + (nNeg : ℝ) + 2)
  jeffreysDifferenceBound :
    ∀ (nPos nNeg : ℕ), nPos + nNeg ≠ 0 →
      |(Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
            (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
        1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1))
  symmetricPriorConvergence :
    ∀ ε : ℝ, 0 < ε → ∀ priorParam : ℝ, 0 < priorParam →
      ∃ N : ℕ, ∀ nPos nNeg : ℕ, nPos + nNeg ≥ N → nPos + nNeg ≠ 0 →
        let strength :=
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength
        let mean :=
          ((nPos : ℝ) + priorParam) /
            ((nPos : ℝ) + (nNeg : ℝ) + 2 * priorParam)
        |strength - mean| < ε

/-- Current strength projection profile. -/
def strengthProjectionProfile : StrengthProjectionProfile where
  lowerMidpointUpperNotForced :=
    generic_itv_does_not_force_point_projection
  typedITVLowerLeMidpoint :=
    typed_itv_lower_le_midpoint
  typedITVMidpointLeUpper :=
    typed_itv_midpoint_le_upper
  typedITVMidpointInUnit :=
    typed_itv_midpoint_in_unit
  credalTowerMidpointAverage :=
    credal_projection_tower_midpoint_is_envelope_average
  credalTowerLowerLeMidpoint :=
    credal_projection_tower_lower_le_midpoint
  credalTowerMidpointLeUpper :=
    credal_projection_tower_midpoint_le_upper
  typedSTVSameStrengthDifferentConfidence :=
    typed_stv_same_strength_can_have_different_confidence
  typedSTVSameConfidenceDifferentStrength :=
    typed_stv_same_confidence_can_have_different_strength
  improperPosteriorIsMLE :=
    binary_counts_improper_posterior_strength_eq_mle
  posteriorMeanInUnit :=
    binary_counts_posterior_mean_strength_in_unit
  priorChoiceCanChangeDisplayedStrength :=
    binary_counts_uniform_prior_changes_displayed_strength
  natMleIsHaldane :=
    binary_counts_of_nat_mle_eq_haldane
  natUniformIsLaplace :=
    binary_counts_of_nat_uniform_eq_laplace
  natJeffreysIsKT :=
    binary_counts_of_nat_jeffreys_eq_kt
  natPriorMatters :=
    binary_counts_of_nat_prior_matters_example
  laplaceDifferenceBound :=
    binary_counts_haldane_vs_laplace_difference
  jeffreysDifferenceBound :=
    binary_counts_haldane_vs_jeffreys_difference
  symmetricPriorConvergence :=
    binary_counts_mle_converges_to_symmetric_posterior_mean

/-- Bayesian credible ITVs fix the credibility coordinate from evidence
concentration while leaving interval construction to backend/level choices. -/
structure BayesCredibleProfile where
  credibilityConcentration :
    ∀ (backend : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.CredibleIntervalBackend)
      (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
      (level : ℝ) (hlevel : 0 < level ∧ level < 1)
      (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence),
      (TypedITV.fromBayesCredible backend ctx level hlevel e).credibility =
        (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toConfidence
          (ctx.α₀ + ctx.β₀) e).toReal
  credibilityIndependentOfBackendLevel :
    ∀ (backend₁ backend₂ :
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.CredibleIntervalBackend)
      (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
      (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
      (level₁ level₂ : ℝ)
      (hlevel₁ : 0 < level₁ ∧ level₁ < 1)
      (hlevel₂ : 0 < level₂ ∧ level₂ < 1),
      (ITV.fromBayesCredibleWithBackend backend₁ e ctx level₁ hlevel₁).credibility =
        (ITV.fromBayesCredibleWithBackend backend₂ e ctx level₂ hlevel₂).credibility

/-- Bayesian credible profile: evidence concentration forces credibility, not
the interval backend. -/
def bayesCredibleProfile : BayesCredibleProfile where
  credibilityConcentration :=
    typed_bayes_credible_credibility_is_evidence_concentration
  credibilityIndependentOfBackendLevel :=
    ITV.fromBayesCredibleWithBackend_credibility_independent_of_backend_level

/-- Walley binary IDM narrows the confidence coordinate by the
width-complement bridge. -/
structure WalleyBinaryProfile where
  typedWidthComplement :
    ∀ (s : ℝ) (hs : 0 < s)
      (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence),
      (TypedITV.fromWalleyBinary s hs e).width +
        (TypedITV.fromWalleyBinary s hs e).credibility = 1
  widthComplementForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s),
      WidthComplementCompatible χ s →
        ∀ {n : ℝ}, 0 ≤ n → χ.encode n = (plnOddsCoordinate s hs).encode n
  reconstructiveNonWalleyCanary :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s

/-- Walley binary profile: generic reconstructivity is not enough; the
width-complement law is the forcing hypothesis. -/
def walleyBinaryProfile : WalleyBinaryProfile where
  typedWidthComplement :=
    typed_walley_binary_has_width_complement
  widthComplementForcesPLNOdds := by
    intro χ s hs hχ n hn
    exact walley_width_complement_forces_pln_odds χ s hs hχ hn
  reconstructiveNonWalleyCanary :=
    reconstructive_coordinate_need_not_be_walley_compatible

/-- Walley categorical IDM is the multinomial counterpart: category envelopes
come from the credal set and carry the same width-complement precision law. -/
structure WalleyCategoricalProfile where
  typedWidthComplement :
    ∀ {k : ℕ}
      (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k) (i : Fin k),
      (TypedITV.fromWalleyCategorical ctx e i).width +
        (TypedITV.fromWalleyCategorical ctx e i).credibility = 1
  typedCredibilityPrecision :
    ∀ {k : ℕ}
      (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k) (i : Fin k),
      (TypedITV.fromWalleyCategorical ctx e i).credibility =
        (e.total : ℝ) / Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmDenom ctx e
  widthMatchesCredalEnvelope :
    ∀ {k : ℕ}
      (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
      (i j : Fin k) (_ : j ≠ i),
      (TypedITV.fromWalleyCategorical ctx e i).width =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
            (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) -
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
            (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i)

/-- Walley categorical profile: multinomial IDM as typed ITV plus credal
envelope agreement. -/
def walleyCategoricalProfile : WalleyCategoricalProfile where
  typedWidthComplement :=
    typed_walley_categorical_has_width_complement
  typedCredibilityPrecision :=
    typed_walley_categorical_credibility_is_idm_precision
  widthMatchesCredalEnvelope :=
    typed_walley_categorical_width_matches_credal_envelope

/-- Mean/concentration coordinates are lossless evidence coordinates, but do
not choose a confidence link by themselves. -/
structure MeanConcentrationProfile where
  binaryPolarEquiv :
    {e : BinaryCounts // 0 < e.total} ≃ BinarySimplexScale
  binaryPolarToCountsTotal :
    ∀ z : BinarySimplexScale,
      (binarySimplexScaleToCounts z).total = z.total
  binaryPolarToCountsStrength :
    ∀ z : BinarySimplexScale,
      (binarySimplexScaleToCounts z).strength = z.strength
  binaryAddStrengthWeightedMixture :
    ∀ (e₁ e₂ : BinaryCounts),
      e₁.total ≠ 0 → e₂.total ≠ 0 → e₁.total + e₂.total ≠ 0 →
        (e₁.add e₂).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  binaryTypedRevisionStrengthWeightedMixture :
    ∀ (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts),
      (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
        (TypedSTV.fromCounts χ e₂)).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  binaryLossless :
    ∀ (e : BinaryCounts), e.total ≠ 0 →
      (BetaMeanConcentration.fromCounts e).decodeCounts =
        (e.nPlus, e.nMinus)
  binaryTypedSTVFactorsThroughMeanConcentration :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts),
      (BetaMeanConcentration.fromCounts e).toTypedSTV χ =
        TypedSTV.fromCounts χ e
  categoricalLossless :
    ∀ {k : ℕ}
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k),
      e.total ≠ 0 → ∀ i : Fin k,
        (DirichletMeanConcentration.fromCounts e).decodeCounts i =
          (e.counts i : ℝ)
  categoricalTypedTruthFactorsThroughMeanConcentration :
    ∀ {k : ℕ} (χ : EvidenceWeightCoordinate)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k),
      (DirichletMeanConcentration.fromCounts e).toTypedTruth χ =
        TypedCategoricalTruth.fromCounts χ e
  binaryLinkNotForced :
    let z : BetaMeanConcentration := ⟨1 / 2, 1⟩
    plnConfidenceLink 1 (by norm_num) z ≠
      reserveHalfLink 1 (by norm_num) z
  binaryBlendWeightIsConcentrationLink :
    ∀ (π : SymmetricBetaPrior) (e : BinaryCounts),
      π.blendWeight e =
        plnConfidenceLink (2 * π.prior) (by nlinarith [π.prior_pos])
          (BetaMeanConcentration.fromCounts e)
  binaryGeneralBetaBlendWeightIsConcentrationLink :
    ∀ (π : BetaPriorMeanConcentration) (e : BinaryCounts),
      π.blendWeight e =
        plnConfidenceLink π.concentration π.concentration_pos
          (BetaMeanConcentration.fromCounts e)
  binaryPosteriorMeanBlend :
    ∀ (π : SymmetricBetaPrior) (e : BinaryCounts),
      e.total ≠ 0 →
        π.posteriorMean e =
          π.blendWeight e * e.strength +
            (1 - π.blendWeight e) * (1 / 2 : ℝ)
  binaryGeneralBetaPosteriorMeanBlend :
    ∀ (π : BetaPriorMeanConcentration) (e : BinaryCounts),
      e.total ≠ 0 →
        π.posteriorMean e =
          π.blendWeight e * e.strength +
            (1 - π.blendWeight e) * π.mean
  binaryGeneralBetaPosteriorConcentrationSequential :
    ∀ (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts),
      π.posteriorConcentration (e₁.add e₂) =
        (π.posteriorPrior e₁).posteriorConcentration e₂
  binaryGeneralBetaPosteriorMeanSequential :
    ∀ (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts),
      π.posteriorMean (e₁.add e₂) =
        (π.posteriorPrior e₁).posteriorMean e₂
  binaryPriorMeanChangesPosteriorStrength :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₀ : BetaPriorMeanConcentration :=
      ⟨0, 2, by norm_num, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₀.posteriorMean e ≠ π₁.posteriorMean e
  binaryPriorConcentrationChangesBlendWeight :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩
    let π₂ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₁.blendWeight e ≠ π₂.blendWeight e
  binaryPosteriorMeanSequentialUpdateCanary :
    let π : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    let e₁ : BinaryCounts :=
      ⟨1, 1, by norm_num, by norm_num⟩
    let e₂ : BinaryCounts :=
      ⟨3, 1, by norm_num, by norm_num⟩
    π.posteriorMean (e₁.add e₂) = 5 / 8 ∧
      (π.posteriorPrior e₁).posteriorMean e₂ = 5 / 8 ∧
      π.posteriorMean (e₁.add e₂) ≠ (e₁.add e₂).strength
  categoricalLinkNotForced :
    let z : DirichletMeanConcentration 3 := ⟨fun _ => 1 / 3, 1⟩
    dirichletPLNConfidenceLink 1 (by norm_num) z ≠
      dirichletReserveHalfLink 1 (by norm_num) z
  categoricalBlendWeightIsConcentrationLink :
    ∀ {k : ℕ} (π : SymmetricDirichletPrior k) (hk : 0 < k)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k),
      π.blendWeight e =
        dirichletPLNConfidenceLink π.priorConcentration
          (by
            have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            unfold SymmetricDirichletPrior.priorConcentration
            exact mul_pos hkR π.prior_pos)
          (DirichletMeanConcentration.fromCounts e)
  categoricalPosteriorMeanBlend :
    ∀ {k : ℕ} (π : SymmetricDirichletPrior k) (_ : 0 < k)
      (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k),
      e.total ≠ 0 → ∀ i : Fin k,
        π.posteriorMean e i =
          π.blendWeight e * (DirichletMeanConcentration.fromCounts e).mean i +
            (1 - π.blendWeight e) * π.priorMean

/-- Mean/concentration profile: evidence coordinates are lossless, confidence
display is a separate link choice; under symmetric conjugate priors, the PLN
concentration link is exactly the posterior empirical/prior blend weight. -/
noncomputable def meanConcentrationProfile : MeanConcentrationProfile where
  binaryPolarEquiv :=
    positiveBinaryCountsEquivSimplexScale
  binaryPolarToCountsTotal :=
    binarySimplexScaleToCounts_total
  binaryPolarToCountsStrength :=
    binarySimplexScaleToCounts_strength
  binaryAddStrengthWeightedMixture :=
    BinaryCounts.add_strength_eq_weighted_mixture
  binaryTypedRevisionStrengthWeightedMixture :=
    typedSTV_revision_fromCounts_strength_eq_weighted_mixture
  binaryLossless :=
    binary_mean_concentration_is_lossless
  binaryTypedSTVFactorsThroughMeanConcentration :=
    BetaMeanConcentration.typedSTV_fromCounts_factors_through_betaCoordinate
  categoricalLossless := by
    intro k e hTotal i
    exact categorical_mean_concentration_is_lossless e hTotal i
  categoricalTypedTruthFactorsThroughMeanConcentration := by
    intro k χ e
    exact
      DirichletMeanConcentration.typedCategorical_fromCounts_factors_through_dirichletCoordinate
        χ e
  binaryLinkNotForced :=
    beta_coordinate_does_not_force_confidence_link
  binaryBlendWeightIsConcentrationLink :=
    symmetric_beta_blend_weight_is_concentration_link
  binaryGeneralBetaBlendWeightIsConcentrationLink :=
    general_beta_blend_weight_is_concentration_link
  binaryPosteriorMeanBlend :=
    symmetric_beta_posterior_mean_is_concentration_blend
  binaryGeneralBetaPosteriorMeanBlend :=
    general_beta_posterior_mean_is_concentration_blend
  binaryGeneralBetaPosteriorConcentrationSequential :=
    general_beta_posterior_concentration_add_is_sequential
  binaryGeneralBetaPosteriorMeanSequential :=
    general_beta_posterior_mean_add_is_sequential
  binaryPriorMeanChangesPosteriorStrength :=
    general_beta_prior_mean_changes_posterior_strength
  binaryPriorConcentrationChangesBlendWeight :=
    general_beta_prior_concentration_changes_blend_weight
  binaryPosteriorMeanSequentialUpdateCanary :=
    general_beta_posterior_mean_sequential_update_canary
  categoricalLinkNotForced :=
    dirichlet_coordinate_does_not_force_confidence_link
  categoricalBlendWeightIsConcentrationLink :=
    symmetric_dirichlet_blend_weight_is_concentration_link
  categoricalPosteriorMeanBlend := by
    intro k π hk e hTotal i
    exact symmetric_dirichlet_posterior_mean_is_concentration_blend
      π hk e hTotal i

/-- Information-geometric lift profile for the finite Bernoulli/Beta slice:
strength is the mean/m-coordinate, log support-odds is the natural/e-coordinate,
and concentration is the separate evidence-weight axis on which confidence
links live. -/
structure InformationGeometryLiftProfile where
  naturalToMeanPositive :
    ∀ θ : ℝ, 0 < bernoulliNaturalToMean θ
  naturalToMeanLtOne :
    ∀ θ : ℝ, bernoulliNaturalToMean θ < 1
  logOddsNaturalToMean :
    ∀ θ : ℝ, bernoulliLogOdds (bernoulliNaturalToMean θ) = θ
  naturalToMeanLogOdds :
    ∀ {p : ℝ}, 0 < p → p < 1 →
      bernoulliNaturalToMean (bernoulliLogOdds p) = p
  hellingerUnitCircle :
    ∀ {p : ℝ}, 0 ≤ p → p ≤ 1 →
      (bernoulliHellingerEmbedding p).1 ^ 2 +
          (bernoulliHellingerEmbedding p).2 ^ 2 = 1
  fisherMetricPositive :
    ∀ {p : ℝ}, 0 < p → p < 1 → 0 < bernoulliFisherMetric p
  fisherMetricHalf :
    bernoulliFisherMetric (1 / 2) = 4
  fisherTensorSymmetric :
    ∀ p v w : ℝ, bernoulliFisherTensor p v w = bernoulliFisherTensor p w v
  fisherTensorDiagPositive :
    ∀ {p v : ℝ}, 0 < p → p < 1 → v ≠ 0 →
      0 < bernoulliFisherTensor p v v
  fisherTensorHalf :
    ∀ v w : ℝ, bernoulliFisherTensor (1 / 2) v w = 4 * v * w
  mixtureGeodesicOpen :
    ∀ {p q t : ℝ}, 0 < p → p < 1 → 0 < q → q < 1 → 0 < t → t < 1 →
      0 < bernoulliMixtureGeodesic p q t ∧
        bernoulliMixtureGeodesic p q t < 1
  exponentialGeodesicOpen :
    ∀ p q t : ℝ,
      0 < bernoulliExponentialGeodesic p q t ∧
        bernoulliExponentialGeodesic p q t < 1
  exponentialGeodesicNaturalLinear :
    ∀ p q t : ℝ,
      bernoulliLogOdds (bernoulliExponentialGeodesic p q t) =
        (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q
  mixtureGeodesicVelocityPathAgrees :
    ∀ p q t : ℝ,
      bernoulliMixtureGeodesicVelocityPath p q t =
        bernoulliMixtureGeodesic p q t
  mixtureGeodesicConstantVelocity :
    ∀ p q t : ℝ,
      HasDerivAt (fun τ : ℝ => bernoulliMixtureGeodesic p q τ)
        (q - p) t
  exponentialGeodesicNaturalVelocityPathAgrees :
    ∀ p q t : ℝ,
      bernoulliExponentialGeodesicNaturalVelocityPath p q t =
        (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q
  exponentialGeodesicNaturalConstantVelocity :
    ∀ p q t : ℝ,
      HasDerivAt
        (fun τ : ℝ =>
          bernoulliLogOdds (bernoulliExponentialGeodesic p q τ))
        (bernoulliLogOdds q - bernoulliLogOdds p) t
  naturalFisherTensorSymmetric :
    ∀ θ u v : ℝ,
      bernoulliNaturalFisherTensor θ u v =
        bernoulliNaturalFisherTensor θ v u
  naturalFisherTensorDiagPositive :
    ∀ {θ u : ℝ}, u ≠ 0 → 0 < bernoulliNaturalFisherTensor θ u u
  naturalFisherTensorZero :
    ∀ u v : ℝ, bernoulliNaturalFisherTensor 0 u v = (1 / 4) * u * v
  fisherTensorPullbackLogOdds :
    ∀ θ u v : ℝ,
      bernoulliFisherTensor (bernoulliNaturalToMean θ)
          (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * u)
          (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * v) =
        bernoulliNaturalFisherTensor θ u v
  mixtureConnectionCoeffZero :
    ∀ p : ℝ, bernoulliMixtureConnectionCoeff p = 0
  exponentialConnectionCoeffZero :
    ∀ θ : ℝ, bernoulliExponentialConnectionCoeff θ = 0
  leviCivitaMeanConnectionCoeffHalf :
    bernoulliLeviCivitaMeanConnectionCoeff (1 / 2) = 0
  squaredHellingerNonnegative :
    ∀ p q : ℝ, 0 ≤ bernoulliSquaredHellinger p q
  squaredHellingerSymmetric :
    ∀ p q : ℝ, bernoulliSquaredHellinger p q = bernoulliSquaredHellinger q p
  squaredHellingerSelfZero :
    ∀ p : ℝ, bernoulliSquaredHellinger p p = 0
  klSelfZero :
    ∀ {p : ℝ}, 0 < p → p < 1 → bernoulliKL p p = 0
  jeffreysSymmetric :
    ∀ p q : ℝ, bernoulliJeffreys p q = bernoulliJeffreys q p
  jeffreysSelfZero :
    ∀ {p : ℝ}, 0 < p → p < 1 → bernoulliJeffreys p p = 0
  logOddsHalf :
    bernoulliLogOdds (1 / 2) = 0
  bornPositiveHellinger :
    ∀ {p : ℝ}, 0 ≤ p →
      bernoulliBornPositive (bernoulliHellingerEmbedding p) = p
  bornNegativeHellinger :
    ∀ {p : ℝ}, p ≤ 1 →
      bernoulliBornNegative (bernoulliHellingerEmbedding p) = 1 - p
  phaseForgetNotInjective :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  revisionStrengthMixture :
    ∀ (e₁ e₂ : BinaryCounts),
      e₁.total ≠ 0 → e₂.total ≠ 0 → e₁.total + e₂.total ≠ 0 →
        (e₁.add e₂).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  truthLogOddsTensorAdd :
    ∀ (x y : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence),
      x.neg ≠ 0 → y.neg ≠ 0 →
      x.truthOdds ≠ 0 → y.truthOdds ≠ 0 →
      x.truthOdds ≠ ⊤ → y.truthOdds ≠ ⊤ →
        (x * y).truthLogOdds = x.truthLogOdds + y.truthLogOdds
  meanConcentrationCoordinates : MeanConcentrationProfile

/-- The current finite Bernoulli/Beta information-geometry package.  It
records the Hellinger circle embedding, Fisher metric positivity, KL
self-zero, derivative-backed m/e geodesic velocities, m-flat revision,
e-flat tensor/log-odds composition, and the mean/concentration coordinate
surface. -/
noncomputable def informationGeometryLiftProfile : InformationGeometryLiftProfile where
  naturalToMeanPositive :=
    bernoulliNaturalToMean_pos
  naturalToMeanLtOne :=
    bernoulliNaturalToMean_lt_one
  logOddsNaturalToMean :=
    bernoulliLogOdds_naturalToMean
  naturalToMeanLogOdds := by
    intro p hp0 hp1
    exact bernoulliNaturalToMean_logOdds hp0 hp1
  hellingerUnitCircle := by
    intro p hp0 hp1
    exact bernoulliHellingerEmbedding_unit_circle hp0 hp1
  fisherMetricPositive := by
    intro p hp0 hp1
    exact bernoulliFisherMetric_pos hp0 hp1
  fisherMetricHalf :=
    bernoulliFisherMetric_half
  fisherTensorSymmetric :=
    bernoulliFisherTensor_symm
  fisherTensorDiagPositive := by
    intro p v hp0 hp1 hv
    exact bernoulliFisherTensor_diag_pos hp0 hp1 hv
  fisherTensorHalf :=
    bernoulliFisherTensor_half
  mixtureGeodesicOpen := by
    intro p q t hp0 hp1 hq0 hq1 ht0 ht1
    exact bernoulliMixtureGeodesic_in_open_simplex
      hp0 hp1 hq0 hq1 ht0 ht1
  exponentialGeodesicOpen :=
    bernoulliExponentialGeodesic_in_open_simplex
  exponentialGeodesicNaturalLinear :=
    bernoulliLogOdds_exponentialGeodesic
  mixtureGeodesicVelocityPathAgrees :=
    bernoulliMixtureGeodesicVelocityPath_eq_geodesic
  mixtureGeodesicConstantVelocity :=
    bernoulliMixtureGeodesic_hasDerivAt
  exponentialGeodesicNaturalVelocityPathAgrees :=
    bernoulliExponentialGeodesicNaturalVelocityPath_eq_linear
  exponentialGeodesicNaturalConstantVelocity :=
    bernoulliLogOdds_exponentialGeodesic_hasDerivAt
  naturalFisherTensorSymmetric :=
    bernoulliNaturalFisherTensor_symm
  naturalFisherTensorDiagPositive := by
    intro θ u hu
    exact bernoulliNaturalFisherTensor_diag_pos hu
  naturalFisherTensorZero :=
    bernoulliNaturalFisherTensor_zero
  fisherTensorPullbackLogOdds :=
    bernoulliFisherTensor_pullback_logOdds
  mixtureConnectionCoeffZero :=
    bernoulliMixtureConnectionCoeff_zero
  exponentialConnectionCoeffZero :=
    bernoulliExponentialConnectionCoeff_zero
  leviCivitaMeanConnectionCoeffHalf :=
    bernoulliLeviCivitaMeanConnectionCoeff_half
  squaredHellingerNonnegative :=
    bernoulliSquaredHellinger_nonneg
  squaredHellingerSymmetric :=
    bernoulliSquaredHellinger_symm
  squaredHellingerSelfZero :=
    bernoulliSquaredHellinger_self
  klSelfZero := by
    intro p hp0 hp1
    exact bernoulliKL_self hp0 hp1
  jeffreysSymmetric :=
    bernoulliJeffreys_symm
  jeffreysSelfZero := by
    intro p hp0 hp1
    exact bernoulliJeffreys_self hp0 hp1
  logOddsHalf :=
    bernoulliLogOdds_half
  bornPositiveHellinger := by
    intro p hp0
    exact bernoulliBornPositive_hellinger hp0
  bornNegativeHellinger := by
    intro p hp1
    exact bernoulliBornNegative_hellinger hp1
  phaseForgetNotInjective :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  revisionStrengthMixture :=
    binaryRevisionStrength_is_mixture_coordinate
  truthLogOddsTensorAdd := by
    intro x y hx_neg hy_neg hx0 hy0 hxTop hyTop
    exact binaryTruthLogOdds_tensor_is_natural_coordinate
      x y hx_neg hy_neg hx0 hy0 hxTop hyTop
  meanConcentrationCoordinates :=
    meanConcentrationProfile


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
