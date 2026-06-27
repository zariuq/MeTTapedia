import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.NaturalExtension

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


/-! ## Core-four local completion profile -/

/-- Completion profile for the four finite/provenance threads Zar asked to
close locally:

1. confidence coordinate freedom/forcing;
2. strength projection taxonomy;
3. typed ITV provenance;
4. finite credal/lower-prevision/desirable-gamble loop.

This is a local finite/provenance completion package.  It deliberately does not
claim the full infinite Walley natural-extension theorem. -/
structure CoreFourCompletionProfile where
  confidence : ConfidenceFormulaAuditProfile
  confidenceReconstructionBoundary :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  confidenceWalleyBridgeForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s),
      WidthComplementCompatible χ s →
        ∀ {n : ℝ}, 0 ≤ n → χ.encode n = (plnOddsCoordinate s hs).encode n
  confidenceNonPLNCoordinateCanary :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s
  strength : StrengthProjectionProfile
  strengthSelectorFreedom :
    ∃ itv : ITV,
      Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv
  strengthTypedMidpointBounds :
    ∀ {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem),
      x.lower ≤ x.midpoint ∧ x.midpoint ≤ x.upper ∧
        x.midpoint ∈ Set.Icc (0 : ℝ) 1
  typedITV : WorldModelTypedITVProfile
  typedBinaryRawCoordinateViews :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).value =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITV
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).lower =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVLower
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).upper =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVUpper
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).width =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVWidth
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).credibility =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVCredibility
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).midpoint =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVStrength
            (State := State) (Query := Query) sem ctx W q
  typedSigmaRawCoordinateViews :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).lower =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVLower
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).upper =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVUpper
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).width =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVWidth
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).credibility =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVCredibility
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).midpoint =
          Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVStrength
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  finiteCredalLoop : NaturalExtensionProfile
  finiteLowerPrevisionToDesirableToLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) = P
  finiteStrictRoundTripFixedIffArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_strict_roundtrip C = C ↔ archimedean_desirable_set C
  finiteStrictRoundTripGreatestArchimedeanSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        D.D ⊆ C.D → D.D ⊆ (finite_strict_roundtrip C).D
  finiteProjectionNonInjectivityCanary :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool)

/-- The verified local completion package for the first four threads. -/
noncomputable def coreFourCompletionProfile : CoreFourCompletionProfile where
  confidence := confidenceFormulaAuditProfile
  confidenceReconstructionBoundary :=
    reconstructive_confidence_coordinates_iff_left_inverse
  confidenceWalleyBridgeForcesPLNOdds := by
    intro χ s hs hχ n hn
    exact walley_width_complement_forces_pln_odds χ s hs hχ hn
  confidenceNonPLNCoordinateCanary :=
    reconstructive_coordinate_need_not_be_walley_compatible
  strength := strengthProjectionProfile
  strengthSelectorFreedom :=
    generic_itv_does_not_force_point_projection
  strengthTypedMidpointBounds := by
    intro Sem x
    exact ⟨typed_itv_lower_le_midpoint x, typed_itv_midpoint_le_upper x,
      typed_itv_midpoint_in_unit x⟩
  typedITV := worldModelTypedITVProfile
  typedBinaryRawCoordinateViews := by
    intro State Query Ctx instE instWM sem ctx W q
    exact ⟨Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_value_eq_queryITV
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_lower_eq_queryITVLower
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_upper_eq_queryITVUpper
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_width_eq_queryITVWidth
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_credibility_eq_queryITVCredibility
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_strength_eq_queryITVStrength
        (State := State) (Query := Query) sem ctx W q⟩
  typedSigmaRawCoordinateViews := by
    intro State Srt Ctx Query instE instWM sem ctx W q
    exact ⟨Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_value_eq_queryITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_lower_eq_queryITVLower
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_upper_eq_queryITVUpper
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_width_eq_queryITVWidth
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_credibility_eq_queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_strength_eq_queryITVStrength
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q⟩
  finiteCredalLoop := naturalExtensionProfile
  finiteLowerPrevisionToDesirableToLowerPrevision :=
    finite_lower_prevision_desirable_roundtrip
  finiteStrictRoundTripFixedIffArchimedean :=
    finite_strict_roundtrip_eq_iff_archimedean
  finiteStrictRoundTripGreatestArchimedeanSubset :=
    finite_strict_roundtrip_greatest_archimedean_subset_D
  finiteProjectionNonInjectivityCanary :=
    bool_positive_cones_projection_not_injective

/-! ## Crispness and imprecision collapse -/

/-- Crispness is not a display choice.  It is forced exactly when the retained
precision object collapses: a unique `Θ`, a singleton credal set, or a precise
lower prevision.  Disagreement and incomparability are the corresponding
canaries that force honest interval/credal semantics. -/
structure CrispnessCollapseProfile where
  thetaSingletonCollapse :
    ∀ {α β : Type} [CompleteLattice β] (Θ₀ : α → β),
      Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.intervalOfFamily
        (Set.singleton Θ₀) = ⟨Θ₀, Θ₀⟩
  thetaSubsingletonLowerEqUpper :
    ∀ {α β : Type} [CompleteLattice β]
      {Θs : Set (α → β)},
      Θs.Subsingleton → Θs.Nonempty → ∀ x : α,
        Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.lower Θs x =
          Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.upper Θs x
  credalSingletonCollapse :
    ∀ (Ω : Type) [Fintype Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Set.singleton P) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Set.singleton P) f
  credalDisagreementCreatesInterval :
    ∀ {Ω : Type} [Fintype Ω]
      (P Q : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.expectedValue P f <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.expectedValue Q f →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Set.insert P (Set.singleton Q)) f <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Set.insert P (Set.singleton Q)) f
  lowerPrevisionZeroImprecisionIffPrecise :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      (∀ X, Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X = 0) ↔
        P.isPrecise
  lowerPrevisionPreciseIffAdditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      P.isPrecise ↔ ∀ X Y, P (X + Y) = P X + P Y
  ksIncomparabilityBlocksCrispPoint :
    ∀ {α : Type}
      [KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra α]
      (x y : α),
      KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra.Incomparable
        x y →
        ¬ ∃ (Θ : α → ℝ), ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b

/-- Crispness-collapse profile: singleton/subsingleton completions collapse
to point semantics; singleton credal sets collapse; disagreement and
incomparability force interval semantics; lower-prevision precision is exactly
zero imprecision, equivalently additivity. -/
def crispnessCollapseProfile : CrispnessCollapseProfile where
  thetaSingletonCollapse :=
    thetaSingleton_collapses_to_point
  thetaSubsingletonLowerEqUpper := by
    intro α β inst Θs hsub hne x
    exact
      Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.lower_eq_upper_of_subsingleton
        hsub hne x
  credalSingletonCollapse :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.V3_is_singleton_collapse
  credalDisagreementCreatesInterval := by
    intro Ω inst P Q f hPQ
    exact
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.V2_intervals_exist_general
        P Q f hPQ
  lowerPrevisionZeroImprecisionIffPrecise :=
    lowerPrevision_zero_imprecision_iff_precise
  lowerPrevisionPreciseIffAdditive :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.precise_iff_additive
  ksIncomparabilityBlocksCrispPoint := by
    intro α inst x y hxy
    exact ks_incomparable_forces_no_faithful_point_representation x y hxy

/-! ## Degrees of freedom versus forcing capstone -/

/-- Capstone view of the current theory.  Each field is either a genuine
forcing law or an explicit canary showing a remaining degree of freedom.
This is the compact answer to: which coordinates are mathematical
consequences, and which are modeling choices? -/
structure DegreesOfFreedomForcingProfile where
  reconstructiveCoordinatesNeedLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      (∀ {nPlus nMinus : ℝ},
        0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
          (let n := nPlus + nMinus
           let stv : ℝ × ℝ := (nPlus / n, encode n)
           let m := decode stv.2
           (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus)) →
        ∀ {w : ℝ}, 0 < w → decode (encode w) = w
  reconstructiveCoordinatesIffLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  reconstructiveCoordinatesWithLeftInverseSuffice :
    ∀ (χ : EvidenceWeightCoordinate) {nPlus nMinus : ℝ},
      0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
        χ.decodeCounts (χ.encodeCounts nPlus nMinus) =
          (nPlus, nMinus)
  reconstructiveCoordinateCanFailWalleyBridge :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionCharts : ConfidenceRevisionChartProfile
  confidenceFormulaAudit : ConfidenceFormulaAuditProfile
  informationGeometryLift : InformationGeometryLiftProfile
  amplitudePhaseBoundary : AmplitudePhasePLNProfile
  genericITVFreedom : GenericITVProfile
  bayesCredibilityNotBackendLevel : BayesCredibleProfile
  meanConcentrationLinkFreedom : MeanConcentrationProfile
  walleyBridgeForcesPLNOdds : WalleyBinaryProfile
  walleyCategoricalCredalLift : WalleyCategoricalProfile
  strengthProjectionForcing : StrengthProjectionProfile
  sufficientStatisticForcing : SufficientStatisticQueryProfile
  typedCompatibilityBoundary : TypedITVOperationProfile
  worldModelTypedITVBoundary : WorldModelTypedITVProfile
  credalProjectionForcing : CredalForcedQueryProfile
  credalProjectionTowerBoundary : CredalProjectionTowerProfile
  naturalExtensionDiscipline : NaturalExtensionProfile
  crispnessCollapseForcing : CrispnessCollapseProfile

/-- The current DOF/forcing capstone: reconstruction gives only invertibility;
generic ITVs leave width, credibility, and selector free; Bayes constructors
force the evidence-concentration coordinate but not interval backend/level;
Walley-IDM width complement forces PLN odds; and retained evidence/credal
objects force their canonical projections. -/
noncomputable def degreesOfFreedomForcingProfile : DegreesOfFreedomForcingProfile where
  reconstructiveCoordinatesNeedLeftInverse :=
    reconstructive_confidence_coordinates_need_left_inverse
  reconstructiveCoordinatesIffLeftInverse :=
    reconstructive_confidence_coordinates_iff_left_inverse
  reconstructiveCoordinatesWithLeftInverseSuffice :=
    evidence_weight_coordinate_suffices_for_binary_count_reconstruction
  reconstructiveCoordinateCanFailWalleyBridge :=
    reconstructive_coordinate_need_not_be_walley_compatible
  confidenceChartTorsor :=
    confidenceChartTorsorProfile
  confidenceRevisionCharts :=
    confidenceRevisionChartProfile
  confidenceFormulaAudit :=
    confidenceFormulaAuditProfile
  informationGeometryLift :=
    informationGeometryLiftProfile
  amplitudePhaseBoundary :=
    amplitudePhasePLNProfile
  genericITVFreedom :=
    genericITVProfile
  bayesCredibilityNotBackendLevel :=
    bayesCredibleProfile
  meanConcentrationLinkFreedom :=
    meanConcentrationProfile
  walleyBridgeForcesPLNOdds :=
    walleyBinaryProfile
  walleyCategoricalCredalLift :=
    walleyCategoricalProfile
  strengthProjectionForcing :=
    strengthProjectionProfile
  sufficientStatisticForcing :=
    sufficientStatisticQueryProfile
  typedCompatibilityBoundary :=
    typedITVOperationProfile
  worldModelTypedITVBoundary :=
    worldModelTypedITVProfile
  credalProjectionForcing :=
    credalForcedQueryProfile
  credalProjectionTowerBoundary :=
    credalProjectionTowerProfile
  naturalExtensionDiscipline :=
    naturalExtensionProfile
  crispnessCollapseForcing :=
    crispnessCollapseProfile

/-- Paper-facing DOF-vs-forcing synthesis.

This profile is intentionally redundant with the lower profiles: its purpose is
to provide a readable theorem map for exposition.  It separates the canonical
simplex/scale strength coordinate, the torsorial confidence-chart freedom, the
extra laws that pick the PLN chart, the mean/natural/concentration
information-geometry split, and the boundary where relative phase would be
additional structure beyond the current real Hellinger/Born shadow. -/
structure PaperFacingDOFForcingSynthesisProfile where
  strengthDirectionAndConcentration :
    MeanConcentrationProfile
  confidenceChartsHaveTorsorFreedom :
    ConfidenceChartTorsorProfile
  reconstructiveConfidenceIffLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  revisionAndCanonicalOddsPickPLN :
    ConfidenceRevisionChartProfile
  walleyWidthComplementPicksPLN :
    WalleyBinaryProfile
  betaPriorMeanAndConcentrationAreTheLearnableAxes :
    MeanConcentrationProfile
  bernoulliInformationGeometry :
    InformationGeometryLiftProfile
  amplitudePhaseExtensionBoundary :
    AmplitudePhasePLNProfile
  phaseIsExtraStructureBeyondClassicalAmplitude :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  fullDOFForcingWall :
    DegreesOfFreedomForcingProfile

/-- The current paper-facing synthesis theorem map. -/
noncomputable def paperFacingDOFForcingSynthesisProfile :
    PaperFacingDOFForcingSynthesisProfile where
  strengthDirectionAndConcentration :=
    meanConcentrationProfile
  confidenceChartsHaveTorsorFreedom :=
    confidenceChartTorsorProfile
  reconstructiveConfidenceIffLeftInverse :=
    reconstructive_confidence_coordinates_iff_left_inverse
  revisionAndCanonicalOddsPickPLN :=
    confidenceRevisionChartProfile
  walleyWidthComplementPicksPLN :=
    walleyBinaryProfile
  betaPriorMeanAndConcentrationAreTheLearnableAxes :=
    meanConcentrationProfile
  bernoulliInformationGeometry :=
    informationGeometryLiftProfile
  amplitudePhaseExtensionBoundary :=
    amplitudePhasePLNProfile
  phaseIsExtraStructureBeyondClassicalAmplitude :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  fullDOFForcingWall :=
    degreesOfFreedomForcingProfile

/-- Compact paper-facing formula characterization profile.

This is the high-level theorem map: strength is the simplex direction;
confidence is a chart on concentration; chart freedom is torsorial until an
extra law chooses a member; revision and Walley laws distinguish the PLN chart;
and the Bernoulli/Beta IG slice separates mean, natural log-odds, and
concentration. -/
structure FormulaCharacterizationProfile where
  strengthAndConcentration : MeanConcentrationProfile
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionAndForcing : ConfidenceRevisionChartProfile
  informationGeometry : InformationGeometryLiftProfile
  amplitudePhaseBoundary : AmplitudePhasePLNProfile
  degreesOfFreedomForcing : DegreesOfFreedomForcingProfile
  paperFacingSynthesis : PaperFacingDOFForcingSynthesisProfile

/-- The current paper-facing DOF-vs-forcing theorem map. -/
noncomputable def formulaCharacterizationProfile :
    FormulaCharacterizationProfile where
  strengthAndConcentration :=
    meanConcentrationProfile
  confidenceChartTorsor :=
    confidenceChartTorsorProfile
  confidenceRevisionAndForcing :=
    confidenceRevisionChartProfile
  informationGeometry :=
    informationGeometryLiftProfile
  amplitudePhaseBoundary :=
    amplitudePhasePLNProfile
  degreesOfFreedomForcing :=
    degreesOfFreedomForcingProfile
  paperFacingSynthesis :=
    paperFacingDOFForcingSynthesisProfile


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
