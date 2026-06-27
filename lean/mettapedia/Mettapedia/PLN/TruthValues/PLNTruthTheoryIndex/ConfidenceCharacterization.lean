import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.CoreFourCrispness

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


/-! ## Confidence characterization endpoint -/

/-- Stable index-level alias for the finite singleton-posterior collapse
endpoint: compact predictive That's-All together with exact typed ITV
readouts. -/
theorem deFinetti_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
    (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (G : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :
    Mettapedia.KR.ConceptOntology.compactPredictiveThatsAll
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
          ({Mettapedia.KR.ConceptOntology.posteriorCanonicalExternalBoolProcessLaw M k l hZ} :
            Set (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
              (ℕ → Bool)))) ∧
      (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).lower =
        Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).upper =
        Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).width = 0 ∧
      (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).credibility = 1 ∧
      (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).midpoint =
        Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G := by
  exact
    Mettapedia.KR.ConceptOntology.posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
      M k l n hZ G hG

/-- Stable index-level alias for the proved infinite i.i.d. regime split: the
raw posterior process-law crown exists exactly in the zero-interior-mixing
regime. -/
theorem deFinetti_posterior_processLawCrown_iff_zeroInteriorMixingMass
    (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
      M k l hZ ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  exact
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ

/-- Stable index-level alias for the proved infinite i.i.d. canonical compact
predictive/process-law regime split.  The canonical compact predictive endpoint
always exists, and the stronger raw process-law crown exists exactly in the
zero-interior-mixing regime. -/
theorem deFinetti_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw (ℕ → Bool) :=
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw.ofProcess
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        Mettapedia.CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply (a := i))
    Mettapedia.KR.ConceptOntology.compactPredictiveThatsAll
      (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
          (ℕ → Bool)))) ∧
      (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
        M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    Mettapedia.KR.ConceptOntology.posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ

/-- Stable index-level alias for the public sigma-additive infinite i.i.d.
mixing-family package.  The canonical `Bool^ℕ` family attached to a Bernoulli-
mixture credal set computes exactly the same finite-prefix and compact
bounded-measurable PLN readouts as the analytic imprecise de Finetti family. -/
theorem deFinetti_canonical_external_mixing_family
    (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty) :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
      C hC := by
  exact
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_canonicalExternalMixingFamily
      C hC

/-- Stable index-level alias for the abstract infinite i.i.d. de Finetti crown
package built from analytic prefix laws plus an explicit finite-window
realization inside a compact carrier. -/
theorem deFinetti_analytic_mixingFamily_processLawCrown_of_prefixFiniteWindowRealization
    (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
        (ℕ → Bool))]
    (carrier :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
        (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
        carrier)
    (hClosed : ∀ n,
      IsClosed
        {P :
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
              (ℕ → Bool) |
          ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                hC).cylinders.marginalPrevision n P) ∈
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
              ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                    C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                    hC).localLower n)})
    (hRealize :
      (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
          hC).jointPrevisionsRealizedInCarrier
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessFiniteJointWindowSystem
          C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
          hC)
        carrier) :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
      C hC := by
  exact
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixFiniteWindowRealization
      C hC carrier hCompact hCarrierConvex hClosed hRealize

/-- Stable index-level alias for the concrete infinite i.i.d. de Finetti crown
package obtained from any carrier containing the explicit tail-false
finite-window realizers. -/
theorem deFinetti_analytic_mixingFamily_processLawCrown_of_prefixTailFalseExtensionCarrierSubset
    (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
        (ℕ → Bool))]
    (carrier :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
        (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
        carrier)
    (hClosed : ∀ n,
      IsClosed
        {P :
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
              (ℕ → Bool) |
          ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                hC).cylinders.marginalPrevision n P) ∈
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
              ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                    C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                    hC).localLower n)})
    (hSubset :
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.prefixTailFalseExtensionCarrier ⊆
        carrier) :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
      C hC := by
  exact
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixTailFalseExtensionCarrierSubset
        C hC carrier hCompact hCarrierConvex hClosed hSubset

/-- Stable index-level alias for the sharp F2 i.i.d. de Finetti boundary: the
external mixing-family readout is unconditional, while the raw all-gambles
analytic crown is equivalent to exact lower-prevision compatibility. -/
theorem deFinetti_analytic_mixingFamily_sharpCompatibilityCrown
    (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty) :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
        C hC ∧
      (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC ↔
        ∃ L : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision (ℕ → Bool),
          (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC).respectsLocalLower L) := by
  exact
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamily_sharpCompatibilityCrown
      C hC

/-- Stable index-level alias for the closed S2 verdict: the analytic raw crown
does not imply pointwise zero-interior for every member of the credal family. -/
theorem deFinetti_analytic_mixingFamily_rawCrown_not_implies_pointwiseZeroInterior :
    ¬ (∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC →
          Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.AnalyticMixingFamilyPointwiseZeroInterior C) := by
  exact
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.not_forall_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_imp_pointwiseZeroInterior_closed

/-- Stable index-level alias for the proved infinite MLN collapse theorem:
uniform Dobrushin small influence forces uniqueness of the infinite DLR
measure. -/
theorem infiniteMLN_paperUniformSmallTotalInfluence_implies_uniqueMeasure
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
      Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    M.PaperUniqueMeasure := by
  exact M.paperUniformSmallTotalInfluence_implies_paperUniqueMeasure hM

/-- Stable index-level alias for the first concrete infinite DLR/PLN contrast:
positive strict width on the reinforced line and Dobrushin collapse on the
zero-weight grid. -/
theorem infiniteMLN_reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast :
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.ConcreteDLRPLNContrast := by
  exact
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast

/-- Stable index-level alias for the symmetric-grid Ising reduction crown: the
high-temperature collapse theorem is proved, and the reduction turns a
low-temperature Peierls input into plus/minus separation and a strict PLN
interval. That Peierls input is now supplied unconditionally by
`symmetricGridZeroField_originPLNStrictIntervalCrown_of_axisAnchoredContourCode_twentyFour`,
so the low-temperature strict-interval direction is itself proved, not merely
reduced. -/
theorem infiniteMLN_symmetricGridZeroField_originPhaseCoexistenceReductionCrown :
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown := by
  exact
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.symmetricGridZeroField_originPhaseCoexistenceReductionCrown

/-- Focused, paper-facing endpoint for the confidence-formula characterization.

This deliberately packages only the proved surface:

* finite DOF/forcing characterization, including the DoF7 distinction/credal
  boundary through `credalProjectionTowerBoundary`, with both the generic
  setoid bridge and the OSLF observational specialization;
* explicit typed-STV canaries showing the residual degrees of freedom;
* the finite singleton-posterior exact ITV collapse;
* the infinite DLR/MLN specialization into width-complement ITVs, including
  the proved Dobrushin uniqueness theorem, a concrete strict-width-versus-
  collapse contrast, the symmetric-grid phase-coexistence reduction crown, and
  the public hypothesis-free low-temperature F4 strict-interval theorem
  `symmetricGridZeroField_originPLNStrictIntervalCrown_of_axisAnchoredContourCode_twentyFour`;
* the public sigma-additive imprecise de Finetti mixing-family object and the
  exact lower-prevision compatibility boundary for the analytic raw
  all-gambles process-law crown, plus conditional finite-window realization
  routes into that crown;
* the proved i.i.d. de Finetti compact-predictive / process-law regime split. -/
structure ConfidenceCharacterizationEndpointProfile where
  formulaCharacterization : FormulaCharacterizationProfile
  typedSTVSameStrengthCanHaveDifferentConfidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display
  typedSTVSameConfidenceCanHaveDifferentStrength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength
  walleyWidthComplementForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s)
      (_hχ : WidthComplementCompatible χ s) {n : ℝ} (_hn : 0 ≤ n),
        χ.encode n = (plnOddsCoordinate s hs).encode n
  credalProjectionTowerBoundary :
    CredalProjectionTowerProfile
  finiteCanonicalExactPredictiveITV :
    ∀ (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l n : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0)
      (G : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1),
      Mettapedia.KR.ConceptOntology.compactPredictiveThatsAll
          (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
            ({Mettapedia.KR.ConceptOntology.posteriorCanonicalExternalBoolProcessLaw M k l hZ} :
              Set (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
                (ℕ → Bool)))) ∧
        (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).lower =
          Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
        (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).upper =
          Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
        (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).width = 0 ∧
        (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).credibility = 1 ∧
        (Mettapedia.KR.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).midpoint =
          Mettapedia.KR.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G
  infiniteMLNCredalBridge :
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.InfiniteMLNCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteDLRQueryOutcomeITV :
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.DLRQueryOutcomePLNBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteProjectiveDeFinettiBridge :
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ProjectiveDeFinettiCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteCanonicalExternalMixingFamily :
    ∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
        C hC
  infiniteAnalyticMixingFamilySharpCompatibility :
    ∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
          C hC ∧
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
            C hC ↔
          ∃ L : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision (ℕ → Bool),
            (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
              C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
              hC).respectsLocalLower L)
  infiniteAnalyticMixingFamilyRawCrownDoesNotForcePointwiseZeroInterior :
    ¬ (∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC →
          Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.AnalyticMixingFamilyPointwiseZeroInterior C)
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :
    ∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty)
      [TopologicalSpace
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
          (ℕ → Bool))]
      (carrier :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
          (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
          carrier)
      (_hClosed : ∀ n,
        IsClosed
          {P :
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
                (ℕ → Bool) |
            ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                  C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                  hC).cylinders.marginalPrevision n P) ∈
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
                ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                      C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                      hC).localLower n)})
      (_hRealize :
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC).jointPrevisionsRealizedInCarrier
          (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessFiniteJointWindowSystem
            C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC)
          carrier),
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :
    ∀ (C : Set Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty)
      [TopologicalSpace
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
          (ℕ → Bool))]
      (carrier :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
          (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
          carrier)
      (_hClosed : ∀ n,
        IsClosed
          {P :
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
                (ℕ → Bool) |
            ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                  C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                  hC).cylinders.marginalPrevision n P) ∈
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
                ((Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                      C (fun M _ n => Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                      hC).localLower n)})
      (_hSubset :
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.prefixTailFalseExtensionCarrier ⊆
          carrier),
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC
  infiniteProcessLawCrownBoundary :
    ∀ (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
        M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0
  infiniteCanonicalCompactPredictiveProcessLawBoundary :
    ∀ (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (k l : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0),
      let A : Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw (ℕ → Bool) :=
        Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw.ofProcess
          (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.bernoulliMixtureCanonicalProcessMeasure
            (M.posteriorBernoulliMixture k l hZ))
          Mettapedia.CategoryTheory.coordProcess
          (by
            intro i
            exact measurable_pi_apply (a := i))
      Mettapedia.KR.ConceptOntology.compactPredictiveThatsAll
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
            (ℕ → Bool)))) ∧
        (Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
          M k l hZ ↔
          M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0)
  infiniteDobrushinUniqueness :
    ∀ {Atom ClauseId : Type} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
        Atom ClauseId),
      M.PaperUniformSmallTotalInfluence →
        M.PaperUniqueMeasure
  infiniteConcreteStrictWidthVsCollapseContrast :
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.ConcreteDLRPLNContrast
  infiniteSymmetricGridStrictIntervalCrown :
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.SymmetricGridZeroFieldOriginPLNStrictIntervalCrown
      (24 : ℝ)
  infiniteSymmetricGridPhaseCoexistenceReduction :
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown

/-- Current focused endpoint for the confidence-formula characterization. -/
noncomputable def confidenceCharacterizationEndpointProfile :
    ConfidenceCharacterizationEndpointProfile where
  formulaCharacterization :=
    formulaCharacterizationProfile
  typedSTVSameStrengthCanHaveDifferentConfidence :=
    typed_stv_same_strength_can_have_different_confidence
  typedSTVSameConfidenceCanHaveDifferentStrength :=
    typed_stv_same_confidence_can_have_different_strength
  walleyWidthComplementForcesPLNOdds :=
    walley_width_complement_forces_pln_odds
  credalProjectionTowerBoundary :=
    credalProjectionTowerProfile
  finiteCanonicalExactPredictiveITV :=
    deFinetti_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
  infiniteMLNCredalBridge :=
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.infiniteMLNCredalBridgeProfile
  infiniteDLRQueryOutcomeITV :=
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.dlrQueryOutcomePLNBridgeProfile
  infiniteProjectiveDeFinettiBridge :=
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.projectiveDeFinettiCredalBridgeProfile
  infiniteCanonicalExternalMixingFamily :=
    deFinetti_canonical_external_mixing_family
  infiniteAnalyticMixingFamilySharpCompatibility :=
    deFinetti_analytic_mixingFamily_sharpCompatibilityCrown
  infiniteAnalyticMixingFamilyRawCrownDoesNotForcePointwiseZeroInterior :=
    deFinetti_analytic_mixingFamily_rawCrown_not_implies_pointwiseZeroInterior
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :=
    deFinetti_analytic_mixingFamily_processLawCrown_of_prefixFiniteWindowRealization
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :=
    deFinetti_analytic_mixingFamily_processLawCrown_of_prefixTailFalseExtensionCarrierSubset
  infiniteProcessLawCrownBoundary :=
    deFinetti_posterior_processLawCrown_iff_zeroInteriorMixingMass
  infiniteCanonicalCompactPredictiveProcessLawBoundary :=
    deFinetti_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
  infiniteDobrushinUniqueness :=
    infiniteMLN_paperUniformSmallTotalInfluence_implies_uniqueMeasure
  infiniteConcreteStrictWidthVsCollapseContrast :=
    infiniteMLN_reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast
  infiniteSymmetricGridStrictIntervalCrown :=
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.symmetricGridZeroField_originPLNStrictIntervalCrown_of_axisAnchoredContourCode_twentyFour
  infiniteSymmetricGridPhaseCoexistenceReduction :=
    infiniteMLN_symmetricGridZeroField_originPhaseCoexistenceReductionCrown

/-- External runtime parity metadata for the arithmetic/provenance mirror.
This is not a proof object; the corresponding commands are run by the build
agent. -/
structure RuntimeParitySurface where
  projectionTowerPeTTaPath : String
  projectionTowerCeTTaPath : String
  projectionTowerExpectedChecks : Nat
  itvIDMPeTTaPath : String
  itvIDMCeTTaPath : String
  itvIDMExpectedChecks : Nat
  truthFunctionPeTTaPath : String
  truthFunctionCeTTaPath : String
  truthFunctionExpectedChecks : Nat
  strengthPriorPeTTaPath : String
  strengthPriorCeTTaPath : String
  strengthPriorExpectedChecks : Nat

/-- Current PeTTa/CeTTa parity surface for the projection-tower canary,
ITV/IDM arithmetic, typed bridge/provenance mirrors, PeTTa truth-function
confidence audit, and strength-prior canaries. -/
def plnITVIDMRuntimeParitySurface : RuntimeParitySurface where
  projectionTowerPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_projection_tower_bool_canary.metta"
  projectionTowerCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_projection_tower_bool_canary.metta"
  projectionTowerExpectedChecks := 15
  itvIDMPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_itv_idm_parity_golden.metta"
  itvIDMCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_itv_idm_parity_golden.metta"
  itvIDMExpectedChecks := 26
  truthFunctionPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_truth_parity_golden.metta"
  truthFunctionCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_truth_parity_golden.metta"
  truthFunctionExpectedChecks := 11
  strengthPriorPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_strength_prior_canary.metta"
  strengthPriorCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_strength_prior_canary.metta"
  strengthPriorExpectedChecks := 13


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
