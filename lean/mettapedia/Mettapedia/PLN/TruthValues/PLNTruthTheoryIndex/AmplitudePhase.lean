import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceRevisionCharts

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


/-! ## Amplitude/phase extension boundary -/

/-- Amplitude/phase PLN boundary profile.

This profile connects the current classical PLN truth-value tower to a possible
amplitude extension without overclaiming that such an extension is complete:
standard PLN is the Born shadow of a phaseless/forgotten-amplitude projection,
relative phase is invisible to the standard typed-STV view, coherent
interference differs from incoherent probability addition, and the
two-dimensional KS-style algebra carrier selected by positive-definite norm is
the complex/negative-`μ` carrier. -/
structure AmplitudePhasePLNProfile where
  bornStrengthFromHellinger :
    ∀ {p concentration phase : ℝ}, 0 ≤ p →
      (BinaryAmplitudePhaseState.fromStrengthConcentration
        p concentration phase).bornStrength = p
  bornCounterStrengthFromHellinger :
    ∀ {p concentration phase : ℝ}, p ≤ 1 →
      (BinaryAmplitudePhaseState.fromStrengthConcentration
        p concentration phase).bornCounterStrength = 1 - p
  countsBornStrength :
    ∀ (e : BinaryCounts), 0 < e.total → ∀ phase : ℝ,
      (BinaryAmplitudePhaseState.fromCounts e phase).bornStrength =
        e.strength
  countsBornCounterStrength :
    ∀ (e : BinaryCounts), 0 < e.total → ∀ phase : ℝ,
      (BinaryAmplitudePhaseState.fromCounts e phase).bornCounterStrength =
        1 - e.strength
  countsProjectToStandardStrength :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts),
      0 < e.total → ∀ phase : ℝ,
        ((BinaryAmplitudePhaseState.fromCounts e phase).toTypedSTV χ).strength =
          e.strength
  countsProjectToStandardConfidence :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts) (phase : ℝ),
      ((BinaryAmplitudePhaseState.fromCounts e phase).toTypedSTV χ).confidence =
        TypedConfidence.ofWeight χ e.total
  phaseNotVisibleToStandardPLN :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let a := BinaryAmplitudePhaseState.fromStrengthConcentration (1 / 2) 1 0
    let b := BinaryAmplitudePhaseState.fromStrengthConcentration (1 / 2) 1 1
    a ≠ b ∧ a.toTypedSTV χ = b.toTypedSTV χ
  phaseForgetNotInjective :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  coherentWeightInterferenceLaw :
    ∀ r s cosDelta : ℝ,
      coherentTwoPathWeight r s cosDelta =
        incoherentTwoPathWeight r s + 2 * r * s * cosDelta
  zeroInterferenceIsIncoherent :
    ∀ r s : ℝ, coherentTwoPathWeight r s 0 = incoherentTwoPathWeight r s
  constructiveInterferenceCanary :
    coherentTwoPathWeight 1 1 1 ≠ incoherentTwoPathWeight 1 1
  destructiveInterferenceCanary :
    coherentTwoPathWeight 1 1 (-1) ≠ incoherentTwoPathWeight 1 1
  phaseFactorIsExponential :
    ∀ θ : ℝ, complexPhaseFactor θ = Complex.exp ((θ : ℂ) * Complex.I)
  complexAmplitudeIsExponential :
    ∀ r θ : ℝ, complexAmplitude r θ =
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  complexPhaseFactorUnitWeight :
    ∀ θ : ℝ, Complex.normSq (complexPhaseFactor θ) = 1
  complexAmplitudeBornWeight :
    ∀ r θ : ℝ, Complex.normSq (complexAmplitude r θ) = r ^ 2
  complexHellingerBornWeight :
    ∀ {p θ : ℝ}, 0 ≤ p →
      Complex.normSq (complexHellingerAmplitude p θ) = p
  complexTwoPathInterferenceLaw :
    ∀ r s θ φ : ℝ,
      complexTwoPathBornWeight r s θ φ =
        r ^ 2 + s ^ 2 + 2 * r * s * Real.cos (θ - φ)
  complexTwoPathReducesToCoherentWeight :
    ∀ r s θ φ : ℝ,
      complexTwoPathBornWeight r s θ φ =
        coherentTwoPathWeight r s (Real.cos (θ - φ))
  complexConstructiveInterference :
    complexTwoPathBornWeight 1 1 0 0 = 4
  complexDestructiveInterference :
    complexTwoPathBornWeight 1 1 0 Real.pi = 0
  ksComplexCarrierEquivComplex :
    KSComplexPhaseCarrier ≃+* ℂ
  ksComplexCarrierPositiveDefinite :
    ∀ z : KSComplexPhaseCarrier,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)
  dualCarrierFailsPositiveDefinite :
    ¬ ∀ z : MuAlgebra 0,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)
  splitCarrierFailsPositiveDefinite :
    ¬ ∀ z : MuAlgebra 1,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)

/-- The current amplitude/phase boundary package. -/
noncomputable def amplitudePhasePLNProfile : AmplitudePhasePLNProfile where
  bornStrengthFromHellinger := by
    intro p concentration phase hp0
    exact BinaryAmplitudePhaseState.fromStrengthConcentration_bornStrength hp0
  bornCounterStrengthFromHellinger := by
    intro p concentration phase hp1
    exact BinaryAmplitudePhaseState.fromStrengthConcentration_bornCounterStrength hp1
  countsBornStrength :=
    BinaryAmplitudePhaseState.fromCounts_bornStrength
  countsBornCounterStrength :=
    BinaryAmplitudePhaseState.fromCounts_bornCounterStrength
  countsProjectToStandardStrength := by
    intro χ e hTotal phase
    exact BinaryAmplitudePhaseState.fromCounts_toTypedSTV_strength
      χ e hTotal phase
  countsProjectToStandardConfidence :=
    BinaryAmplitudePhaseState.fromCounts_toTypedSTV_confidence
  phaseNotVisibleToStandardPLN :=
    BinaryAmplitudePhaseState.phase_not_visible_to_standard_pln_view
  phaseForgetNotInjective :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  coherentWeightInterferenceLaw :=
    coherentTwoPathWeight_eq_incoherent_plus_interference
  zeroInterferenceIsIncoherent :=
    coherentTwoPathWeight_zero_interference
  constructiveInterferenceCanary :=
    constructiveInterference_differs_from_incoherent
  destructiveInterferenceCanary :=
    destructiveInterference_differs_from_incoherent
  phaseFactorIsExponential :=
    complexPhaseFactor_eq_exp_mul_I
  complexAmplitudeIsExponential :=
    complexAmplitude_eq_real_mul_exp_mul_I
  complexPhaseFactorUnitWeight :=
    complexPhaseFactor_normSq
  complexAmplitudeBornWeight :=
    complexAmplitude_normSq
  complexHellingerBornWeight := by
    intro p θ hp
    exact complexHellingerAmplitude_normSq hp
  complexTwoPathInterferenceLaw :=
    complexTwoPathBornWeight_interference
  complexTwoPathReducesToCoherentWeight :=
    complexTwoPathBornWeight_eq_coherentWeight
  complexConstructiveInterference :=
    complexTwoPath_constructive_at_equal_phase
  complexDestructiveInterference :=
    complexTwoPath_destructive_at_pi
  ksComplexCarrierEquivComplex :=
    ksComplexPhaseCarrierEquivComplex
  ksComplexCarrierPositiveDefinite :=
    ksComplexPhaseCarrier_positiveDefinite
  dualCarrierFailsPositiveDefinite :=
    dualCarrier_not_positiveDefinite
  splitCarrierFailsPositiveDefinite :=
    splitCarrier_not_positiveDefinite

/-- Typed ITV operation profile: operations either require same semantics or
an explicit bridge to a shared target semantics. -/
structure TypedITVOperationProfile where
  sameSemanticsConjunction :
    ∀ {Sem : ITVSemantics.{0}} (x y : TypedITV Sem),
      (TypedITV.conjunctionSameSemantics x y).value =
        ITV.conjunction x.value y.value
  sameSemanticsImplication :
    ∀ {Sem : ITVSemantics.{0}} (x y : TypedITV Sem),
      (TypedITV.implicationSameSemantics x y).value =
        ITV.implication x.value y.value
  forgetToGenericPreservesValue :
    ∀ {Sem : ITVSemantics.{0}} (x : TypedITV Sem),
      (TypedITV.forgetToGeneric x).value = x.value
  crossSemanticsConjunctionViaBridge :
    ∀ {Sem₁ Sem₂ Target : ITVSemantics.{0}}
      (B : TypedITV.Bridge Sem₁ Sem₂ Target)
      (x : TypedITV Sem₁) (y : TypedITV Sem₂),
      (TypedITV.conjunctionViaBridge B x y).value =
        ITV.conjunction (B.left x).value (B.right y).value

/-- Typed operation profile: no silent cross-semantics mixing. -/
def typedITVOperationProfile : TypedITVOperationProfile where
  sameSemanticsConjunction :=
    typed_itv_same_semantics_conjunction_raw_value
  sameSemanticsImplication :=
    typed_itv_same_semantics_implication_raw_value
  forgetToGenericPreservesValue :=
    typed_itv_forget_to_generic_preserves_raw_value
  crossSemanticsConjunctionViaBridge :=
    typed_itv_cross_semantics_conjunction_via_bridge_raw_value

/-- World-model typed ITV profile: the world model extracts evidence as the
load-bearing state, typed ITV queries retain constructor provenance, and the
old raw query functions are exactly the forgetful projections. -/
structure WorldModelTypedITVProfile where
  binaryForgetsToRaw :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).value =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITV
          (State := State) (Query := Query) sem ctx W q
  binaryTypedLowerIsRawLower :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).lower =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVLower
          (State := State) (Query := Query) sem ctx W q
  binaryTypedUpperIsRawUpper :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).upper =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVUpper
          (State := State) (Query := Query) sem ctx W q
  binaryTypedStrengthIsRawStrength :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).midpoint =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVStrength
          (State := State) (Query := Query) sem ctx W q
  binaryTypedWidthIsRawWidth :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).width =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVWidth
          (State := State) (Query := Query) sem ctx W q
  binaryTypedCredibilityIsRawCredibility :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).credibility =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryITVCredibility
          (State := State) (Query := Query) sem ctx W q
  binaryTypedJudgmentForgetsToRaw :
    ∀ {State Query Ctx : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {W : State} {q : Query}
      {itv : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics.toTruthTowerSemantics sem ctx)},
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.WMTypedITVJudgment
        (State := State) (Query := Query) sem ctx W q itv →
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.WMITVJudgment
        (State := State) (Query := Query) sem ctx W q itv.value
  binaryWalleyWidthComplement :
    ∀ {State Query : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (ctx : Mettapedia.PLN.WorldModel.PLNWorldModel.IDMPredictiveContext)
      (W : State) (q : Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley
          (State := State) (Query := Query) ctx W q).width +
        (Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley
          (State := State) (Query := Query) ctx W q).credibility = 1
  sigmaForgetsToRaw :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedAtForgetsToRawAt :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) {s : Srt} (q : Query s),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITVAt
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVAt
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedLowerIsRawLower :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).lower =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVLower
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedUpperIsRawUpper :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).upper =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVUpper
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedStrengthIsRawStrength :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).midpoint =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVStrength
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedWidthIsRawWidth :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).width =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVWidth
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedCredibilityIsRawCredibility :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).credibility =
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryITVCredibility
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedJudgmentForgetsToRaw :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {W : State} {q : Sigma Query}
      {itv : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics.toTruthTowerSemantics sem ctx)},
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q itv →
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q itv.value
  sigmaQueryEquivalencePreservesTypedITV :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      {q₁ q₂ : Sigma Query}
      (_ : Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State),
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q₁ =
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q₂
  sigmaRewriteProducesTypedJudgment :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {r :
        Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query}
      {W : State}, r.side → Mettapedia.PLN.WorldModel.PLNWorldModel.WMJudgment W →
      Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx
        W r.conclusion
        (Mettapedia.PLN.WorldModel.PLNWorldModel.ITVSemantics.typedEval sem ctx (r.derive W))
  sigmaWalleyWidthComplement :
    ∀ {State Srt : Type} {Query : Srt → Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma State Srt Query]
      (ctx : Mettapedia.PLN.WorldModel.PLNWorldModel.IDMPredictiveContext)
      (W : State) (q : Sigma Query),
      (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITVWalley
          (State := State) (Srt := Srt) (Query := Query) ctx W q).width +
        (Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITVWalley
          (State := State) (Srt := Srt) (Query := Query) ctx W q).credibility = 1

/-- World-model ITV profile: typed provenance is now available at the query
boundary, with raw ITV queries retained only as forgetful views. -/
def worldModelTypedITVProfile : WorldModelTypedITVProfile where
  binaryForgetsToRaw :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_value_eq_queryITV
  binaryTypedLowerIsRawLower :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_lower_eq_queryITVLower
  binaryTypedUpperIsRawUpper :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_upper_eq_queryITVUpper
  binaryTypedStrengthIsRawStrength :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_strength_eq_queryITVStrength
  binaryTypedWidthIsRawWidth :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_width_eq_queryITVWidth
  binaryTypedCredibilityIsRawCredibility :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITV_credibility_eq_queryITVCredibility
  binaryTypedJudgmentForgetsToRaw :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.WMTypedITVJudgment.forget
  binaryWalleyWidthComplement :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley_width_add_credibility
  sigmaForgetsToRaw :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_value_eq_queryITV
  sigmaTypedAtForgetsToRawAt :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITVAt_value_eq_queryITVAt
  sigmaTypedLowerIsRawLower :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_lower_eq_queryITVLower
  sigmaTypedUpperIsRawUpper :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_upper_eq_queryITVUpper
  sigmaTypedStrengthIsRawStrength :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_strength_eq_queryITVStrength
  sigmaTypedWidthIsRawWidth :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_width_eq_queryITVWidth
  sigmaTypedCredibilityIsRawCredibility :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITV_credibility_eq_queryITVCredibility
  sigmaTypedJudgmentForgetsToRaw :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma.forget
  sigmaQueryEquivalencePreservesTypedITV :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryTypedITV
  sigmaRewriteProducesTypedJudgment :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma.applyTypedITV
  sigmaWalleyWidthComplement :=
    Mettapedia.PLN.WorldModel.PLNWorldModel.WorldModelSigma.queryTypedITVWalley_width_add_credibility

/-- Credal/lower-prevision profile: lower and upper projections are forced by
the retained imprecise-probability object. -/
structure CredalForcedQueryProfile where
  lowerForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₂) f
  upperForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₂) f
  envelopeForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (credal W₁) f,
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (credal W₁) f) =
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (credal W₂) f,
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (credal W₂) f)
  lowerPrevisionForced :
    ∀ {World Ω : Type}
      (prevision :
        World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      {W₁ W₂ : World}, prevision W₁ = prevision W₂ →
        prevision W₁ X = prevision W₂ X
  upperPrevisionForced :
    ∀ {World Ω : Type}
      (prevision :
        World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      {W₁ W₂ : World}, prevision W₁ = prevision W₂ →
        (prevision W₁).conjugate X = (prevision W₂).conjugate X
  desirableSetForced :
    ∀ {World Ω : Type}
      (desirable :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, desirable W₁ = desirable W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₂) f
  typedEnvelopeLowerForced :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).lower =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          src.credal src.gamble
  typedEnvelopeUpperForced :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).upper =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          src.credal src.gamble
  typedEnvelopeCredibilitySelected :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).credibility =
        src.credibility
  typedEnvelopeBoundsDoNotForceCredibility :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1),
      let x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := f
            credal_nonempty := hK
            gamble_in_unit := hf
            credibility := 0
            credibility_in_unit := by norm_num }
      let y : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := f
            credal_nonempty := hK
            gamble_in_unit := hf
            credibility := 1
            credibility_in_unit := by norm_num }
      x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility
  typedLowerPrevisionLowerForced :
    ∀ {Ω : Type}
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).lower =
        src.prevision src.gamble
  typedLowerPrevisionUpperForced :
    ∀ {Ω : Type}
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).upper =
        src.prevision.conjugate src.gamble
  typedLowerPrevisionCredibilitySelected :
    ∀ {Ω : Type}
      (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).credibility =
        src.credibility
  typedLowerPrevisionBoundsDoNotForceCredibility :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1),
      let x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
          { prevision := P
            gamble := X
            gamble_in_unit := hX
            credibility := 0
            credibility_in_unit := by norm_num }
      let y : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
          { prevision := P
            gamble := X
            gamble_in_unit := hX
            credibility := 1
            credibility_in_unit := by norm_num }
      x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility
  singletonCredalLowerPrevisionAgreement :
    ∀ {Ω : Type} [Fintype Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
      (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1),
      let lp : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
          (Mettapedia.PLN.TruthValues.PLNTruthTower.SingletonCredalLowerPrevision.source
            P X hX credibility hc);
      let ce : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
          (Mettapedia.PLN.TruthValues.PLNTruthTower.SingletonCredalLowerPrevision.credalEnvelopeSource
            P X hX credibility hc);
      lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
        lp.credibility = ce.credibility
  finiteCredalLowerPrevisionAgreement :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
      (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1),
      let lp : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
          (Mettapedia.PLN.TruthValues.PLNTruthTower.FiniteCredalLowerPrevision.source
            K hK X hX credibility hc);
      let ce : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
          (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := X
            credal_nonempty := hK
            gamble_in_unit := hX
            credibility := credibility
            credibility_in_unit := hc };
      lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
        lp.credibility = ce.credibility
  regularLowerPrevisionInducesDesirableSet :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (_hReg :
        Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  regularLowerPrevisionDesirableMembership :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (hReg :
        Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      X ∈
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
            P hReg).D ↔
        P X > 0
  finiteLowerPrevisionRegular :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P
  finiteLowerPrevisionInducesDesirableSet :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (_P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  finiteCredalLowerPrevisionDesirableMembership :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      X ∈
          (Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet
            K hK).D ↔
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K X > 0

/-- Credal/lower-prevision forced-query profile. -/
noncomputable def credalForcedQueryProfile : CredalForcedQueryProfile where
  lowerForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_lower_expectation_is_forced_by_credal_set credal f h
  upperForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_upper_expectation_is_forced_by_credal_set credal f h
  envelopeForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_envelope_is_forced_by_credal_set credal f h
  lowerPrevisionForced :=
    lower_prevision_value_is_forced_by_lower_prevision
  upperPrevisionForced :=
    upper_prevision_value_is_forced_by_lower_prevision
  desirableSetForced :=
    desirable_lower_prevision_is_forced_by_desirable_set
  typedEnvelopeLowerForced :=
    credal_envelope_typed_itv_lower_forced
  typedEnvelopeUpperForced :=
    credal_envelope_typed_itv_upper_forced
  typedEnvelopeCredibilitySelected :=
    credal_envelope_typed_itv_credibility_is_selected
  typedEnvelopeBoundsDoNotForceCredibility :=
    credal_envelope_bounds_do_not_force_confidence_coordinate
  typedLowerPrevisionLowerForced :=
    lower_prevision_typed_itv_lower_forced
  typedLowerPrevisionUpperForced :=
    lower_prevision_typed_itv_upper_forced
  typedLowerPrevisionCredibilitySelected :=
    lower_prevision_typed_itv_credibility_is_selected
  typedLowerPrevisionBoundsDoNotForceCredibility :=
    lower_prevision_bounds_do_not_force_confidence_coordinate
  singletonCredalLowerPrevisionAgreement :=
    singleton_credal_lower_prevision_itv_agrees
  finiteCredalLowerPrevisionAgreement :=
    finite_credal_lower_prevision_itv_agrees
  regularLowerPrevisionInducesDesirableSet :=
    regular_lower_prevision_induces_coherent_desirable_set
  regularLowerPrevisionDesirableMembership :=
    regular_lower_prevision_desirable_membership
  finiteLowerPrevisionRegular :=
    finite_lower_prevision_is_regular
  finiteLowerPrevisionInducesDesirableSet :=
    finite_lower_prevision_induces_coherent_desirable_set
  finiteCredalLowerPrevisionDesirableMembership := by
    intro Ω instΩ nonemptyΩ K hK X
    exact finite_credal_lower_prevision_desirable_membership K hK X

/-- Profile for the explicit credal projection tower: the credal set/query
forces lower and upper, while coordinate plus weight select displayed
confidence. -/
structure CredalProjectionTowerProfile where
  lowerForced :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.lower =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          t.credal t.gamble
  upperForced :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.upper =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          t.credal t.gamble
  credibilitySelectedByCoordinate :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.credibility = t.coordinate.encode t.weight
  confidenceDecodesWeight :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.typedConfidence.weight = t.weight
  widthComplementBridgeForcesDisplay :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω),
      t.WidthComplementBridge →
        t.credibilityDisplay = 1 - t.toTypedITV.width
  sameWeightDifferentCoordinateCanary :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1),
      let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K
          credal_nonempty := hK
          gamble := f
          gamble_in_unit := hf
          coordinate := plnOddsCoordinate 1 (by norm_num)
          coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
          weight := 1
          weight_nonneg := by norm_num }
      let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K
          credal_nonempty := hK
          gamble := f
          gamble_in_unit := hf
          coordinate := reserveHalfCoordinate 1 (by norm_num)
          coordinate_unit := reserveHalfCoordinate_encode_in_Ico 1 (by norm_num)
          weight := 1
          weight_nonneg := by norm_num }
      x.toTypedITV.lower = y.toTypedITV.lower ∧
        x.toTypedITV.upper = y.toTypedITV.upper ∧
        x.toTypedITV.credibility ≠ y.toTypedITV.credibility ∧
        x.typedConfidence.weight = y.typedConfidence.weight
  sameCoordinateWeightForcesSameConfidence :
    ∀ {Ω : Type} [Fintype Ω]
      (K₁ K₂ :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
      (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
      (w : ℝ) (hw : 0 ≤ w),
      let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₁
          credal_nonempty := hK₁
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₂
          credal_nonempty := hK₂
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      x.toTypedITV.credibility = y.toTypedITV.credibility ∧
        x.typedConfidence.weight = y.typedConfidence.weight
  sameConfidenceDifferentEnvelopeCanary :
    ∀ {Ω : Type} [Fintype Ω]
      (K₁ K₂ :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
      (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
      (w : ℝ) (hw : 0 ≤ w)
      (_hLower :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₁ f ≠
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₂ f),
      let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₁
          credal_nonempty := hK₁
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₂
          credal_nonempty := hK₂
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      x.toTypedITV.credibility = y.toTypedITV.credibility ∧
        x.typedConfidence.weight = y.typedConfidence.weight ∧
          x.toTypedITV.lower ≠ y.toTypedITV.lower
  concreteBoolSameConfidenceDifferentEnvelopeCanary :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolFalseProbDist
        credal_nonempty :=
          ⟨Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolFalseProbDist, rfl⟩
        gamble :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTrueProbDist
        credal_nonempty :=
          ⟨Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTrueProbDist, rfl⟩
        gamble :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
      x.toTypedITV.lower = 0 ∧
      y.toTypedITV.lower = 1 ∧
      x.toTypedITV.lower ≠ y.toTypedITV.lower
  distinctionObservationWidthOfRelatedNe :
    ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
      (r : Setoid Ω) {ω₀ ω₁ : Ω},
      r.r ω₁ ω₀ → ω₁ ≠ ω₀ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet r ω₀)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble ω₀) <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet r ω₀)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble ω₀)
  distinctionObservationCollapseOfSingletonClass :
    ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
      (r : Setoid Ω) (ω₀ : Ω),
      (∀ ω, r.r ω ω₀ → ω = ω₀) →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet r ω₀)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble ω₀) =
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet r ω₀)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble ω₀)
  oslfObservationWidthOfIndistinguishableNe :
    ∀ [Fintype Mettapedia.OSLF.Framework.DistinctionGraph.Pat]
      [DecidableEq Mettapedia.OSLF.Framework.DistinctionGraph.Pat]
      {R :
        Mettapedia.OSLF.Framework.DistinctionGraph.Pat →
          Mettapedia.OSLF.Framework.DistinctionGraph.Pat → Prop}
      {I : Mettapedia.OSLF.Formula.AtomSem}
      {p q : Mettapedia.OSLF.Framework.DistinctionGraph.Pat},
      Mettapedia.OSLF.Framework.DistinctionGraph.indistObs R I q p → q ≠ p →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet
              (Mettapedia.OSLF.Framework.DistinctionGraph.indistObs_setoid R I) p)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble p) <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet
              (Mettapedia.OSLF.Framework.DistinctionGraph.indistObs_setoid R I) p)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble p)
  oslfObservationCollapseOfSingletonClass :
    ∀ [Fintype Mettapedia.OSLF.Framework.DistinctionGraph.Pat]
      [DecidableEq Mettapedia.OSLF.Framework.DistinctionGraph.Pat]
      {R :
        Mettapedia.OSLF.Framework.DistinctionGraph.Pat →
          Mettapedia.OSLF.Framework.DistinctionGraph.Pat → Prop}
      {I : Mettapedia.OSLF.Formula.AtomSem}
      (p : Mettapedia.OSLF.Framework.DistinctionGraph.Pat),
      (∀ q : Mettapedia.OSLF.Framework.DistinctionGraph.Pat,
          Mettapedia.OSLF.Framework.DistinctionGraph.indistObs R I q p → q = p) →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet
              (Mettapedia.OSLF.Framework.DistinctionGraph.indistObs_setoid R I) p)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble p) =
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet
              (Mettapedia.OSLF.Framework.DistinctionGraph.indistObs_setoid R I) p)
            (Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.indicatorGamble p)

/-- Credal projection tower profile.

This packages the finite projection-forcing surface together with the generic
setoid-based distinction/credal bridge and its OSLF observational
specialization.  The concrete Bool witness remains available underneath these
fields, but the profile surfaces the generic and language-specialized theorems
directly. -/
def credalProjectionTowerProfile : CredalProjectionTowerProfile where
  lowerForced :=
    credal_projection_tower_lower_forced
  upperForced :=
    credal_projection_tower_upper_forced
  credibilitySelectedByCoordinate :=
    credal_projection_tower_credibility_selected
  confidenceDecodesWeight :=
    credal_projection_tower_confidence_decodes_weight
  widthComplementBridgeForcesDisplay :=
    credal_projection_width_complement_bridge_forces_display
  sameWeightDifferentCoordinateCanary :=
    credal_projection_same_weight_can_display_different_confidence
  sameCoordinateWeightForcesSameConfidence :=
    credal_projection_same_coordinate_weight_forces_same_confidence
  sameConfidenceDifferentEnvelopeCanary :=
    credal_projection_same_confidence_can_have_different_envelope
  concreteBoolSameConfidenceDifferentEnvelopeCanary :=
    credal_projection_bool_same_confidence_different_envelope
  distinctionObservationWidthOfRelatedNe :=
    Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
  distinctionObservationCollapseOfSingletonClass :=
    Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
  oslfObservationWidthOfIndistinguishableNe :=
    Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_has_strict_width
  oslfObservationCollapseOfSingletonClass :=
    Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_collapses_of_class_subsingleton


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
