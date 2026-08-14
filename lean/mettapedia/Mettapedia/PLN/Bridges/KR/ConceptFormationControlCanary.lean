import Mettapedia.KR.ConceptOntology.LoopConjectureScrutability
import Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge
import Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge

/-!
# Control Canaries for Credal Concept-Formation ITVs

This module instantiates the finite/projective concept-formation ITV bridge on
the reusable FCA control benchmark.  It keeps the benchmark data in KR and only
records the PLN readout: a permissive-but-not-robust concept displays full
semantic width, while a concept absent from the permissive family displays exact
zero.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary

open Mettapedia.KR.ConceptOntology
open Mettapedia.KR.ConceptOntology.ControlExample
open Mettapedia.KR.ConceptOntology.ControlCredalExample
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
open Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
open scoped ENNReal

universe uΩ

/-- A one-observation interface whose singleton aggregate is the existing KR
control context. -/
def controlObservationEncoder :
    ObservationEncoder PUnit.{1} Animal Trait BinaryEvidence where
  observe _ q := context.evidence q.1 q.2

/-- The singleton observation packet used to present the control context through
the observation-interface API. -/
def controlObservationSample : Multiset PUnit.{1} :=
  ({PUnit.unit} : Multiset PUnit.{1})

@[simp] theorem controlObservationEncoder_aggregate
    (x : Animal) (t : Trait) :
    ObservationEncoder.aggregate controlObservationEncoder controlObservationSample x t =
      context.evidence x t := by
  simp [controlObservationEncoder, controlObservationSample, ObservationEncoder.aggregate]

@[simp] theorem controlObservationEncoder_aggregate_eq :
    ObservationEncoder.aggregate controlObservationEncoder controlObservationSample =
      context.evidence := by
  funext x t
  exact controlObservationEncoder_aggregate x t

theorem flyingFamilyConcept_mem_observationUpper :
    flyingFamilyConcept ∈
      ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample := by
  simpa [ObservationEncoder.upperConceptFamily, gateFamily,
    BinaryFcaBenchmarkContext.upperThresholdConceptFamily] using flyingFamilyConcept_mem_upper

theorem flyingFamilyConcept_not_mem_observationLower :
    flyingFamilyConcept ∉
      ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample := by
  simpa [ObservationEncoder.lowerConceptFamily, gateFamily,
    BinaryFcaBenchmarkContext.lowerThresholdConceptFamily] using flyingFamilyConcept_not_mem_lower

/-- The flying-family concept is visible under some admissible threshold gate but
not robust across all admissible gates. -/
theorem flyingFamilyConcept_observationGap :
    flyingFamilyConcept ∈
        ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample ∧
      flyingFamilyConcept ∉
        ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample :=
  ⟨flyingFamilyConcept_mem_observationUpper, flyingFamilyConcept_not_mem_observationLower⟩

/-- The untyped PLN ITV readout for a permissive-but-not-robust control concept:
the bridge honestly displays the full semantic interval. -/
theorem flyingFamilyConcept_widthComplementITV_full_readout :
    (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).lower = 0 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).upper = 1 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).width = 1 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).credibility = 0 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).strength = (1 / 2 : ℝ) :=
  conceptFormationWidthComplementITV_gap_readout
    controlObservationEncoder gateFamily controlObservationSample flyingFamilyConcept
    flyingFamilyConcept_observationGap

/-- Typed counterpart of `flyingFamilyConcept_widthComplementITV_full_readout`. -/
theorem flyingFamilyConcept_typedWidthComplementITV_full_readout :
    (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).upper = 1 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).width = 1 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).credibility = 0 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept).midpoint = (1 / 2 : ℝ) :=
  conceptFormationTypedWidthComplementITV_gap_readout
    controlObservationEncoder gateFamily controlObservationSample flyingFamilyConcept
    flyingFamilyConcept_observationGap

theorem batOnlyFlyingConcept_not_mem_observationUpper :
    batOnlyFlyingConcept ∉
      ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample := by
  simpa [ObservationEncoder.upperConceptFamily, gateFamily,
    BinaryFcaBenchmarkContext.upperThresholdConceptFamily] using batOnlyFlyingConcept_not_mem_upper

theorem batOnlyFlyingConcept_not_mem_observationLower :
    batOnlyFlyingConcept ∉
      ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample := by
  intro hLower
  exact batOnlyFlyingConcept_not_mem_observationUpper
    (ObservationEncoder.lowerConceptFamily_subset_upperConceptFamily
      controlObservationEncoder gateFamily controlObservationSample hLower)

/-- A concept outside even the permissive control family displays exact zero:
lower and upper coincide, width is zero, and credibility is one. -/
theorem batOnlyFlyingConcept_widthComplementITV_exact_zero_readout :
    (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).lower = 0 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).upper = 0 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).width = 0 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).credibility = 1 ∧
      (conceptFormationWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).strength = 0 := by
  have hUpper := batOnlyFlyingConcept_not_mem_observationUpper
  have hLower := batOnlyFlyingConcept_not_mem_observationLower
  have hNoGap :
      ¬ (batOnlyFlyingConcept ∈
            ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample ∧
          batOnlyFlyingConcept ∉
            ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample) := by
    intro hGap
    exact hUpper hGap.1
  exact ⟨by
      rw [conceptFormationWidthComplementITV_lower]
      exact if_neg hLower,
    by
      rw [conceptFormationWidthComplementITV_upper]
      exact if_neg hUpper,
    by
      rw [conceptFormationWidthComplementITV_width]
      exact if_neg hNoGap,
    by
      rw [conceptFormationWidthComplementITV_credibility]
      exact if_neg hNoGap,
    by
      rw [conceptFormationWidthComplementITV_strength]
      simp [hLower, hUpper]⟩

/-- Typed counterpart of
`batOnlyFlyingConcept_widthComplementITV_exact_zero_readout`. -/
theorem batOnlyFlyingConcept_typedWidthComplementITV_exact_zero_readout :
    (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).lower = 0 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).upper = 0 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).width = 0 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).credibility = 1 ∧
      (conceptFormationTypedWidthComplementITV controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept).midpoint = 0 := by
  have hUpper := batOnlyFlyingConcept_not_mem_observationUpper
  have hLower := batOnlyFlyingConcept_not_mem_observationLower
  have hNoGap :
      ¬ (batOnlyFlyingConcept ∈
            ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample ∧
          batOnlyFlyingConcept ∉
            ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample) := by
    intro hGap
    exact hUpper hGap.1
  exact ⟨by
      rw [conceptFormationTypedWidthComplementITV_lower]
      exact if_neg hLower,
    by
      rw [conceptFormationTypedWidthComplementITV_upper]
      exact if_neg hUpper,
    by
      rw [conceptFormationTypedWidthComplementITV_width]
      exact if_neg hNoGap,
    by
      rw [conceptFormationTypedWidthComplementITV_credibility]
      exact if_neg hNoGap,
    by
      rw [conceptFormationTypedWidthComplementITV_midpoint]
      simp [hLower, hUpper]⟩

/-- The absent control concept has no lower/upper concept-family gap. -/
theorem batOnlyFlyingConcept_observationNoGap :
    ¬ (batOnlyFlyingConcept ∈
          ObservationEncoder.upperConceptFamily controlObservationEncoder gateFamily controlObservationSample ∧
        batOnlyFlyingConcept ∉
          ObservationEncoder.lowerConceptFamily controlObservationEncoder gateFamily controlObservationSample) := by
  intro hGap
  exact batOnlyFlyingConcept_not_mem_observationUpper hGap.1

/-- The absent control concept is determined by the finite Boolean gate
projective specification. -/
theorem batOnlyFlyingConcept_gateCredalProjectiveSpec_determines :
    (gateCredalProjectiveSpec (Gate := Bool)).determinesGlobalGamble
      (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept) := by
  exact
    (ObservationEncoder.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
      controlObservationEncoder gateFamily controlObservationSample batOnlyFlyingConcept).mpr
      batOnlyFlyingConcept_observationNoGap

/-- Concrete de Finetti-adapter endpoint canary for the permissive-but-not-robust
control concept: once a de Finetti specialization is explicitly glued to the
finite Boolean gate specification, the flying-family gap supplies compatible
precise completions evaluating the same concept-formation gamble as `1` and
`0`. -/
theorem flyingFamilyConcept_deFinettiGateSpec_endpoint_completions
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Bool)) :
    ∃ P Q : PrecisePrevision Bool,
      P ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      Q ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
      P (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept) = 1 ∧
      Q (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
        controlObservationSample flyingFamilyConcept) = 0 :=
  deFinettiGateSpec_gap_has_endpoint_completions
    X μ D hSpec controlObservationEncoder gateFamily controlObservationSample
    flyingFamilyConcept flyingFamilyConcept_observationGap

/-- Concrete de Finetti-adapter exact-collapse canary for the absent control
concept: the glued finite-gate specialization determines the absent concept's
concept-formation gamble. -/
theorem batOnlyFlyingConcept_deFinettiGateSpec_determines
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Bool)) :
    D.projectiveSpec.determinesGlobalGamble
      (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept) := by
  rw [hSpec]
  exact batOnlyFlyingConcept_gateCredalProjectiveSpec_determines

/-- Every representing mixture completion of the glued de Finetti adapter reads
the absent control concept as `0`.  This is the negative counterpart to the
endpoint-completion gap canary above. -/
theorem batOnlyFlyingConcept_deFinettiMixture_completion_eq_zero
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (D : DeFinettiProjectiveCredalSpecialization X μ)
    (hSpec : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Bool))
    (M : BernoulliMixture) (hRep : Represents M X μ) :
    (D.completionOfMixture M)
      (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
        controlObservationSample batOnlyFlyingConcept) = 0 := by
  have hReadout :=
    conceptFormationWidthComplementITV_deFinettiMixtureReadout_of_determines
      X μ D hSpec M hRep controlObservationEncoder gateFamily controlObservationSample
      batOnlyFlyingConcept
      batOnlyFlyingConcept_gateCredalProjectiveSpec_determines
  exact hReadout.1.symm.trans
    batOnlyFlyingConcept_widthComplementITV_exact_zero_readout.1

/-- Compact proof-carrying handle for the concrete control canaries of the
concept-formation ITV bridge.

The profile deliberately has four fields: the permissive-but-not-robust
positive gap canary and the absent-concept exact-zero negative canary, each in
untyped and typed ITV form. -/
noncomputable abbrev flyingFamilyWidthComplementITV :=
  conceptFormationWidthComplementITV
    (Obs := PUnit.{1}) (Obj := Animal) (Attr := Trait)
    (Q := BinaryEvidence) (Gate := Bool)
    controlObservationEncoder gateFamily controlObservationSample flyingFamilyConcept

noncomputable abbrev flyingFamilyTypedWidthComplementITV :=
  conceptFormationTypedWidthComplementITV
    (Obs := PUnit.{1}) (Obj := Animal) (Attr := Trait)
    (Q := BinaryEvidence) (Gate := Bool)
    controlObservationEncoder gateFamily controlObservationSample flyingFamilyConcept

noncomputable abbrev batOnlyWidthComplementITV :=
  conceptFormationWidthComplementITV
    (Obs := PUnit.{1}) (Obj := Animal) (Attr := Trait)
    (Q := BinaryEvidence) (Gate := Bool)
    controlObservationEncoder gateFamily controlObservationSample batOnlyFlyingConcept

noncomputable abbrev batOnlyTypedWidthComplementITV :=
  conceptFormationTypedWidthComplementITV
    (Obs := PUnit.{1}) (Obj := Animal) (Attr := Trait)
    (Q := BinaryEvidence) (Gate := Bool)
    controlObservationEncoder gateFamily controlObservationSample batOnlyFlyingConcept

abbrev FlyingFamilyUntypedFullReadout : Prop :=
  flyingFamilyWidthComplementITV.lower = 0 ∧
    flyingFamilyWidthComplementITV.upper = 1 ∧
    flyingFamilyWidthComplementITV.width = 1 ∧
    flyingFamilyWidthComplementITV.credibility = 0 ∧
    flyingFamilyWidthComplementITV.strength = (1 / 2 : ℝ)

abbrev FlyingFamilyTypedFullReadout : Prop :=
  flyingFamilyTypedWidthComplementITV.lower = 0 ∧
    flyingFamilyTypedWidthComplementITV.upper = 1 ∧
    flyingFamilyTypedWidthComplementITV.width = 1 ∧
    flyingFamilyTypedWidthComplementITV.credibility = 0 ∧
    flyingFamilyTypedWidthComplementITV.midpoint = (1 / 2 : ℝ)

abbrev BatOnlyUntypedExactZeroReadout : Prop :=
  batOnlyWidthComplementITV.lower = 0 ∧
    batOnlyWidthComplementITV.upper = 0 ∧
    batOnlyWidthComplementITV.width = 0 ∧
    batOnlyWidthComplementITV.credibility = 1 ∧
    batOnlyWidthComplementITV.strength = 0

abbrev BatOnlyTypedExactZeroReadout : Prop :=
  batOnlyTypedWidthComplementITV.lower = 0 ∧
    batOnlyTypedWidthComplementITV.upper = 0 ∧
    batOnlyTypedWidthComplementITV.width = 0 ∧
    batOnlyTypedWidthComplementITV.credibility = 1 ∧
    batOnlyTypedWidthComplementITV.midpoint = 0

structure ConceptFormationControlCanaryProfile where
  untypedPermissiveNotRobustFullReadout : FlyingFamilyUntypedFullReadout
  typedPermissiveNotRobustFullReadout : FlyingFamilyTypedFullReadout
  untypedAbsentExactZeroReadout : BatOnlyUntypedExactZeroReadout
  typedAbsentExactZeroReadout : BatOnlyTypedExactZeroReadout
  deFinettiPermissiveNotRobustEndpointCompletions :
    ∀ {Ω : Type uΩ} [MeasurableSpace Ω]
      (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
      (D : DeFinettiProjectiveCredalSpecialization X μ)
      (_ : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Bool)),
      ∃ P Q : PrecisePrevision Bool,
        P ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
        Q ∈ D.projectiveSpec.projectiveLimitCredalSet ∧
        P (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
          controlObservationSample flyingFamilyConcept) = 1 ∧
        Q (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
          controlObservationSample flyingFamilyConcept) = 0
  deFinettiAbsentMixtureCompletionExactZero :
    ∀ {Ω : Type uΩ} [MeasurableSpace Ω]
      (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
      (D : DeFinettiProjectiveCredalSpecialization X μ)
      (_ : D.projectiveSpec = gateCredalProjectiveSpec (Gate := Bool))
      (M : BernoulliMixture) (_ : Represents M X μ),
      (D.completionOfMixture M)
        (ObservationEncoder.conceptFormationGamble controlObservationEncoder gateFamily
          controlObservationSample batOnlyFlyingConcept) = 0

/-- Public control-canary profile for the concept-formation ITV bridge and its
finite-gate de Finetti adapter boundary. -/
def conceptFormationControlCanaryProfile : ConceptFormationControlCanaryProfile where
  untypedPermissiveNotRobustFullReadout := by
    simpa [FlyingFamilyUntypedFullReadout, flyingFamilyWidthComplementITV] using
      flyingFamilyConcept_widthComplementITV_full_readout
  typedPermissiveNotRobustFullReadout := by
    simpa [FlyingFamilyTypedFullReadout, flyingFamilyTypedWidthComplementITV] using
      flyingFamilyConcept_typedWidthComplementITV_full_readout
  untypedAbsentExactZeroReadout := by
    simpa [BatOnlyUntypedExactZeroReadout, batOnlyWidthComplementITV] using
      batOnlyFlyingConcept_widthComplementITV_exact_zero_readout
  typedAbsentExactZeroReadout := by
    simpa [BatOnlyTypedExactZeroReadout, batOnlyTypedWidthComplementITV] using
      batOnlyFlyingConcept_typedWidthComplementITV_exact_zero_readout
  deFinettiPermissiveNotRobustEndpointCompletions := by
    intro Ω _ X μ D hSpec
    exact flyingFamilyConcept_deFinettiGateSpec_endpoint_completions X μ D hSpec
  deFinettiAbsentMixtureCompletionExactZero := by
    intro Ω _ X μ D hSpec M hRep
    exact batOnlyFlyingConcept_deFinettiMixture_completion_eq_zero X μ D hSpec M hRep

end Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary
