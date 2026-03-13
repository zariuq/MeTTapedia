import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mettapedia.Logic.HOL.Probabilistic.Flattening
import Mettapedia.Logic.PLNGuardedHigherOrderSemantics

/-!
# Benchmark Bridge for Hierarchical Probabilistic HOL

This module interprets the existing guarded higher-order benchmark payloads as a
concrete hierarchical `ProbHOL` instance.

The design follows the semantic higher-order probability line of:

- Henry E. Kyburg, *Higher Order Probabilities*
- Haim Gaifman, *A Theory of Higher Order Probabilities* (1986)
- David Atkinson and Jeanne Peijnenburg,
  *A Consistent Set of Infinite-Order Probabilities* (2013)

and keeps faith with the higher-order calibration perspective of:

- Gustaf Ahdritz, Aravind Gollakota, Parikshit Gopalan,
  Charlotte Peale, and Udi Wieder,
  *Provable Uncertainty Decomposition via Higher-Order Calibration* (2025)

The current bridge realizes the existing three-way admissibility regime payload
as a first concrete hierarchical layer. This is the semantic seed for the wider
Pathfinder-style hierarchy over hidden context, admissibility, trust, and
topology; those additional coordinates are intentionally left as later
refinements instead of being introduced half-formed here.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.HOL.Probabilistic.ModelSpace
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open scoped ENNReal ProbabilityTheory

universe u

abbrev BenchmarkBase := PUnit

inductive BenchmarkConst : Ty BenchmarkBase → Type
  | query : BenchmarkConst .prop
deriving DecidableEq, Repr

/-- Benchmark-side hidden-context status carried as an explicit latent
coordinate.  The current benchmark bridge is still query-focused, but making
this coordinate first-class now keeps later Pathfinder/Hailfinder refinements
from having to smuggle context back in through ad hoc payload fields. -/
inductive BenchmarkContextStatus where
  | contextMissing
  | contextComplete
  deriving DecidableEq, Repr, Fintype

/-- Benchmark-side trust/calibration regime carried as an explicit latent
coordinate. -/
inductive BenchmarkTrustRegime where
  | skeptical
  | baseline
  | confident
  deriving DecidableEq, Repr, Fintype

/-- Benchmark-side topology class carried as an explicit latent coordinate. -/
inductive BenchmarkTopologyClass where
  | unspecified
  | hubDominated
  | loopyDense
  deriving DecidableEq, Repr, Fintype

/-- Non-regime latent benchmark profile.  The current semantic bridge still
recovers the existing guarded payload exactly, but the hidden context, trust,
and topology coordinates now have an explicit home instead of being left as
future prose only. -/
structure BenchmarkLatentProfile where
  contextStatus : BenchmarkContextStatus
  trustRegime : BenchmarkTrustRegime
  topologyClass : BenchmarkTopologyClass
  deriving DecidableEq, Repr, Fintype

/-- Full latent benchmark coordinate: the benchmark profile together with the
admissibility regime already present in the guarded higher-order payload. -/
structure BenchmarkLatent where
  profile : BenchmarkLatentProfile
  guardRegime : GuardRegime
  deriving DecidableEq, Repr

/-- Closed HOL formula used as the benchmark query event. -/
def benchmarkSentence : ClosedFormula BenchmarkConst :=
  .const BenchmarkConst.query

/-- Tiny standard model family in which the benchmark query is either true or
false. This gives a clean semantic target for guarded branch probabilities. -/
def benchmarkModel (b : Bool) : HenkinModel BenchmarkBase BenchmarkConst :=
  HenkinModel.standard
    (Carrier := fun _ => PUnit)
    (constDen := by
      intro τ c
      cases c with
      | query => exact ULift.up (b = true))

@[simp] theorem benchmarkModel_models_query_iff (b : Bool) :
    holSatisfies (benchmarkModel b) benchmarkSentence ↔ b = true := by
  change (ULift.up (b = true)).down ↔ b = true
  simp

/-- Discrete two-point model space for the benchmark bridge. -/
noncomputable def benchmarkSpace : ModelSpace BenchmarkBase BenchmarkConst where
  Idx := Bool
  instMeasurableSpace := inferInstance
  model := benchmarkModel
  measurable_sentence_event := by
    intro φ
    trivial

@[simp] theorem benchmarkSpace_sentenceEvent_query :
    (benchmarkSpace.sentenceEvent benchmarkSentence : Set Bool) = ({true} : Set Bool) := by
  ext b
  cases b <;> simp [benchmarkSpace, ModelSpace.sentenceEvent, benchmarkModel_models_query_iff]

instance : Fintype GuardRegime where
  elems := { .exactAdmissible, .boundedViolation, .fallbackRequired }
  complete := by
    intro g
    cases g <;> simp

instance : MeasurableSpace GuardRegime := ⊤

instance : MeasurableSingletonClass GuardRegime := by
  infer_instance

instance : MeasurableSpace BenchmarkContextStatus := ⊤
instance : MeasurableSingletonClass BenchmarkContextStatus := by infer_instance

instance : MeasurableSpace BenchmarkTrustRegime := ⊤
instance : MeasurableSingletonClass BenchmarkTrustRegime := by infer_instance

instance : MeasurableSpace BenchmarkTopologyClass := ⊤
instance : MeasurableSingletonClass BenchmarkTopologyClass := by infer_instance

instance : MeasurableSpace BenchmarkLatentProfile := ⊤
instance : MeasurableSingletonClass BenchmarkLatentProfile := by infer_instance

instance : MeasurableSpace BenchmarkLatent := ⊤
instance : MeasurableSingletonClass BenchmarkLatent := by infer_instance

instance : Fintype BenchmarkLatent :=
  Fintype.ofEquiv (BenchmarkLatentProfile × GuardRegime)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun θ => (θ.profile, θ.guardRegime)
      left_inv := by intro x; cases x; rfl
      right_inv := by intro θ; cases θ; rfl }

/-- Default latent benchmark profile used when the current compact guarded
payload is viewed as one slice of a richer Pathfinder/Hailfinder-style
hierarchy.  The semantic value is unchanged; the extra coordinates simply
become explicit and theorem-visible. -/
def defaultBenchmarkLatentProfile : BenchmarkLatentProfile where
  contextStatus := .contextMissing
  trustRegime := .baseline
  topologyClass := .unspecified

/-- Valid benchmark payloads are guard payloads whose branch values are honest
probabilities in `[0,1]`. -/
structure ValidBenchmarkPayload01 (payload : HigherOrderGuardPayload) : Prop where
  validWeights : ValidGuardRegimeWeights payload.weights
  exact_nonneg : 0 ≤ payload.exactBranchValue
  exact_le_one : payload.exactBranchValue ≤ 1
  bounded_nonneg : 0 ≤ payload.boundedBranchValue
  bounded_le_one : payload.boundedBranchValue ≤ 1
  fallback_nonneg : 0 ≤ payload.fallbackBranchValue
  fallback_le_one : payload.fallbackBranchValue ≤ 1

/-- ENNReal mass attached to one admissibility regime. -/
def regimeMass (weights : GuardRegimeWeights) : GuardRegime → ℝ≥0∞
  | .exactAdmissible => ENNReal.ofReal weights.exactMass
  | .boundedViolation => ENNReal.ofReal weights.boundedMass
  | .fallbackRequired => ENNReal.ofReal weights.fallbackMass

private theorem sum_regimeMass_eq_one
    (weights : GuardRegimeWeights)
    (hweights : ValidGuardRegimeWeights weights) :
    ∑ g : GuardRegime, regimeMass weights g = 1 := by
  rcases hweights with ⟨hexact, hbounded, hfallback, hsum⟩
  have huniv :
      (Finset.univ : Finset GuardRegime) =
        { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp [regimeMass]
  have hsumR : ((weights.exactMass + weights.boundedMass + weights.fallbackMass : ℚ) : ℝ) = 1 := by
    exact_mod_cast hsum
  have hexactR : (0 : ℝ) ≤ weights.exactMass := by exact_mod_cast hexact
  have hboundedR : (0 : ℝ) ≤ weights.boundedMass := by exact_mod_cast hbounded
  have hfallbackR : (0 : ℝ) ≤ weights.fallbackMass := by exact_mod_cast hfallback
  have hsumBF : (0 : ℝ) ≤ weights.boundedMass + weights.fallbackMass := by
    exact add_nonneg hboundedR hfallbackR
  calc
    ENNReal.ofReal (weights.exactMass : ℝ) +
        (ENNReal.ofReal (weights.boundedMass : ℝ) + ENNReal.ofReal (weights.fallbackMass : ℝ))
        =
          ENNReal.ofReal (weights.exactMass : ℝ) +
            ENNReal.ofReal ((weights.boundedMass : ℝ) + weights.fallbackMass) := by
              rw [← ENNReal.ofReal_add hboundedR hfallbackR]
    _ = ENNReal.ofReal ((weights.exactMass : ℝ) + ((weights.boundedMass : ℝ) + weights.fallbackMass)) := by
          rw [← ENNReal.ofReal_add hexactR hsumBF]
    _ = 1 := by
          simpa [add_assoc] using congrArg ENNReal.ofReal hsumR

/-- Finite mixing PMF induced by the benchmark's explicit regime weights. -/
noncomputable def benchmarkMixingPMF
    (weights : GuardRegimeWeights)
    (hweights : ValidGuardRegimeWeights weights) : PMF GuardRegime :=
  PMF.ofFintype (regimeMass weights) (sum_regimeMass_eq_one weights hweights)

/-- ENNReal branch probability attached to one admissibility regime. -/
def branchMass (payload : HigherOrderGuardPayload) : GuardRegime → ℝ≥0∞
  | .exactAdmissible => ENNReal.ofReal payload.exactBranchValue
  | .boundedViolation => ENNReal.ofReal payload.boundedBranchValue
  | .fallbackRequired => ENNReal.ofReal payload.fallbackBranchValue

private theorem branchMass_le_one
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (g : GuardRegime) :
    branchMass payload g ≤ 1 := by
  cases g with
  | exactAdmissible =>
      exact ENNReal.ofReal_le_one.mpr (by exact_mod_cast hvalid.exact_le_one)
  | boundedViolation =>
      exact ENNReal.ofReal_le_one.mpr (by exact_mod_cast hvalid.bounded_le_one)
  | fallbackRequired =>
      exact ENNReal.ofReal_le_one.mpr (by exact_mod_cast hvalid.fallback_le_one)

/-- Bernoulli PMF realizing one guarded benchmark branch as a truth distribution
over the benchmark query event. -/
noncomputable def branchPMF
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (g : GuardRegime) : PMF Bool :=
  PMF.ofFintype
    (fun b => cond b (branchMass payload g) (1 - branchMass payload g))
    (by simp [branchMass_le_one payload hvalid g])

@[simp] theorem branchPMF_apply_true
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (g : GuardRegime) :
    branchPMF payload hvalid g true = branchMass payload g := by
  simp [branchPMF]

@[simp] theorem branchPMF_apply_false
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (g : GuardRegime) :
    branchPMF payload hvalid g false = 1 - branchMass payload g := by
  simp [branchPMF]

/-- Kernel sending each admissibility regime to its corresponding branch
distribution over the benchmark truth event. -/
noncomputable def benchmarkKernel
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ProbabilityTheory.Kernel GuardRegime Bool :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun g => (branchPMF payload hvalid g).toMeasure)

/-- Embed an admissibility regime into the richer benchmark latent coordinate
system by fixing the non-regime benchmark profile. -/
def attachBenchmarkProfile
    (profile : BenchmarkLatentProfile) (g : GuardRegime) : BenchmarkLatent where
  profile := profile
  guardRegime := g

theorem measurable_attachBenchmarkProfile
    (profile : BenchmarkLatentProfile) :
    Measurable (attachBenchmarkProfile profile) := by
  exact Measurable.of_discrete

/-- Kernel on the richer benchmark latent coordinate system.  The current
branch distribution still depends only on the guard regime; the extra latent
coordinates are carried explicitly for later refinements. -/
noncomputable def benchmarkLatentKernel
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ProbabilityTheory.Kernel BenchmarkLatent Bool :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun θ => (branchPMF payload hvalid θ.guardRegime).toMeasure)

/-- Mixing measure on the richer latent benchmark coordinate system, obtained
by pushing the guarded-regime prior forward along the chosen latent profile. -/
noncomputable def benchmarkLatentMixingMeasure
    (profile : BenchmarkLatentProfile)
    (weights : GuardRegimeWeights)
    (hweights : ValidGuardRegimeWeights weights) :
    MeasureTheory.Measure BenchmarkLatent :=
  (benchmarkMixingPMF weights hweights).toMeasure.map (attachBenchmarkProfile profile)

/-- Concrete hierarchical state induced by the current finite guarded benchmark
payload. -/
noncomputable def benchmarkHierarchicalState
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    HierarchicalState BenchmarkBase BenchmarkConst where
  Θ := GuardRegime
  instMeasurableSpace := inferInstance
  baseSpace := benchmarkSpace
  pd := {
    kernel := benchmarkKernel payload hvalid
    kernel_isMarkov := by
      refine ⟨?_⟩
      intro g
      change MeasureTheory.IsProbabilityMeasure ((branchPMF payload hvalid g).toMeasure)
      exact PMF.toMeasure.isProbabilityMeasure _
    mixingMeasure := (benchmarkMixingPMF payload.weights hvalid.validWeights).toMeasure
    mixing_isProbability := PMF.toMeasure.isProbabilityMeasure _
  }

/-- Concrete hierarchical state over the richer latent benchmark coordinate
system.  This refines the current guarded benchmark state by carrying explicit
context, trust, and topology coordinates while preserving the same query
semantics. -/
noncomputable def benchmarkLatentHierarchicalState
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    HierarchicalState BenchmarkBase BenchmarkConst where
  Θ := BenchmarkLatent
  instMeasurableSpace := inferInstance
  baseSpace := benchmarkSpace
  pd := {
    kernel := benchmarkLatentKernel payload hvalid
    kernel_isMarkov := by
      refine ⟨?_⟩
      intro θ
      change MeasureTheory.IsProbabilityMeasure
        ((branchPMF payload hvalid θ.guardRegime).toMeasure)
      exact PMF.toMeasure.isProbabilityMeasure _
    mixingMeasure := benchmarkLatentMixingMeasure profile payload.weights hvalid.validWeights
    mixing_isProbability := by
      unfold benchmarkLatentMixingMeasure
      exact MeasureTheory.Measure.isProbabilityMeasure_map
        (measurable_attachBenchmarkProfile profile).aemeasurable
  }

/-- Each guarded branch value is realized as a semantic sentence probability in
the benchmark bridge. -/
theorem componentSentenceProb_eq_branchMass
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (g : GuardRegime) :
    (benchmarkHierarchicalState payload hvalid).componentSentenceProb g benchmarkSentence =
      branchMass payload g := by
  rw [HierarchicalState.componentSentenceProb, sentenceProb]
  change (branchPMF payload hvalid g).toMeasure ({true} : Set Bool) =
    branchMass payload g
  rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
  simp [branchPMF_apply_true]

/-- The richer latent hierarchy still realizes each branch value as the
semantic sentence probability of the benchmark query. -/
theorem latentComponentSentenceProb_eq_branchMass
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (θ : BenchmarkLatent) :
    (benchmarkLatentHierarchicalState profile payload hvalid).componentSentenceProb θ benchmarkSentence =
      branchMass payload θ.guardRegime := by
  rw [HierarchicalState.componentSentenceProb, sentenceProb]
  change (branchPMF payload hvalid θ.guardRegime).toMeasure ({true} : Set Bool) =
    branchMass payload θ.guardRegime
  rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
  simp [branchPMF_apply_true]

/-- The benchmark hierarchy answers the query by flattening to the predictive
marginal over admissibility regimes. -/
theorem benchmarkHierarchicalSentenceProb_eq_integral_branchMass
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkHierarchicalState payload hvalid)
        benchmarkSentence =
      ∫⁻ g, branchMass payload g
        ∂(benchmarkMixingPMF payload.weights hvalid.validWeights).toMeasure := by
  rw [hierarchicalSentenceProb_eq_integral_componentSentenceProb]
  congr with g
  exact componentSentenceProb_eq_branchMass payload hvalid g

/-- The richer latent hierarchy flattens to the same branch-mass integral as
the current guarded benchmark hierarchy. -/
theorem benchmarkLatentHierarchicalSentenceProb_eq_integral_branchMass
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkLatentHierarchicalState profile payload hvalid)
        benchmarkSentence =
      ∫⁻ g, branchMass payload g
        ∂(benchmarkMixingPMF payload.weights hvalid.validWeights).toMeasure := by
  rw [hierarchicalSentenceProb_eq_integral_componentSentenceProb]
  calc
    ∫⁻ θ, (benchmarkLatentHierarchicalState profile payload hvalid).componentSentenceProb θ benchmarkSentence
        ∂benchmarkLatentMixingMeasure profile payload.weights hvalid.validWeights
      =
        ∫⁻ θ : BenchmarkLatent, branchMass payload θ.guardRegime
          ∂benchmarkLatentMixingMeasure profile payload.weights hvalid.validWeights := by
            congr with θ
            exact latentComponentSentenceProb_eq_branchMass profile payload hvalid θ
    _ =
        ∫⁻ g : GuardRegime, branchMass payload g
          ∂(benchmarkMixingPMF payload.weights hvalid.validWeights).toMeasure := by
            simpa [benchmarkLatentMixingMeasure, attachBenchmarkProfile] using
              (MeasureTheory.lintegral_map
                (μ := (benchmarkMixingPMF payload.weights hvalid.validWeights).toMeasure)
                (f := fun θ : BenchmarkLatent => branchMass payload θ.guardRegime)
                (g := attachBenchmarkProfile profile)
                (hf := Measurable.of_discrete)
                (hg := measurable_attachBenchmarkProfile profile))

/-- Adding explicit context/trust/topology coordinates does not change the
current benchmark query probability. -/
theorem benchmarkLatentHierarchicalSentenceProb_eq_benchmarkHierarchicalSentenceProb
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkLatentHierarchicalState profile payload hvalid)
        benchmarkSentence =
      hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkHierarchicalState payload hvalid)
        benchmarkSentence := by
  rw [benchmarkLatentHierarchicalSentenceProb_eq_integral_branchMass,
    benchmarkHierarchicalSentenceProb_eq_integral_branchMass]

end Mettapedia.Logic.HOL.Probabilistic
