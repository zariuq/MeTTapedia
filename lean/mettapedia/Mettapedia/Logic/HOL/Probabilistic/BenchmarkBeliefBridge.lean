import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBridge
import Mettapedia.Logic.HOL.Probabilistic.BeliefBridge

/-!
# Benchmark-to-Belief Bridge for Probabilistic HOL

This module derives a benchmark-facing LI-style belief layer from the canonical
semantic benchmark bridge.

The semantic side remains primary:

- `BenchmarkBridge.lean` interprets guarded benchmark payloads as a concrete
  hierarchical `ProbHOL` state,
- `BeliefBridge.lean` explains what it means for a belief day/process to track
  semantic probability,
- and this file constructs the benchmark's belief-side shadow without allowing
  planner-facing numbers to become the canonical semantics.

References:

- Haim Gaifman, *A Theory of Higher Order Probabilities* (1986)
- Henry E. Kyburg, *Higher Order Probabilities*
- Scott Garrabrant, Tsvi Benson-Tilsen, Andrew Critch, Nate Soares, and
  Jessica Taylor, *Logical Induction*, arXiv:1609.03543v5 (2020)
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics
open scoped ENNReal

/-- The guarded benchmark's flattened semantic value is always nonnegative when
the branch values are honest probabilities and the regime weights are valid. -/
theorem higherOrderSemanticValue_nonneg
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    0 ≤ higherOrderSemanticValue payload := by
  rcases hvalid with ⟨hweights, hexact_nonneg, _, hbounded_nonneg, _, hfallback_nonneg, _⟩
  rcases hweights with ⟨hwexact_nonneg, hwbounded_nonneg, hwfallback_nonneg, _⟩
  have hexact_term_nonneg :
      0 ≤ payload.weights.exactMass * payload.exactBranchValue := by
    nlinarith
  have hbounded_term_nonneg :
      0 ≤ payload.weights.boundedMass * payload.boundedBranchValue := by
    nlinarith
  have hfallback_term_nonneg :
      0 ≤ payload.weights.fallbackMass * payload.fallbackBranchValue := by
    nlinarith
  unfold higherOrderSemanticValue
  nlinarith

/-- The guarded benchmark's flattened semantic value stays inside the unit
interval under the validity hypotheses. -/
theorem higherOrderSemanticValue_le_one
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    higherOrderSemanticValue payload ≤ 1 := by
  rcases hvalid with
    ⟨hweights, hexact_nonneg, hexact_le_one,
      hbounded_nonneg, hbounded_le_one,
      hfallback_nonneg, hfallback_le_one⟩
  rcases hweights with ⟨hwexact_nonneg, hwbounded_nonneg, hwfallback_nonneg, hsum⟩
  have hexact_term_le :
      payload.weights.exactMass * payload.exactBranchValue ≤ payload.weights.exactMass := by
    nlinarith
  have hbounded_term_le :
      payload.weights.boundedMass * payload.boundedBranchValue ≤ payload.weights.boundedMass := by
    nlinarith
  have hfallback_term_le :
      payload.weights.fallbackMass * payload.fallbackBranchValue ≤ payload.weights.fallbackMass := by
    nlinarith
  unfold higherOrderSemanticValue
  nlinarith

/-- The benchmark hierarchy's sentence probability agrees exactly with the
guarded benchmark's carried flattened value. -/
theorem benchmarkHierarchicalSentenceProb_eq_higherOrderSemanticValue
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkHierarchicalState payload hvalid)
        benchmarkSentence =
      ENNReal.ofReal (((higherOrderSemanticValue payload : ℚ) : ℝ)) := by
  rcases hvalid with
    ⟨hweights, hexact_nonneg, _,
      hbounded_nonneg, _,
      hfallback_nonneg, _⟩
  rcases hweights with ⟨hwexact_nonneg, hwbounded_nonneg, hwfallback_nonneg, _⟩
  have hexact_nonnegR : 0 ≤ ((payload.exactBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hexact_nonneg
  have hbounded_nonnegR : 0 ≤ ((payload.boundedBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hbounded_nonneg
  have hfallback_nonnegR : 0 ≤ ((payload.fallbackBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hfallback_nonneg
  have hwexact_nonnegR : 0 ≤ ((payload.weights.exactMass : ℚ) : ℝ) := by
    exact_mod_cast hwexact_nonneg
  have hwbounded_nonnegR : 0 ≤ ((payload.weights.boundedMass : ℚ) : ℝ) := by
    exact_mod_cast hwbounded_nonneg
  have hwfallback_nonnegR : 0 ≤ ((payload.weights.fallbackMass : ℚ) : ℝ) := by
    exact_mod_cast hwfallback_nonneg
  have hexact_term_nonneg :
      0 ≤ ((payload.exactBranchValue : ℚ) : ℝ) * ((payload.weights.exactMass : ℚ) : ℝ) := by
    exact mul_nonneg hexact_nonnegR hwexact_nonnegR
  have hbounded_term_nonneg :
      0 ≤ ((payload.boundedBranchValue : ℚ) : ℝ) * ((payload.weights.boundedMass : ℚ) : ℝ) := by
    exact mul_nonneg hbounded_nonnegR hwbounded_nonnegR
  have hfallback_term_nonneg :
      0 ≤ ((payload.fallbackBranchValue : ℚ) : ℝ) * ((payload.weights.fallbackMass : ℚ) : ℝ) := by
    exact mul_nonneg hfallback_nonnegR hwfallback_nonnegR
  rw [benchmarkHierarchicalSentenceProb_eq_integral_branchMass]
  rw [MeasureTheory.lintegral_fintype]
  have huniv :
      (Finset.univ : Finset GuardRegime) =
        { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp [benchmarkMixingPMF, PMF.ofFintype, branchMass, regimeMass]
  rw [← ENNReal.ofReal_mul hexact_nonnegR,
    ← ENNReal.ofReal_mul hbounded_nonnegR,
    ← ENNReal.ofReal_mul hfallback_nonnegR]
  rw [← ENNReal.ofReal_add hbounded_term_nonneg hfallback_term_nonneg]
  rw [← ENNReal.ofReal_add hexact_term_nonneg
    (add_nonneg hbounded_term_nonneg hfallback_term_nonneg)]
  congr 1
  change
    ((payload.exactBranchValue : ℚ) : ℝ) * ((payload.weights.exactMass : ℚ) : ℝ) +
      (((payload.boundedBranchValue : ℚ) : ℝ) * ((payload.weights.boundedMass : ℚ) : ℝ) +
        ((payload.fallbackBranchValue : ℚ) : ℝ) * ((payload.weights.fallbackMass : ℚ) : ℝ)) =
      (((payload.weights.exactMass * payload.exactBranchValue +
          payload.weights.boundedMass * payload.boundedBranchValue +
          payload.weights.fallbackMass * payload.fallbackBranchValue : ℚ)) : ℝ)
  push_cast
  ring_nf

/-- The WM-facing hierarchical query strength for the benchmark sentence agrees
with the guarded benchmark's carried flattened value. -/
theorem benchmarkHierarchicalProbQueryStrength_eq_higherOrderSemanticValue
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalProbQueryStrength
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkHierarchicalState payload hvalid)
        benchmarkSentence =
      ENNReal.ofReal (((higherOrderSemanticValue payload : ℚ) : ℝ)) := by
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    benchmarkHierarchicalSentenceProb_eq_higherOrderSemanticValue]

/-- Adding explicit benchmark latent coordinates does not change the benchmark
sentence probability: the richer hierarchy still flattens to the carried
guarded semantic value. -/
theorem benchmarkLatentHierarchicalSentenceProb_eq_higherOrderSemanticValue
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalSentenceProb
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkLatentHierarchicalState profile payload hvalid)
        benchmarkSentence =
      ENNReal.ofReal (((higherOrderSemanticValue payload : ℚ) : ℝ)) := by
  rcases hvalid with
    ⟨hweights, hexact_nonneg, _,
      hbounded_nonneg, _,
      hfallback_nonneg, _⟩
  rcases hweights with ⟨hwexact_nonneg, hwbounded_nonneg, hwfallback_nonneg, _⟩
  have hexact_nonnegR : 0 ≤ ((payload.exactBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hexact_nonneg
  have hbounded_nonnegR : 0 ≤ ((payload.boundedBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hbounded_nonneg
  have hfallback_nonnegR : 0 ≤ ((payload.fallbackBranchValue : ℚ) : ℝ) := by
    exact_mod_cast hfallback_nonneg
  have hwexact_nonnegR : 0 ≤ ((payload.weights.exactMass : ℚ) : ℝ) := by
    exact_mod_cast hwexact_nonneg
  have hwbounded_nonnegR : 0 ≤ ((payload.weights.boundedMass : ℚ) : ℝ) := by
    exact_mod_cast hwbounded_nonneg
  have hwfallback_nonnegR : 0 ≤ ((payload.weights.fallbackMass : ℚ) : ℝ) := by
    exact_mod_cast hwfallback_nonneg
  have hexact_term_nonneg :
      0 ≤ ((payload.exactBranchValue : ℚ) : ℝ) * ((payload.weights.exactMass : ℚ) : ℝ) := by
    exact mul_nonneg hexact_nonnegR hwexact_nonnegR
  have hbounded_term_nonneg :
      0 ≤ ((payload.boundedBranchValue : ℚ) : ℝ) * ((payload.weights.boundedMass : ℚ) : ℝ) := by
    exact mul_nonneg hbounded_nonnegR hwbounded_nonnegR
  have hfallback_term_nonneg :
      0 ≤ ((payload.fallbackBranchValue : ℚ) : ℝ) * ((payload.weights.fallbackMass : ℚ) : ℝ) := by
    exact mul_nonneg hfallback_nonnegR hwfallback_nonnegR
  rw [benchmarkLatentHierarchicalSentenceProb_eq_integral_branchMass]
  rw [MeasureTheory.lintegral_fintype]
  have huniv :
      (Finset.univ : Finset GuardRegime) =
        { .exactAdmissible, .boundedViolation, .fallbackRequired } := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp [benchmarkMixingPMF, PMF.ofFintype, branchMass, regimeMass]
  rw [← ENNReal.ofReal_mul hexact_nonnegR,
    ← ENNReal.ofReal_mul hbounded_nonnegR,
    ← ENNReal.ofReal_mul hfallback_nonnegR]
  rw [← ENNReal.ofReal_add hbounded_term_nonneg hfallback_term_nonneg]
  rw [← ENNReal.ofReal_add hexact_term_nonneg
    (add_nonneg hbounded_term_nonneg hfallback_term_nonneg)]
  congr 1
  change
    ((payload.exactBranchValue : ℚ) : ℝ) * ((payload.weights.exactMass : ℚ) : ℝ) +
      (((payload.boundedBranchValue : ℚ) : ℝ) * ((payload.weights.boundedMass : ℚ) : ℝ) +
        ((payload.fallbackBranchValue : ℚ) : ℝ) * ((payload.weights.fallbackMass : ℚ) : ℝ)) =
      (((payload.weights.exactMass * payload.exactBranchValue +
          payload.weights.boundedMass * payload.boundedBranchValue +
          payload.weights.fallbackMass * payload.fallbackBranchValue : ℚ)) : ℝ)
  push_cast
  ring_nf

/-- WM-facing probabilistic strength for the richer benchmark latent hierarchy
also agrees with the carried guarded semantic value. -/
theorem benchmarkLatentHierarchicalProbQueryStrength_eq_higherOrderSemanticValue
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    hierarchicalProbQueryStrength
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkLatentHierarchicalState profile payload hvalid)
        benchmarkSentence =
      ENNReal.ofReal (((higherOrderSemanticValue payload : ℚ) : ℝ)) := by
  calc
    hierarchicalProbQueryStrength
        (Base := BenchmarkBase)
        (Const := BenchmarkConst)
        (benchmarkLatentHierarchicalState profile payload hvalid)
        benchmarkSentence
      =
        hierarchicalSentenceProb
          (Base := BenchmarkBase)
          (Const := BenchmarkConst)
          (benchmarkLatentHierarchicalState profile payload hvalid)
          benchmarkSentence := by
            exact hierarchicalProbQueryStrength_eq_sentenceProb
              (H := benchmarkLatentHierarchicalState profile payload hvalid)
              (φ := benchmarkSentence)
    _ = ENNReal.ofReal (((higherOrderSemanticValue payload : ℚ) : ℝ)) := by
          exact benchmarkLatentHierarchicalSentenceProb_eq_higherOrderSemanticValue
            profile payload hvalid

/-- The benchmark's guarded semantic value can be used as a unit-interval LI
price. -/
def benchmarkBeliefPrice
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) : Price01 :=
  ⟨higherOrderSemanticValue payload,
    higherOrderSemanticValue_nonneg payload hvalid,
    higherOrderSemanticValue_le_one payload hvalid⟩

@[simp] theorem benchmarkBeliefPrice_val
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ((benchmarkBeliefPrice payload hvalid : Price01) : Rat) =
      higherOrderSemanticValue payload := by
  rfl

/-- Query-focused benchmark belief day: it prices the benchmark sentence by the
semantic guarded value and leaves all other coded formulas at zero. -/
noncomputable def benchmarkBeliefDay
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDay BenchmarkConst :=
  fun φ =>
    if _hφ : φ = encodeClosedFormula benchmarkSentence then
      benchmarkBeliefPrice payload hvalid
    else
      Price01.zero

/-- Constant benchmark belief process induced by the benchmark belief day. -/
noncomputable def benchmarkBeliefProcess
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefProcess BenchmarkConst :=
  fun _ => benchmarkBeliefDay payload hvalid

@[simp] theorem benchmarkBeliefDay_apply_query
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    benchmarkBeliefDay payload hvalid (encodeClosedFormula benchmarkSentence) =
      benchmarkBeliefPrice payload hvalid := by
  simp [benchmarkBeliefDay]

theorem benchmarkBeliefDay_apply_of_ne_query
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    {φ : ClosedFormulaCode BenchmarkConst}
    (hφ : φ ≠ encodeClosedFormula benchmarkSentence) :
    benchmarkBeliefDay payload hvalid φ = Price01.zero := by
  simp [benchmarkBeliefDay, hφ]

/-- Singleton sample carrying only the benchmark query code. -/
noncomputable def benchmarkBeliefSample : Finset (ClosedFormulaCode BenchmarkConst) :=
  { encodeClosedFormula benchmarkSentence }

/-- Slightly larger sample used to witness that the benchmark belief adapter is
intentionally query-focused rather than a global pricing oracle. -/
noncomputable def benchmarkBeliefExpandedSample : Finset (ClosedFormulaCode BenchmarkConst) :=
  { encodeClosedFormula benchmarkSentence,
    encodeClosedFormula (.top : ClosedFormula BenchmarkConst) }

private theorem encodeTop_ne_encodeBenchmarkSentence :
    encodeClosedFormula (.top : ClosedFormula BenchmarkConst) ≠
      encodeClosedFormula benchmarkSentence := by
  intro h
  have h' : (.top : ClosedFormula BenchmarkConst) = benchmarkSentence := by
    simpa using congrArg decodeClosedFormula h
  simp [benchmarkSentence] at h'

/-- The benchmark belief day tracks the flattened semantic benchmark
probability on the benchmark query itself. -/
theorem benchmarkBeliefDay_tracks_benchmarkSentenceProb
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksSentenceProb
      (Const := BenchmarkConst)
      benchmarkSpace
      (benchmarkHierarchicalState payload hvalid).flattenedModelMeasure
      (benchmarkBeliefDay payload hvalid)
      benchmarkSentence := by
  unfold BeliefDayTracksSentenceProb
  rw [dayQueryStrength_eq_price, benchmarkBeliefDay_apply_query]
  rw [probQueryStrength_eq_sentenceProb
    (S := benchmarkSpace)
    (μ := (benchmarkHierarchicalState payload hvalid).flattenedModelMeasure)
    (hμ := by
      unfold HierarchicalState.flattenedModelMeasure
      infer_instance)]
  simpa [benchmarkBeliefPrice] using
    (benchmarkHierarchicalSentenceProb_eq_higherOrderSemanticValue payload hvalid).symm

/-- Hierarchical version of the preceding benchmark belief-day tracking
theorem. -/
theorem benchmarkBeliefDay_tracks_benchmarkHierarchicalProb
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksHierarchicalProb
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkSentence := by
  unfold BeliefDayTracksHierarchicalProb
  rw [dayQueryStrength_eq_price, benchmarkBeliefDay_apply_query]
  rw [benchmarkHierarchicalProbQueryStrength_eq_higherOrderSemanticValue]
  simp [benchmarkBeliefPrice]

/-- The same benchmark belief day also tracks any richer benchmark latent
hierarchy, because the explicit context/trust/topology coordinates preserve the
current query semantics. -/
theorem benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProb
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksHierarchicalProb
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkSentence := by
  unfold BeliefDayTracksHierarchicalProb
  rw [dayQueryStrength_eq_price, benchmarkBeliefDay_apply_query]
  rw [benchmarkLatentHierarchicalProbQueryStrength_eq_higherOrderSemanticValue]
  simp [benchmarkBeliefPrice]

/-- Singleton-sample flat semantic benchmark tracking. -/
theorem benchmarkBeliefDay_tracks_benchmarkSentenceProbOn
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksSentenceProbOn
      (Const := BenchmarkConst)
      benchmarkSpace
      (benchmarkHierarchicalState payload hvalid).flattenedModelMeasure
      (benchmarkBeliefDay payload hvalid)
      benchmarkBeliefSample := by
  exact (beliefDayTracksSentenceProbOn_singleton
    (Const := BenchmarkConst)
    (S := benchmarkSpace)
    (μ := (benchmarkHierarchicalState payload hvalid).flattenedModelMeasure)
    (B := benchmarkBeliefDay payload hvalid)
    (φ := benchmarkSentence)).mp
      (benchmarkBeliefDay_tracks_benchmarkSentenceProb payload hvalid)

/-- Singleton-sample hierarchical benchmark tracking. -/
theorem benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkBeliefSample := by
  exact (beliefDayTracksHierarchicalProbOn_singleton
    (Const := BenchmarkConst)
    (H := benchmarkHierarchicalState payload hvalid)
    (B := benchmarkBeliefDay payload hvalid)
    (φ := benchmarkSentence)).mp
      (benchmarkBeliefDay_tracks_benchmarkHierarchicalProb payload hvalid)

/-- Singleton-sample hierarchical tracking for the richer benchmark latent
hierarchy. -/
theorem benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProbOn
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkBeliefSample := by
  exact (beliefDayTracksHierarchicalProbOn_singleton
    (Const := BenchmarkConst)
    (H := benchmarkLatentHierarchicalState profile payload hvalid)
    (B := benchmarkBeliefDay payload hvalid)
    (φ := benchmarkSentence)).mp
      (benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProb profile payload hvalid)

/-- The benchmark belief process tracks the benchmark hierarchy from day `0`
on the singleton benchmark sample. -/
theorem benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      benchmarkBeliefSample
      (benchmarkBeliefProcess payload hvalid) := by
  refine ⟨0, ?_⟩
  intro n hn
  simpa [benchmarkBeliefProcess] using
    benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn payload hvalid

/-- The benchmark belief process also tracks any richer benchmark latent
hierarchy on the singleton benchmark sample. -/
theorem benchmarkBeliefProcess_eventuallyTracks_benchmarkLatentHierarchicalProbOn
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    BeliefProcessEventuallyTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      benchmarkBeliefSample
      (benchmarkBeliefProcess payload hvalid) := by
  refine ⟨0, ?_⟩
  intro n hn
  simpa [benchmarkBeliefProcess] using
    benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProbOn profile payload hvalid

/-- Negative benchmark canary: the benchmark belief adapter is intentionally
query-focused, so it does not track the benchmark hierarchy on an expanded
sample that also demands correct pricing for `⊤`. -/
theorem benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ¬ BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkHierarchicalState payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkBeliefExpandedSample := by
  intro htrack
  have htop := htrack
    (φ := encodeClosedFormula (.top : ClosedFormula BenchmarkConst))
    (by simp [benchmarkBeliefExpandedSample])
  have hzero :
      dayQueryStrength
        (Const := BenchmarkConst)
        (benchmarkBeliefDay payload hvalid)
        (encodeClosedFormula (.top : ClosedFormula BenchmarkConst)) = 0 := by
    rw [dayQueryStrength_eq_price]
    simp [benchmarkBeliefDay, encodeTop_ne_encodeBenchmarkSentence]
  have hone :
      hierarchicalProbQueryStrength
        (benchmarkHierarchicalState payload hvalid)
        (.top : ClosedFormula BenchmarkConst) = 1 := by
    rw [hierarchicalProbQueryStrength_eq_sentenceProb,
      hierarchicalSentenceProb_top_eq_one]
  have hcontra : (0 : ℝ≥0∞) = 1 := by
    calc
      (0 : ℝ≥0∞) =
          dayQueryStrength
            (Const := BenchmarkConst)
            (benchmarkBeliefDay payload hvalid)
            (encodeClosedFormula (.top : ClosedFormula BenchmarkConst)) := hzero.symm
      _ =
          hierarchicalProbQueryStrength
            (benchmarkHierarchicalState payload hvalid)
            (decodeClosedFormula (encodeClosedFormula (.top : ClosedFormula BenchmarkConst))) := htop
      _ = 1 := by simpa using hone
  norm_num at hcontra

/-- Negative benchmark canary for the richer benchmark latent hierarchy:
making the latent coordinates explicit does not magically turn the
query-focused adapter into a global belief oracle. -/
theorem benchmarkBeliefDay_not_tracks_benchmarkLatentHierarchicalProbOn_with_top
    (profile : BenchmarkLatentProfile)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload) :
    ¬ BeliefDayTracksHierarchicalProbOn
      (Const := BenchmarkConst)
      (benchmarkLatentHierarchicalState profile payload hvalid)
      (benchmarkBeliefDay payload hvalid)
      benchmarkBeliefExpandedSample := by
  intro htrack
  have htop := htrack
    (φ := encodeClosedFormula (.top : ClosedFormula BenchmarkConst))
    (by simp [benchmarkBeliefExpandedSample])
  have hzero :
      dayQueryStrength
        (Const := BenchmarkConst)
        (benchmarkBeliefDay payload hvalid)
        (encodeClosedFormula (.top : ClosedFormula BenchmarkConst)) = 0 := by
    rw [dayQueryStrength_eq_price]
    simp [benchmarkBeliefDay, encodeTop_ne_encodeBenchmarkSentence]
  have hone :
      hierarchicalProbQueryStrength
        (benchmarkLatentHierarchicalState profile payload hvalid)
        (.top : ClosedFormula BenchmarkConst) = 1 := by
    rw [hierarchicalProbQueryStrength_eq_sentenceProb,
      hierarchicalSentenceProb_top_eq_one]
  have hcontra : (0 : ℝ≥0∞) = 1 := by
    calc
      (0 : ℝ≥0∞) =
          dayQueryStrength
            (Const := BenchmarkConst)
            (benchmarkBeliefDay payload hvalid)
            (encodeClosedFormula (.top : ClosedFormula BenchmarkConst)) := hzero.symm
      _ =
          hierarchicalProbQueryStrength
            (benchmarkLatentHierarchicalState profile payload hvalid)
            (decodeClosedFormula (encodeClosedFormula (.top : ClosedFormula BenchmarkConst))) := htop
      _ = 1 := by simpa using hone
  norm_num at hcontra

/-- The guarded benchmark contraction value coincides with the benchmark belief
price extracted from the semantic hierarchy.  This is the key planner-facing
identification theorem: the carried benchmark value can be consumed as a belief
price because it is already the semantically justified benchmark marginal. -/
theorem higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hvalid : ValidBenchmarkPayload01 payload)
    (sigma provenance : List String) :
    (higherOrderSemanticContraction query payload hvalid.validWeights sigma provenance).value =
      some (((benchmarkBeliefPrice payload hvalid : Price01) : Rat)) := by
  simp [higherOrderSemanticContraction, benchmarkBeliefPrice]

end Mettapedia.Logic.HOL.Probabilistic
