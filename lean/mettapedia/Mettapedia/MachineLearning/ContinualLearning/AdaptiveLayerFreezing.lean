import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention
import Mathlib.Tactic

/-!
# Compute-budgeted adaptive layer freezing and replay

Seo, Koh, and Choi, *Budgeted Online Continual Learning by Adaptive Layer
Freezing and Frequency-based Sampling* (ICLR 2025, arXiv:2410.15143),
compare prefix-freezing policies through information gained per computation.
Their Equations (1)--(4) divide the Fisher-trace proxy remaining in unfrozen
layers by forward cost plus the remaining backward cost.  Equation (5)
subtracts the current batch's lost Fisher trace from the information expected
from the backward computation saved by freezing.

This file isolates the finite algebra behind that criterion.  The marginal
change from freezing one additional layer is exactly

`anticipatedRate * backwardCost - batchInformation`.

Consequently, extending a frozen prefix is beneficial precisely when that
layer's batch information is below the declared exchange rate times its
backward cost.  A two-layer fixture proves the source's motivation for the
batch criterion: the globally best information-per-compute prefix can be
strictly harmful on a particular batch.

Equations (6)--(8) motivate a second boundary.  Softmax retrieval of negative
effective-use frequency is normalized and, at positive temperature, strictly
prefers the lower effective-use score.  But cosine similarities may be
negative, so an effective-use score need not itself be a nonnegative
frequency.  Zero temperature also destroys the intended ordering by producing
equal logits under exact-real field semantics.

The Fisher trace is treated as a declared proxy.  These theorems do not prove
that it equals future knowledge, that a saved FLOP can always be reinvested at
the anticipated rate, or that the paper's empirical accuracy and run-time
comparisons hold for another implementation.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace AdaptiveLayerFreezing

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

/-! ## Equations (1)--(5): prefix freezing under a compute budget -/

/-- Sum of the first `count` entries of a layer-indexed quantity. -/
def prefixSum (value : ℕ → ℝ) (count : ℕ) : ℝ :=
  ∑ layer ∈ Finset.range count, value layer

/-- Sum over the half-open layer interval `[first, stop)`. -/
def intervalSum (value : ℕ → ℝ) (first stop : ℕ) : ℝ :=
  ∑ layer ∈ Finset.Ico first stop, value layer

/-- Equation (2): information retained in the unfrozen suffix. -/
def informationPerMinibatch
    (globalInformation : ℕ → ℝ) (layerCount frozenPrefix : ℕ) : ℝ :=
  intervalSum globalInformation frozenPrefix layerCount

/-- Equation (3)'s denominator: every layer pays forward cost, while only the
unfrozen suffix pays backward cost. -/
def minibatchCost
    (forwardCost backwardCost : ℕ → ℝ)
    (layerCount frozenPrefix : ℕ) : ℝ :=
  prefixSum forwardCost layerCount +
    intervalSum backwardCost frozenPrefix layerCount

/-- Equation (3): mini-batches available per unit computation. -/
def minibatchesPerCompute
    (forwardCost backwardCost : ℕ → ℝ)
    (layerCount frozenPrefix : ℕ) : ℝ :=
  1 / minibatchCost forwardCost backwardCost layerCount frozenPrefix

/-- Equation (4): the source's global Fisher-trace information-per-compute
proxy for one frozen prefix. -/
def informationPerCompute
    (globalInformation forwardCost backwardCost : ℕ → ℝ)
    (layerCount frozenPrefix : ℕ) : ℝ :=
  informationPerMinibatch globalInformation layerCount frozenPrefix /
    minibatchCost forwardCost backwardCost layerCount frozenPrefix

/-- Equation (1) holds exactly for the finite definitions above. -/
theorem informationPerCompute_factorization
    (globalInformation forwardCost backwardCost : ℕ → ℝ)
    (layerCount frozenPrefix : ℕ) :
    informationPerCompute globalInformation forwardCost backwardCost
        layerCount frozenPrefix =
      informationPerMinibatch globalInformation layerCount frozenPrefix *
        minibatchesPerCompute forwardCost backwardCost
          layerCount frozenPrefix := by
  simp [informationPerCompute, minibatchesPerCompute, div_eq_mul_inv]

/-- Backward computation avoided by freezing a prefix. -/
def savedBackwardCost
    (backwardCost : ℕ → ℝ) (frozenPrefix : ℕ) : ℝ :=
  prefixSum backwardCost frozenPrefix

/-- Current-batch Fisher-trace proxy lost by freezing a prefix. -/
def batchInformationLost
    (batchInformation : ℕ → ℝ) (frozenPrefix : ℕ) : ℝ :=
  prefixSum batchInformation frozenPrefix

/-- Equation (5), parameterized by the anticipated information-per-compute
rate.  The source instantiates this with the maximum of Equation (4) over its
finite candidate prefixes. -/
def batchFreezingCriterion
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ)
    (frozenPrefix : ℕ) : ℝ :=
  anticipatedRate * savedBackwardCost backwardCost frozenPrefix -
    batchInformationLost batchInformation frozenPrefix

@[simp] theorem prefixSum_zero (value : ℕ → ℝ) :
    prefixSum value 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ (value : ℕ → ℝ) (count : ℕ) :
    prefixSum value (count + 1) =
      prefixSum value count + value count := by
  simp [prefixSum, Finset.sum_range_succ]

@[simp] theorem batchFreezingCriterion_zero
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ) :
    batchFreezingCriterion anticipatedRate backwardCost batchInformation 0 =
      0 := by
  simp [batchFreezingCriterion, savedBackwardCost, batchInformationLost]

/-- Adding one layer to the frozen prefix has an exact local exchange value. -/
theorem batchFreezingCriterion_succ
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ)
    (frozenPrefix : ℕ) :
    batchFreezingCriterion anticipatedRate backwardCost batchInformation
        (frozenPrefix + 1) =
      batchFreezingCriterion anticipatedRate backwardCost batchInformation
          frozenPrefix +
        (anticipatedRate * backwardCost frozenPrefix -
          batchInformation frozenPrefix) := by
  simp [batchFreezingCriterion, savedBackwardCost, batchInformationLost,
    prefixSum_succ]
  ring

/-- The exact layer-local threshold for extending the frozen prefix. -/
theorem batchFreezingCriterion_le_succ_iff
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ)
    (frozenPrefix : ℕ) :
    batchFreezingCriterion anticipatedRate backwardCost batchInformation
          frozenPrefix ≤
        batchFreezingCriterion anticipatedRate backwardCost batchInformation
          (frozenPrefix + 1) ↔
      batchInformation frozenPrefix ≤
        anticipatedRate * backwardCost frozenPrefix := by
  rw [batchFreezingCriterion_succ]
  constructor <;> intro inequality <;> linarith

/-- Strict improvement has the corresponding strict per-layer threshold. -/
theorem batchFreezingCriterion_lt_succ_iff
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ)
    (frozenPrefix : ℕ) :
    batchFreezingCriterion anticipatedRate backwardCost batchInformation
          frozenPrefix <
        batchFreezingCriterion anticipatedRate backwardCost batchInformation
          (frozenPrefix + 1) ↔
      batchInformation frozenPrefix <
        anticipatedRate * backwardCost frozenPrefix := by
  rw [batchFreezingCriterion_succ]
  constructor <;> intro inequality <;> linarith

/-- If every frozen layer satisfies the local exchange threshold, the entire
prefix has nonnegative batch freezing criterion. -/
theorem batchFreezingCriterion_nonnegative_of_layerwise
    (anticipatedRate : ℝ)
    (backwardCost batchInformation : ℕ → ℝ)
    (frozenPrefix : ℕ)
    (layerwise :
      ∀ layer < frozenPrefix,
        batchInformation layer ≤ anticipatedRate * backwardCost layer) :
    0 ≤ batchFreezingCriterion anticipatedRate backwardCost batchInformation
      frozenPrefix := by
  induction frozenPrefix with
  | zero =>
      simp
  | succ frozenPrefix inductionHypothesis =>
      rw [batchFreezingCriterion_succ]
      have previous :
          0 ≤ batchFreezingCriterion anticipatedRate backwardCost
            batchInformation frozenPrefix :=
        inductionHypothesis (fun layer layer_lt =>
          layerwise layer (Nat.lt_trans layer_lt (Nat.lt_succ_self _)))
      have current :
          batchInformation frozenPrefix ≤
            anticipatedRate * backwardCost frozenPrefix :=
        layerwise frozenPrefix (Nat.lt_succ_self _)
      linarith

/-! ### A global-versus-current-batch separation fixture -/

def twoLayerGlobalInformation : ℕ → ℝ
  | 0 => 1
  | 1 => 100
  | _ => 0

def twoLayerForwardCost : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | _ => 0

def twoLayerBackwardCost : ℕ → ℝ
  | 0 => 100
  | 1 => 1
  | _ => 0

def shiftedBatchInformation : ℕ → ℝ
  | 0 => 4000
  | 1 => 0
  | _ => 0

/-- Under the global Fisher/cost proxy, freezing the first layer strictly
beats both freezing none and freezing both. -/
theorem twoLayer_global_rate_prefers_freeze_first :
    informationPerCompute twoLayerGlobalInformation twoLayerForwardCost
          twoLayerBackwardCost 2 0 <
        informationPerCompute twoLayerGlobalInformation twoLayerForwardCost
          twoLayerBackwardCost 2 1 ∧
      informationPerCompute twoLayerGlobalInformation twoLayerForwardCost
          twoLayerBackwardCost 2 2 <
        informationPerCompute twoLayerGlobalInformation twoLayerForwardCost
          twoLayerBackwardCost 2 1 := by
  norm_num [informationPerCompute, informationPerMinibatch, minibatchCost,
    intervalSum, prefixSum, twoLayerGlobalInformation, twoLayerForwardCost,
    twoLayerBackwardCost, Finset.sum_range_succ]

/-- Nevertheless, the same globally preferred rate rejects that prefix on a
batch whose information is concentrated in the first layer.  This is a
finite counterexample to replacing Equation (5) by the global ratio alone. -/
theorem global_best_prefix_can_have_negative_batch_criterion :
    batchFreezingCriterion
        (informationPerCompute twoLayerGlobalInformation twoLayerForwardCost
          twoLayerBackwardCost 2 1)
        twoLayerBackwardCost shiftedBatchInformation 1 < 0 := by
  norm_num [batchFreezingCriterion, savedBackwardCost,
    batchInformationLost, informationPerCompute, informationPerMinibatch,
    minibatchCost, intervalSum, prefixSum, twoLayerGlobalInformation,
    twoLayerForwardCost, twoLayerBackwardCost, shiftedBatchInformation,
    Finset.sum_range_succ]

/-! ## Equations (6)--(8): similarity-aware replay -/

/-- Discounted use frequency after `age` unobserved iterations. -/
def discountedUseFrequency
    (useCount decay : ℝ) (age : ℕ) : ℝ :=
  useCount * decay ^ age

theorem discountedUseFrequency_succ
    (useCount decay : ℝ) (age : ℕ) :
    discountedUseFrequency useCount decay (age + 1) =
      decay * discountedUseFrequency useCount decay age := by
  simp [discountedUseFrequency, pow_succ]
  ring

/-- Equation (7): own discounted use plus similarity-weighted class totals. -/
def effectiveUseFrequency
    {Class : Type*} [Fintype Class]
    (own : ℝ) (similarity classTotal : Class → ℝ) : ℝ :=
  own + ∑ label, similarity label * classTotal label

/-- Equation (8)'s negative-frequency logit. -/
def retrievalLogit
    {Sample : Type*}
    (temperature : ℝ) (effectiveUse : Sample → ℝ) (sample : Sample) : ℝ :=
  -effectiveUse sample / temperature

/-- Equation (8), reusing the exact finite softmax semantics. -/
def retrievalProbability
    {Sample : Type*} [Fintype Sample]
    (temperature : ℝ) (effectiveUse : Sample → ℝ) (sample : Sample) : ℝ :=
  attentionWeight (retrievalLogit temperature effectiveUse) sample

theorem sum_retrievalProbability_eq_one
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (temperature : ℝ) (effectiveUse : Sample → ℝ) :
    ∑ sample, retrievalProbability temperature effectiveUse sample = 1 :=
  sum_attentionWeight_eq_one
    (retrievalLogit temperature effectiveUse)

/-- At positive temperature, lower effective use receives strictly greater
retrieval probability. -/
theorem retrievalProbability_gt_of_effectiveUse_lt
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (temperature : ℝ) (effectiveUse : Sample → ℝ)
    (first second : Sample)
    (temperature_pos : 0 < temperature)
    (effective_lt : effectiveUse first < effectiveUse second) :
    retrievalProbability temperature effectiveUse second <
      retrievalProbability temperature effectiveUse first := by
  have logit_lt :
      retrievalLogit temperature effectiveUse second <
        retrievalLogit temperature effectiveUse first := by
    apply (div_lt_div_iff₀ temperature_pos temperature_pos).2
    exact mul_lt_mul_of_pos_right (neg_lt_neg effective_lt) temperature_pos
  have exp_lt :
      Real.exp (retrievalLogit temperature effectiveUse second) <
        Real.exp (retrievalLogit temperature effectiveUse first) :=
    Real.exp_lt_exp.mpr logit_lt
  have mass_pos :
      0 < attentionMass (retrievalLogit temperature effectiveUse) :=
    attentionMass_pos _
  unfold retrievalProbability attentionWeight
  exact (div_lt_div_iff₀ mass_pos mass_pos).2
    (mul_lt_mul_of_pos_right exp_lt mass_pos)

/-- The strict positive-temperature premise is load-bearing: exact-real
division by zero maps every retrieval logit to zero, erasing the ordering. -/
theorem zero_temperature_erases_effectiveUse_order
    {Sample : Type*} [Fintype Sample]
    (effectiveUse : Sample → ℝ) (first second : Sample) :
    retrievalProbability 0 effectiveUse first =
      retrievalProbability 0 effectiveUse second := by
  simp [retrievalProbability, retrievalLogit, attentionWeight]

/-- Even with nonnegative own and class use counts and a cosine-valid
similarity, Equation (7)'s quantity can be negative.  It is therefore a signed
retrieval score rather than a literal frequency unless extra hypotheses are
checked. -/
theorem negative_similarity_can_make_effectiveUseFrequency_negative :
    let similarity : Fin 1 → ℝ := fun _ => -1
    let classTotal : Fin 1 → ℝ := fun _ => 2
    (0 : ℝ) ≤ 0 ∧
      (∀ label, (0 : ℝ) ≤ classTotal label) ∧
      (∀ label, similarity label ∈ Set.Icc (-1 : ℝ) 1) ∧
      effectiveUseFrequency 0 similarity classTotal < 0 := by
  norm_num [effectiveUseFrequency]

#print axioms informationPerCompute_factorization
#print axioms batchFreezingCriterion_succ
#print axioms batchFreezingCriterion_le_succ_iff
#print axioms batchFreezingCriterion_lt_succ_iff
#print axioms batchFreezingCriterion_nonnegative_of_layerwise
#print axioms twoLayer_global_rate_prefers_freeze_first
#print axioms global_best_prefix_can_have_negative_batch_criterion
#print axioms discountedUseFrequency_succ
#print axioms sum_retrievalProbability_eq_one
#print axioms retrievalProbability_gt_of_effectiveUse_lt
#print axioms zero_temperature_erases_effectiveUse_order
#print axioms negative_similarity_can_make_effectiveUseFrequency_negative

end

end AdaptiveLayerFreezing

end Mettapedia.MachineLearning.ContinualLearning
