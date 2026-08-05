import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention

/-!
# Soft mixtures of experts

Puigcerver et al., *From Sparse to Soft Mixtures of Experts*
(arXiv:2308.00951), Equations (1)--(2), normalize one shared token-slot logit
matrix in two different directions:

* dispatch weights normalize over tokens for each slot;
* combine weights normalize over slots for each token.

This file recovers those exact-real finite semantics by reusing the established
softmax-attention algebra.  Both families have full positive support and sum
to one along their respective axes, so constant token and slot values are
preserved.  A rectangular zero-logit fixture proves that dispatch and combine
weights are not interchangeable even though they arise from the same matrix.

No theorem here identifies positive soft routing with discrete sparsity,
hardware cost, learned specialization, or the source's empirical results.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace SoftMixtureOfExperts

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Token Slot Coordinate : Type*}

/-- Equation (1): normalize one token-slot logit column over tokens. -/
def dispatchWeight [Fintype Token]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) : ℝ :=
  attentionWeight (fun candidate => logits candidate slot) token

/-- Equation (2): normalize one token-slot logit row over slots. -/
def combineWeight [Fintype Slot]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) : ℝ :=
  attentionWeight (logits token) slot

/-- Equation (1): one slot is the dispatch-weighted combination of all input
tokens. -/
def dispatchSlot [Fintype Token]
    [NormedAddCommGroup (Coordinate → ℝ)]
    [NormedSpace ℝ (Coordinate → ℝ)]
    (logits : Token → Slot → ℝ)
    (tokens : Token → Coordinate → ℝ)
    (slot : Slot) : Coordinate → ℝ :=
  softmaxAttention (fun token => logits token slot) tokens

/-- Equation (2): one output token is the combine-weighted combination of all
processed slots. -/
def combineToken [Fintype Slot]
    [NormedAddCommGroup (Coordinate → ℝ)]
    [NormedSpace ℝ (Coordinate → ℝ)]
    (logits : Token → Slot → ℝ)
    (token : Token)
    (slots : Slot → Coordinate → ℝ) : Coordinate → ℝ :=
  softmaxAttention (logits token) slots

theorem dispatchWeight_pos [Fintype Token] [Nonempty Token]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) :
    0 < dispatchWeight logits token slot :=
  attentionWeight_pos (fun candidate => logits candidate slot) token

theorem combineWeight_pos [Fintype Slot] [Nonempty Slot]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) :
    0 < combineWeight logits token slot :=
  attentionWeight_pos (logits token) slot

/-- Every slot's dispatch column is an affine weight family over tokens. -/
theorem sum_dispatchWeight_eq_one [Fintype Token] [Nonempty Token]
    (logits : Token → Slot → ℝ) (slot : Slot) :
    ∑ token, dispatchWeight logits token slot = 1 :=
  sum_attentionWeight_eq_one (fun token => logits token slot)

/-- Every token's combine row is an affine weight family over slots. -/
theorem sum_combineWeight_eq_one [Fintype Slot] [Nonempty Slot]
    (logits : Token → Slot → ℝ) (token : Token) :
    ∑ slot, combineWeight logits token slot = 1 :=
  sum_attentionWeight_eq_one (logits token)

/-- Finite logits give every input token strictly positive dispatch mass in
every slot. -/
theorem dispatchWeight_ne_zero [Fintype Token] [Nonempty Token]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) :
    dispatchWeight logits token slot ≠ 0 :=
  ne_of_gt (dispatchWeight_pos logits token slot)

/-- Finite logits give every output token strictly positive combine mass from
every slot. -/
theorem combineWeight_ne_zero [Fintype Slot] [Nonempty Slot]
    (logits : Token → Slot → ℝ) (token : Token) (slot : Slot) :
    combineWeight logits token slot ≠ 0 :=
  ne_of_gt (combineWeight_pos logits token slot)

/-- Dispatch preserves a constant token family exactly. -/
theorem dispatchSlot_const [Fintype Token] [Nonempty Token]
    [NormedAddCommGroup (Coordinate → ℝ)]
    [NormedSpace ℝ (Coordinate → ℝ)]
    (logits : Token → Slot → ℝ)
    (value : Coordinate → ℝ) (slot : Slot) :
    dispatchSlot logits (fun _ => value) slot = value :=
  softmaxAttention_const (fun token => logits token slot) value

/-- Combination preserves a constant processed-slot family exactly. -/
theorem combineToken_const [Fintype Slot] [Nonempty Slot]
    [NormedAddCommGroup (Coordinate → ℝ)]
    [NormedSpace ℝ (Coordinate → ℝ)]
    (logits : Token → Slot → ℝ)
    (token : Token) (value : Coordinate → ℝ) :
    combineToken logits token (fun _ => value) = value :=
  softmaxAttention_const (logits token) value

/-! ## Rectangular normalization boundary -/

def zeroRectangularLogits : Fin 2 → Fin 3 → ℝ :=
  fun _token _slot => 0

theorem zeroRectangular_dispatch_weight :
    dispatchWeight zeroRectangularLogits 0 0 = 1 / 2 := by
  norm_num [dispatchWeight, attentionWeight, attentionMass,
    zeroRectangularLogits]

theorem zeroRectangular_combine_weight :
    combineWeight zeroRectangularLogits 0 0 = 1 / 3 := by
  norm_num [combineWeight, attentionWeight, attentionMass,
    zeroRectangularLogits]

/-- Row and column normalizations of the same logits are not interchangeable:
with two tokens and three slots their uniform weights are `1/2` and `1/3`. -/
theorem dispatch_and_combine_normalizations_differ :
    dispatchWeight zeroRectangularLogits 0 0 ≠
      combineWeight zeroRectangularLogits 0 0 := by
  rw [zeroRectangular_dispatch_weight, zeroRectangular_combine_weight]
  norm_num

#print axioms dispatchWeight_pos
#print axioms combineWeight_pos
#print axioms sum_dispatchWeight_eq_one
#print axioms sum_combineWeight_eq_one
#print axioms dispatchSlot_const
#print axioms combineToken_const
#print axioms dispatch_and_combine_normalizations_differ

end

end SoftMixtureOfExperts

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
