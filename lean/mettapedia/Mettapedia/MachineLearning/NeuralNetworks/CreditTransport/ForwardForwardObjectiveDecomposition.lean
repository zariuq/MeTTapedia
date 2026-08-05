import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Forward-Forward objective decomposition

Gong, Li, and Abdulla, *Mono-Forward: Revisiting Forward-Forward through
Objective-Locality Decomposition* (2025, arXiv:2501.09238), separate two
choices that are coupled in the original Forward-Forward algorithm:

1. a positive-versus-negative goodness objective; and
2. layer-local parameter updates.

Their full-comparison variant contrasts the positive label against every
incorrect class.  Equations (1)--(3) observe that this objective is exactly
softmax cross-entropy over the goodness scores.  The paper also recalls that
inter-layer `L2` normalization erases positive activation scale.

This file proves both identities and their boundaries.

* Full comparison is exactly multiclass cross-entropy for any finite family
  of negative scores.
* Sampling only one of multiple negative classes does not give the same
  pointwise objective.
* `L2` normalization is invariant under positive rescaling of a nonzero
  activation, but a negative rescaling reverses direction.

The equality of objectives does not imply equality of training trajectories:
detachment, normalization, parameter sharing, batching, and optimizer state
remain separate mechanisms.  Nor do these identities establish accuracy,
convergence, biological plausibility, or memory superiority.

Source artifact SHA-256:
`fe1b1bb78ff557c9d1ad64f91d608989d88f4dbfdd5da06af7228b6dcb91017b`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ForwardForwardObjectiveDecomposition

open scoped BigOperators

noncomputable section

/-! ## Full comparison is softmax cross-entropy -/

variable {Incorrect : Type*} [Fintype Incorrect]

/-- Contrast the positive goodness against every supplied negative score. -/
def fullComparisonLoss
    (positive : ℝ) (negative : Incorrect → ℝ) : ℝ :=
  Real.log (1 + ∑ index, Real.exp (negative index - positive))

/-- Multiclass cross-entropy for the positive class, written directly from
the goodness-score softmax. -/
def goodnessCrossEntropy
    (positive : ℝ) (negative : Incorrect → ℝ) : ℝ :=
  -Real.log
    (Real.exp positive /
      (Real.exp positive + ∑ index, Real.exp (negative index)))

/-- Factorization of the full-comparison partition by the positive score. -/
theorem fullComparison_partition_factorization
    (positive : ℝ) (negative : Incorrect → ℝ) :
    1 + ∑ index, Real.exp (negative index - positive) =
      (Real.exp positive + ∑ index, Real.exp (negative index)) /
        Real.exp positive := by
  calc
    1 + ∑ index, Real.exp (negative index - positive) =
        1 + ∑ index, Real.exp (negative index) / Real.exp positive := by
          apply congrArg (fun value : ℝ => 1 + value)
          apply Finset.sum_congr rfl
          intro index _
          rw [Real.exp_sub]
    _ = 1 +
          (∑ index, Real.exp (negative index)) / Real.exp positive := by
          rw [Finset.sum_div]
    _ = Real.exp positive / Real.exp positive +
          (∑ index, Real.exp (negative index)) / Real.exp positive := by
          rw [div_self (Real.exp_ne_zero positive)]
    _ = (Real.exp positive + ∑ index, Real.exp (negative index)) /
          Real.exp positive := by
          rw [add_div]

/-- Contrasting one positive score against all incorrect scores is exactly
multiclass softmax cross-entropy. -/
theorem fullComparisonLoss_eq_goodnessCrossEntropy
    (positive : ℝ) (negative : Incorrect → ℝ) :
    fullComparisonLoss positive negative =
      goodnessCrossEntropy positive negative := by
  have hdenPos :
      0 <
        Real.exp positive +
          ∑ index, Real.exp (negative index) := by
    positivity
  have hdenNe :
      Real.exp positive + ∑ index, Real.exp (negative index) ≠ 0 :=
    ne_of_gt hdenPos
  rw [fullComparisonLoss, goodnessCrossEntropy,
    fullComparison_partition_factorization]
  rw [Real.log_div hdenNe (Real.exp_ne_zero positive)]
  rw [Real.log_div (Real.exp_ne_zero positive) hdenNe]
  rw [Real.log_exp]
  ring

/-- The one-negative logistic comparison used by a sampled-negative update. -/
def singleNegativeLoss (positive negative : ℝ) : ℝ :=
  Real.log (1 + Real.exp (negative - positive))

/-- With two equal negative classes, using only one sampled negative is not
the full multiclass objective. -/
theorem oneSampledNegative_ne_fullComparison :
    let negatives : Bool → ℝ := fun _ => 0
    singleNegativeLoss 0 (negatives false) ≠
      fullComparisonLoss 0 negatives := by
  dsimp
  have hlog : Real.log 2 ≠ Real.log 3 := by
    intro h
    have hexp := congrArg Real.exp h
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hexp
    norm_num at hexp
  norm_num [singleNegativeLoss, fullComparisonLoss]
  exact hlog

/-! ## Inter-layer normalization erases only positive scale -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Totalized `L2` normalization.  The zero vector is mapped to itself. -/
def l2Normalize (activation : E) : E :=
  ‖activation‖⁻¹ • activation

/-- Positive rescaling of a nonzero activation is erased exactly. -/
theorem l2Normalize_pos_smul
    (scale : ℝ) (activation : E)
    (hscale : 0 < scale)
    (hactivation : activation ≠ 0) :
    l2Normalize (scale • activation) =
      l2Normalize activation := by
  have hscaleNe : scale ≠ 0 := ne_of_gt hscale
  have hnormNe : ‖activation‖ ≠ 0 := norm_ne_zero_iff.mpr hactivation
  simp only [l2Normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
  rw [smul_smul]
  congr 1
  field_simp

/-- The zero activation remains zero under normalization and any rescaling. -/
theorem l2Normalize_smul_zero
    (scale : ℝ) :
    l2Normalize (scale • (0 : E)) = l2Normalize 0 := by
  simp [l2Normalize]

/-- Positive scale erasure therefore holds for every activation, including
zero. -/
theorem l2Normalize_pos_smul_all
    (scale : ℝ) (activation : E)
    (hscale : 0 < scale) :
    l2Normalize (scale • activation) =
      l2Normalize activation := by
  by_cases hactivation : activation = 0
  · subst activation
    exact l2Normalize_smul_zero scale
  · exact l2Normalize_pos_smul scale activation hscale hactivation

/-- Negative scale is not erased: in one dimension it reverses the normalized
direction. -/
theorem l2Normalize_negativeScale_not_invariant :
    l2Normalize ((-1 : ℝ) • (1 : ℝ)) ≠
      l2Normalize (1 : ℝ) := by
  norm_num [l2Normalize, Real.norm_eq_abs]

/-- Removing normalization leaves scale visible, so the identity is specific
to the normalization mechanism rather than the goodness objective. -/
theorem raw_positiveScale_changes_activation :
    (2 : ℝ) • (1 : ℝ) ≠ (1 : ℝ) := by
  norm_num

end

end ForwardForwardObjectiveDecomposition

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
