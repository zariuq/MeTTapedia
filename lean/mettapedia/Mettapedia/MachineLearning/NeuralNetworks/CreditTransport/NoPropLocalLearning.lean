import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# NoProp local-learning structure

Li, Teh, and Pascanu, *NoProp: Training Neural Networks without Full
Back-propagation or Full Forward-propagation* (CoLLAs 2025,
arXiv:2503.24322), derive a diffusion-based classifier whose transition block
at time `t` predicts the label embedding from a noised label state and the
input.  Equal-covariance Gaussian transition terms reduce to weighted local
squared errors, with weight

`SNR(t + 1) - SNR(t)`.

This file isolates the reusable algebraic and scheduling content of that
construction.

* A shared affine skip cancels exactly, so the transition discrepancy depends
  only on the block prediction error.
* A monotone SNR schedule gives nonnegative local weights, and the weights
  telescope to the endpoint SNR difference.
* Uniformly sampling one time block is unbiased only after multiplying the
  sampled local term by the number of blocks.
* Updates to genuinely disjoint block parameters commute and can be executed
  in parallel.

The locality claim is conditional.  A learned label embedding is shared by
all block losses, so changing it changes multiple local objectives at once.
A concrete two-block fixture records that boundary.  Likewise, reversing the
SNR schedule produces a negative local weight.

These results concern objective structure and update dependencies.  They do
not establish statistical consistency, diffusion convergence, task accuracy,
or a physical parallel-memory bound.

Source artifact SHA-256:
`993ff39c417d89588913e7fc71c82ff8b7893b8ebecb881778a93784bd5c0a2c`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NoPropLocalLearning

open scoped BigOperators

noncomputable section

/-! ## Equal-covariance transition terms are local -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine mean used by one diffusion transition: a predicted target
component plus a skip connection from the previous state. -/
def affineTransitionMean
    (target previous : E) (targetScale skipScale : ℝ) : E :=
  targetScale • target + skipScale • previous

/-- When the model and posterior transitions use the same skip connection,
the skip cancels from their mean discrepancy. -/
theorem affineTransitionMean_sub_affineTransitionMean
    (prediction target previous : E)
    (targetScale skipScale : ℝ) :
    affineTransitionMean prediction previous targetScale skipScale -
        affineTransitionMean target previous targetScale skipScale =
      targetScale • (prediction - target) := by
  simp only [affineTransitionMean]
  module

/-- The squared transition discrepancy is the squared local prediction error
scaled by the square of the target coefficient. -/
theorem norm_affineTransitionMean_sub_sq
    (prediction target previous : E)
    (targetScale skipScale : ℝ) :
    ‖affineTransitionMean prediction previous targetScale skipScale -
        affineTransitionMean target previous targetScale skipScale‖ ^ 2 =
      targetScale ^ 2 * ‖prediction - target‖ ^ 2 := by
  rw [affineTransitionMean_sub_affineTransitionMean]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Scalar equal-covariance Gaussian transition cost reduces exactly to a
weighted local squared error.  Positivity of `variance` is a semantic
requirement for a Gaussian variance, although the algebraic identity itself
also holds at the field's zero-division convention. -/
theorem equalCovarianceTransitionCost_local
    (prediction target previous : E)
    (targetScale skipScale variance : ℝ) :
    ‖affineTransitionMean prediction previous targetScale skipScale -
        affineTransitionMean target previous targetScale skipScale‖ ^ 2 /
        (2 * variance) =
      (targetScale ^ 2 / (2 * variance)) *
        ‖prediction - target‖ ^ 2 := by
  rw [norm_affineTransitionMean_sub_sq]
  ring

/-! ## SNR schedules and the local objective -/

/-- The local coefficient between two adjacent SNR values. -/
def scheduleWeight (snr : ℕ → ℝ) (time : ℕ) : ℝ :=
  snr (time + 1) - snr time

/-- Sum of weighted block-local losses. -/
def weightedLocalObjective
    (steps : ℕ) (snr : ℕ → ℝ) (localLoss : ℕ → ℝ) : ℝ :=
  ∑ time ∈ Finset.range steps, scheduleWeight snr time * localLoss time

/-- A monotone SNR schedule makes every adjacent local coefficient
nonnegative. -/
theorem scheduleWeight_nonneg_of_monotone
    (snr : ℕ → ℝ) (hsnr : Monotone snr) (time : ℕ) :
    0 ≤ scheduleWeight snr time := by
  exact sub_nonneg.mpr (hsnr (Nat.le_succ time))

/-- Adjacent SNR increments telescope exactly to the endpoint difference. -/
theorem sum_scheduleWeight
    (steps : ℕ) (snr : ℕ → ℝ) :
    ∑ time ∈ Finset.range steps, scheduleWeight snr time =
      snr steps - snr 0 := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [scheduleWeight]
      ring

/-- The NoProp parameterization `SNR(t) = exp(-γ(t))` is monotone when `γ` is
antitone, as required for nonnegative local loss weights. -/
def snrOfGamma {Time : Type*} (gamma : Time → ℝ) : Time → ℝ :=
  fun time => Real.exp (-gamma time)

theorem snrOfGamma_monotone_of_antitone
    {Time : Type*} [Preorder Time]
    (gamma : Time → ℝ) (hgamma : Antitone gamma) :
    Monotone (snrOfGamma gamma) := by
  intro first second hle
  exact Real.exp_le_exp.mpr (neg_le_neg (hgamma hle))

/-- Conversely, a strictly increasing `γ` makes the induced SNR strictly
decrease.  This is the schedule-direction boundary. -/
theorem snrOfGamma_strictAnti_of_strictMono
    {Time : Type*} [Preorder Time]
    (gamma : Time → ℝ) (hgamma : StrictMono gamma) :
    StrictAnti (snrOfGamma gamma) := by
  intro first second hlt
  exact Real.exp_lt_exp.mpr (neg_lt_neg (hgamma hlt))

/-! ## One sampled block is an unbiased estimator only after scaling -/

/-- Exact arithmetic mean over the first `steps` values. -/
def finiteUniformMean
    (steps : ℕ) (value : ℕ → ℝ) : ℝ :=
  (∑ time ∈ Finset.range steps, value time) / steps

/-- The single-block estimator used when one uniformly sampled time step
stands in for the full sum. -/
def scaledSingleBlockEstimator
    (steps : ℕ) (localTerm : ℕ → ℝ) (time : ℕ) : ℝ :=
  steps * localTerm time

/-- Averaging the scaled single-block estimator recovers the complete sum. -/
theorem finiteUniformMean_scaledSingleBlockEstimator
    (steps : ℕ) (localTerm : ℕ → ℝ) (hsteps : 0 < steps) :
    finiteUniformMean steps
        (scaledSingleBlockEstimator steps localTerm) =
      ∑ time ∈ Finset.range steps, localTerm time := by
  have hstepsReal : (steps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hsteps)
  simp only [finiteUniformMean, scaledSingleBlockEstimator]
  rw [← Finset.mul_sum]
  field_simp

/-- Without the scale factor, the exact mean need not equal the complete
objective.  Two unit local terms are the smallest counterexample. -/
theorem unscaledUniformMean_not_fullSum :
    finiteUniformMean 2 (fun _ => (1 : ℝ)) ≠
      ∑ _time ∈ Finset.range 2, (1 : ℝ) := by
  norm_num [finiteUniformMean]

/-! ## Disjoint block updates commute -/

variable {Block Parameter : Type*} [DecidableEq Block]

/-- Change exactly one block's private parameter. -/
def privateBlockStep
    (update : Block → Parameter → Parameter)
    (block : Block)
    (parameters : Block → Parameter) :
    Block → Parameter :=
  Function.update parameters block (update block (parameters block))

@[simp]
theorem privateBlockStep_same
    (update : Block → Parameter → Parameter)
    (block : Block)
    (parameters : Block → Parameter) :
    privateBlockStep update block parameters block =
      update block (parameters block) := by
  simp [privateBlockStep]

@[simp]
theorem privateBlockStep_other
    (update : Block → Parameter → Parameter)
    (changed other : Block)
    (parameters : Block → Parameter)
    (hne : other ≠ changed) :
    privateBlockStep update changed parameters other =
      parameters other := by
  simp [privateBlockStep, hne]

/-- Parameter updates for distinct blocks commute.  This is the exact
dependency theorem licensing parallel or arbitrarily ordered private-block
updates. -/
theorem privateBlockStep_commute
    (update : Block → Parameter → Parameter)
    (first second : Block)
    (parameters : Block → Parameter)
    (hne : first ≠ second) :
    privateBlockStep update first
        (privateBlockStep update second parameters) =
      privateBlockStep update second
        (privateBlockStep update first parameters) := by
  funext block
  by_cases hfirst : block = first
  · subst block
    simp [privateBlockStep, hne]
  · by_cases hsecond : block = second
    · subst block
      simp [privateBlockStep, hne, hfirst]
    · simp [privateBlockStep, hfirst, hsecond]

/-! ## Boundaries: shared embeddings and reversed schedules -/

/-- Scalar local prediction loss used for executable boundary fixtures. -/
def scalarLocalLoss (prediction target : ℝ) : ℝ :=
  (prediction - target) ^ 2

/-- Updating a shared target embedding changes both of two otherwise local
block losses.  Private block parameters remain separable only conditional on
the shared embedding. -/
theorem sharedTargetEmbedding_changes_multipleLocalLosses :
    scalarLocalLoss 0 0 ≠ scalarLocalLoss 0 1 ∧
      scalarLocalLoss 2 0 ≠ scalarLocalLoss 2 1 := by
  norm_num [scalarLocalLoss]

/-- Reversing the SNR direction yields a negative weight even for a positive
local loss. -/
theorem reversedSnrSchedule_negativeLocalTerm :
    scheduleWeight (fun time => if time = 0 then (1 : ℝ) else 0) 0 *
        scalarLocalLoss 1 0 <
      0 := by
  norm_num [scheduleWeight, scalarLocalLoss]

/-- Positive fixture: two rising SNR increments weight two local losses
nonnegatively and telescope to the endpoint increase. -/
theorem risingSnr_twoStep :
    weightedLocalObjective 2
        (fun time => (time : ℝ))
        (fun time => if time = 0 then 3 else 5) =
      8 := by
  norm_num [weightedLocalObjective, scheduleWeight, Finset.sum_range_succ]

end

end NoPropLocalLearning

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
