import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ForwardInitializationOrder
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-!
# Stream-aligned average initialization

Pinchetti, Frieder, Lukasiewicz, and Salvatori, *Faster Predictive Coding
Networks via Better Initialization*, arXiv:2601.20895v1, initialize each
hidden layer of a labelled stream with the previous converged class average
(Eq. 7).  The audited primary artifact has SHA-256
`b6911b2d3bc32b4beed13deca49a1cbe88b38a1bbf56a210379e03322a285df9`.

This file proves the statistical core that the source uses but does not state
as a theorem: over a nonempty finite stream, the arithmetic mean is the unique
constant initializer minimizing total squared initialization error.  The
proof is the exact finite bias--variance decomposition, so it is reusable for
every label/layer coordinate.  A concrete fixture shows strict improvement
over a mismatched forward initializer, while an empty-stream fixture shows
why nonemptiness is necessary.

The final theorem composes this initialization result with the existing
contractive-solver certificate: if a mean initializer is closer to the actual
fixed point than a baseline, every finite geometric error bound is no worse.
This is a conditional solver statement, not a claim that class labels,
previous batches, or model drift automatically satisfy the premise.  Reported
speedups and test accuracy remain empirical.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped BigOperators

/-! ## Exact finite-stream geometry -/

/-- Arithmetic mean of one scalar hidden coordinate over a finite stream.
For Eq. 7, `Sample` is one label-conditioned sub-minibatch. -/
noncomputable def streamHiddenMean
    {Sample : Type*} [Fintype Sample]
    (hidden : Sample → ℝ) : ℝ :=
  (Fintype.card Sample : ℝ)⁻¹ * ∑ sample, hidden sample

/-- Total squared initialization mismatch for a constant initializer. -/
noncomputable def streamInitializationError
    {Sample : Type*} [Fintype Sample]
    (hidden : Sample → ℝ) (initializer : ℝ) : ℝ :=
  ∑ sample, (hidden sample - initializer) ^ 2

/-- Centered hidden states sum to zero on a nonempty stream. -/
theorem sum_hidden_sub_streamMean_eq_zero
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (hidden : Sample → ℝ) :
    ∑ sample, (hidden sample - streamHiddenMean hidden) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold streamHiddenMean
  have hcard : (Fintype.card Sample : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- Exact finite bias--variance decomposition. -/
theorem streamInitializationError_decomposition
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (hidden : Sample → ℝ) (initializer : ℝ) :
    streamInitializationError hidden initializer =
      streamInitializationError hidden (streamHiddenMean hidden) +
        (Fintype.card Sample : ℝ) *
          (initializer - streamHiddenMean hidden) ^ 2 := by
  let mean := streamHiddenMean hidden
  have hcenter : ∑ sample, (hidden sample - mean) = 0 := by
    simpa [mean] using sum_hidden_sub_streamMean_eq_zero hidden
  have hpoint :
      ∀ sample,
        (hidden sample - initializer) ^ 2 =
          (hidden sample - mean) ^ 2 +
            2 * (mean - initializer) * (hidden sample - mean) +
            (mean - initializer) ^ 2 := by
    intro sample
    ring
  unfold streamInitializationError
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross :
      ∑ sample, 2 * (mean - initializer) * (hidden sample - mean) = 0 := by
    rw [← Finset.mul_sum]
    simp [hcenter]
  rw [hcross]
  simp only [add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  ring

/-- Eq. 7's class average is a global minimizer among constant initializers. -/
theorem streamHiddenMean_minimizes_initializationError
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (hidden : Sample → ℝ) (initializer : ℝ) :
    streamInitializationError hidden (streamHiddenMean hidden) ≤
      streamInitializationError hidden initializer := by
  calc
    streamInitializationError hidden (streamHiddenMean hidden) ≤
        streamInitializationError hidden (streamHiddenMean hidden) +
          (Fintype.card Sample : ℝ) *
            (initializer - streamHiddenMean hidden) ^ 2 :=
      le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = streamInitializationError hidden initializer :=
      (streamInitializationError_decomposition hidden initializer).symm

/-- The minimizer is strict whenever the initializer differs from the class
mean. -/
theorem streamHiddenMean_strictly_better_of_ne
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (hidden : Sample → ℝ) (initializer : ℝ)
    (hne : initializer ≠ streamHiddenMean hidden) :
    streamInitializationError hidden (streamHiddenMean hidden) <
      streamInitializationError hidden initializer := by
  calc
    streamInitializationError hidden (streamHiddenMean hidden) <
        streamInitializationError hidden (streamHiddenMean hidden) +
          (Fintype.card Sample : ℝ) *
            (initializer - streamHiddenMean hidden) ^ 2 := by
      apply lt_add_of_pos_right
      exact mul_pos (by exact_mod_cast Fintype.card_pos)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    _ = streamInitializationError hidden initializer :=
      (streamInitializationError_decomposition hidden initializer).symm

/-- Exact uniqueness characterization for the stream-average initializer. -/
theorem streamInitializationError_eq_minimum_iff
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (hidden : Sample → ℝ) (initializer : ℝ) :
    streamInitializationError hidden initializer =
        streamInitializationError hidden (streamHiddenMean hidden) ↔
      initializer = streamHiddenMean hidden := by
  constructor
  · intro heq
    by_contra hne
    have hstrict :=
      streamHiddenMean_strictly_better_of_ne hidden initializer hne
    linarith
  · rintro rfl
    rfl

/-! ## Positive and negative fixtures -/

/-- Two converged states at one and three have average two.  Initializing at
the average has error two; initializing at zero has error ten. -/
theorem twoSample_streamAverage_strict :
    streamHiddenMean (fun sample : Bool => if sample then (3 : ℝ) else 1) = 2 ∧
      streamInitializationError
          (fun sample : Bool => if sample then (3 : ℝ) else 1) 2 = 2 ∧
      streamInitializationError
          (fun sample : Bool => if sample then (3 : ℝ) else 1) 0 = 10 := by
  norm_num [streamHiddenMean, streamInitializationError,
    Fintype.sum_bool]

/-- Negative boundary: on an empty stream every constant initializer has
zero error, so the arithmetic mean is not uniquely optimal. -/
theorem emptyStream_has_no_unique_constant_initializer :
    streamInitializationError (fun sample : Empty => nomatch sample) 0 =
        streamInitializationError (fun sample : Empty => nomatch sample) 1 ∧
      (0 : ℝ) ≠ 1 := by
  norm_num [streamInitializationError]

/-! ## Composition with corrective settling -/

open
  Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
  Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-- If the stream mean is no farther from the actual solver fixed point than
a baseline initializer, contraction transports that advantage through every
finite number of corrective settling steps. -/
theorem streamMean_contractingSolver_bound_le_baseline
    {Sample : Type*} [Fintype Sample]
    (hidden : Sample → ℝ)
    {solver : ℝ → ℝ}
    (certificate : ContractionCertificate solver)
    (target baseline : ℝ)
    (htarget : IsFixedPoint solver target)
    (hbetter :
      ‖streamHiddenMean hidden - target‖ ≤ ‖baseline - target‖)
    (steps : ℕ) :
    ‖solver^[steps] (streamHiddenMean hidden) - target‖ ≤
      certificate.factor ^ steps * ‖baseline - target‖ := by
  calc
    ‖solver^[steps] (streamHiddenMean hidden) - target‖ ≤
      certificate.factor ^ steps *
          ‖streamHiddenMean hidden - target‖ :=
      iterate_initializer_to_fixedPoint_le certificate
        target (streamHiddenMean hidden) htarget steps
    _ ≤ certificate.factor ^ steps * ‖baseline - target‖ :=
      mul_le_mul_of_nonneg_left hbetter
        (pow_nonneg certificate.factor_nonneg steps)

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
