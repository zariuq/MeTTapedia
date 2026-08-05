import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AffineFixedPointAcceleration

/-!
# Semantic drift compensation

Yu, Liu, and van de Weijer, *Semantic Drift Compensation for Class-Incremental
Learning* (CVPR 2020, arXiv:2004.00440), Equations (8)--(13), update a stored
class prototype by interpolating the measured feature drifts of current-task
examples with Gaussian-kernel weights.

This file isolates the finite geometry of that estimator:

* nonzero raw weights normalize to an affine combination;
* constant proxy drift is recovered exactly;
* nonnegative weights preserve any uniform local drift-error radius;
* the compensated prototype inherits the same error budget;
* recursive compensation is exactly addition of the chronological estimates;
* Gaussian weights have a positive normalizer on a nonempty batch.

The local-coherence premise is essential.  Current-task drift can point in the
opposite direction from an old prototype's true drift, and a zero normalizer
does not preserve even a constant vector.  These results therefore do not
derive the source's empirical accuracy gains or assert that feature distance
alone guarantees similar semantic drift.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SemanticDriftCompensation

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

noncomputable section

variable {Sample State : Type*} [Fintype Sample]
variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Normalize a finite family of raw interpolation weights. -/
def normalizedWeights (raw : Sample → ℝ) : Sample → ℝ :=
  fun sample => (∑ other, raw other)⁻¹ * raw sample

/-- A nonzero normalizer makes the normalized weights affine. -/
theorem normalizedWeights_affine
    (raw : Sample → ℝ)
    (total_ne : (∑ sample, raw sample) ≠ 0) :
    IsAffineWeights (normalizedWeights raw) := by
  simp only [IsAffineWeights, normalizedWeights]
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ total_ne

/-- Nonnegative raw weights remain nonnegative after normalization by a
positive total. -/
theorem normalizedWeights_nonnegative
    (raw : Sample → ℝ)
    (raw_nonnegative : ∀ sample, 0 ≤ raw sample)
    (total_pos : 0 < ∑ sample, raw sample) :
    ∀ sample, 0 ≤ normalizedWeights raw sample := by
  intro sample
  exact
    mul_nonneg
      (inv_nonneg.mpr (le_of_lt total_pos))
      (raw_nonnegative sample)

/-- Equation (10): interpolate the observed current-task drift field at an
old prototype. -/
def weightedDriftEstimate
    (raw : Sample → ℝ) (drift : Sample → State) : State :=
  weightedCombination (normalizedWeights raw) drift

/-- If every observed proxy has the same drift, interpolation recovers that
drift exactly. -/
theorem weightedDriftEstimate_eq_of_constant
    (raw : Sample → ℝ) (drift : Sample → State) (target : State)
    (total_ne : (∑ sample, raw sample) ≠ 0)
    (constant : ∀ sample, drift sample = target) :
    weightedDriftEstimate raw drift = target := by
  have drift_eq : drift = fun _ => target := funext constant
  rw [weightedDriftEstimate, drift_eq]
  exact
    weightedCombination_const
      (normalizedWeights raw) target
      (normalizedWeights_affine raw total_ne)

/-- A positive weighted average of locally accurate drift proxies is no less
accurate than their common radius. -/
theorem weightedDriftEstimate_norm_sub_le_radius
    (raw : Sample → ℝ) (drift : Sample → State) (target : State)
    (total_pos : 0 < ∑ sample, raw sample)
    (raw_nonnegative : ∀ sample, 0 ≤ raw sample)
    (radius : ℝ)
    (bounded : ∀ sample, ‖drift sample - target‖ ≤ radius) :
    ‖weightedDriftEstimate raw drift - target‖ ≤ radius := by
  exact
    norm_weightedCombination_sub_reference_le_radius
      (normalizedWeights raw) drift target
      (normalizedWeights_affine raw (ne_of_gt total_pos))
      (normalizedWeights_nonnegative raw raw_nonnegative total_pos)
      radius bounded

/-- Equations (12)--(13) update one stored prototype by one estimated drift. -/
def compensatePrototype
    (prototype estimatedDrift : State) : State :=
  prototype + estimatedDrift

omit [NormedSpace ℝ State] in
/-- Prototype translation neither amplifies nor hides drift-estimation error. -/
theorem norm_compensatePrototype_sub_true
    (prototype estimatedDrift trueDrift : State) :
    ‖compensatePrototype prototype estimatedDrift -
        compensatePrototype prototype trueDrift‖ =
      ‖estimatedDrift - trueDrift‖ := by
  congr 1
  unfold compensatePrototype
  abel

/-- The local proxy radius transfers directly to the compensated prototype. -/
theorem compensatePrototype_norm_sub_true_le_radius
    (raw : Sample → ℝ) (drift : Sample → State)
    (prototype trueDrift : State)
    (total_pos : 0 < ∑ sample, raw sample)
    (raw_nonnegative : ∀ sample, 0 ≤ raw sample)
    (radius : ℝ)
    (bounded : ∀ sample, ‖drift sample - trueDrift‖ ≤ radius) :
    ‖compensatePrototype prototype
          (weightedDriftEstimate raw drift) -
        compensatePrototype prototype trueDrift‖ ≤ radius := by
  rw [norm_compensatePrototype_sub_true]
  exact
    weightedDriftEstimate_norm_sub_le_radius
      raw drift trueDrift total_pos raw_nonnegative radius bounded

/-- Exact local drift recovery gives exact prototype compensation. -/
theorem compensatePrototype_exact_of_constant
    (raw : Sample → ℝ) (drift : Sample → State)
    (prototype trueDrift : State)
    (total_ne : (∑ sample, raw sample) ≠ 0)
    (constant : ∀ sample, drift sample = trueDrift) :
    compensatePrototype prototype (weightedDriftEstimate raw drift) =
      compensatePrototype prototype trueDrift := by
  rw [weightedDriftEstimate_eq_of_constant raw drift trueDrift
    total_ne constant]

/-- Chronological recursive compensation from Equation (13). -/
def compensateRun : List State → State → State
  | [], initial => initial
  | drift :: drifts, initial =>
      compensateRun drifts (compensatePrototype initial drift)

omit [NormedSpace ℝ State] in
@[simp]
theorem compensateRun_nil (initial : State) :
    compensateRun [] initial = initial := rfl

omit [NormedSpace ℝ State] in
@[simp]
theorem compensateRun_cons
    (drift : State) (drifts : List State) (initial : State) :
    compensateRun (drift :: drifts) initial =
      compensateRun drifts (compensatePrototype initial drift) := rfl

omit [NormedSpace ℝ State] in
/-- Recursive compensation is the initial prototype plus the sum of all
chronological drift estimates. -/
theorem compensateRun_eq_initial_add_sum
    (drifts : List State) (initial : State) :
    compensateRun drifts initial = initial + drifts.sum := by
  induction drifts generalizing initial with
  | nil =>
      simp
  | cons drift drifts induction =>
      rw [compensateRun_cons, induction]
      simp only [compensatePrototype, List.sum_cons]
      ac_rfl

omit [NormedSpace ℝ State] in
/-- Splitting a task stream does not change recursive compensation. -/
theorem compensateRun_append
    (first second : List State) (initial : State) :
    compensateRun (first ++ second) initial =
      compensateRun second (compensateRun first initial) := by
  induction first generalizing initial with
  | nil =>
      rfl
  | cons drift drifts induction =>
      simp only [List.cons_append, compensateRun_cons]
      exact induction (compensatePrototype initial drift)

/-- Equation (11), parameterized by squared feature distance. -/
def gaussianKernelWeight
    (distanceSquared bandwidth : ℝ) : ℝ :=
  Real.exp (-distanceSquared / (2 * bandwidth ^ 2))

theorem gaussianKernelWeight_pos
    (distanceSquared bandwidth : ℝ) :
    0 < gaussianKernelWeight distanceSquared bandwidth := by
  exact Real.exp_pos _

/-- A nonempty current-task batch gives the Gaussian estimator a positive
normalizer. -/
theorem gaussianWeights_total_pos
    [Nonempty Sample]
    (distanceSquared : Sample → ℝ) (bandwidth : ℝ) :
    0 <
      ∑ sample,
        gaussianKernelWeight (distanceSquared sample) bandwidth := by
  apply Finset.sum_pos
  · intro sample _
    exact gaussianKernelWeight_pos _ _
  · exact Finset.univ_nonempty

/-- Gaussian interpolation exactly recovers a constant measured drift on a
nonempty batch. -/
theorem gaussianDriftEstimate_eq_of_constant
    [Nonempty Sample]
    (distanceSquared : Sample → ℝ) (bandwidth : ℝ)
    (drift : Sample → State) (target : State)
    (constant : ∀ sample, drift sample = target) :
    weightedDriftEstimate
        (fun sample =>
          gaussianKernelWeight (distanceSquared sample) bandwidth)
        drift =
      target := by
  apply weightedDriftEstimate_eq_of_constant
  · exact ne_of_gt (gaussianWeights_total_pos distanceSquared bandwidth)
  · exact constant

section Boundaries

/-- One positive proxy whose measured drift is opposite to the old class's
true drift. -/
def singletonRaw : Fin 1 → ℝ := fun _ => 1

theorem singleton_proxy_estimate :
    weightedDriftEstimate singletonRaw
        (fun _ : Fin 1 => (1 : ℝ)) =
      1 := by
  norm_num [weightedDriftEstimate, weightedCombination, normalizedWeights,
    singletonRaw]

/-- Current-task drift alone cannot certify an old prototype's drift. -/
theorem proxy_drift_can_miscompensate :
    compensatePrototype 0
        (weightedDriftEstimate singletonRaw
          (fun _ : Fin 1 => (1 : ℝ))) ≠
      (0 : ℝ) + (-1) := by
  norm_num [singleton_proxy_estimate, compensatePrototype]

/-- A signed kernel can have a zero normalizer. -/
def cancellingRaw : Fin 2 → ℝ := ![1, -1]

/-- With a zero normalizer, totalized field inversion maps even a constant
nonzero drift to zero; the nonzero-total premise is load-bearing. -/
theorem zero_total_does_not_preserve_constant :
    weightedDriftEstimate cancellingRaw
        (fun _ : Fin 2 => (7 : ℝ)) =
      0 := by
  norm_num [weightedDriftEstimate, weightedCombination, normalizedWeights,
    cancellingRaw, Matrix.cons_val_zero, Matrix.cons_val_one]

end Boundaries

end

end SemanticDriftCompensation

end Mettapedia.MachineLearning.ContinualLearning
