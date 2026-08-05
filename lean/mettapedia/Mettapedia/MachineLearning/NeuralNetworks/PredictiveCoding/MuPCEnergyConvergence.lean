import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DepthScalingVector
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Deterministic core of the μPC energy limit

Innocenti, Achour, and Buckley, *μPC: Scaling Predictive Coding to 100+
Layer Networks*, arXiv:2505.13124v2, express the equilibrated linear-ResNet
energy as a residual quadratic form with an inverse rescaling matrix
(Appendix A.2.6, Eqs. 31--32).  Their Theorem 1 argues that this rescaling
approaches the identity at random initialization when the depth/width aspect
ratio vanishes.  The audited v2 artifact has SHA-256
`b7df50b34c099820478a7c250f175a5ea60d56a07a82c111ca64bc1eacd3de01`.

This file isolates and proves the deterministic part of that argument:

* identity inverse rescaling recovers the batch squared-error loss exactly;
* convergence of the inverse rescaling to the identity implies convergence
  of the equilibrated quadratic energy;
* a finite-dimensional diagonal aspect-ratio family supplies an executable
  positive instance;
* a nonvanishing aspect ratio supplies an exact failure fixture; and
* convergence of energy values alone does **not** imply convergence of
  parameter gradients.

The last boundary matters for the paper's subsequent statement that PC then
computes the same gradients as backpropagation.  That conclusion additionally
requires derivative-level control of the weight-dependent rescaling.  We do
not turn the paper's random-matrix scaling argument into an assumption, and
we make no claim here about changing-dimensional random matrices or trained
weights.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Matrix Topology
open scoped BigOperators

/-! ## Batch quadratic energies -/

/-- Batch squared-error loss, using the normalization in Eq. 31.  The empty
batch has value zero by Lean's total inverse convention. -/
noncomputable def muPCBatchSquaredError
    {Sample Output : Type*} [Fintype Sample] [Fintype Output]
    (residual : Sample → Output → ℝ) : ℝ :=
  (Fintype.card Sample : ℝ)⁻¹ *
    ∑ sample, residual sample ⬝ᵥ residual sample

/-- Eq. 31 with the inverse rescaling supplied explicitly.  This separates
the exact quadratic identity from the probabilistic claim that Eq. 32 tends
to the identity. -/
noncomputable def muPCEquilibratedQuadraticEnergy
    {Sample Output : Type*} [Fintype Sample] [Fintype Output]
    (residual : Sample → Output → ℝ)
    (inverseRescaling : Matrix Output Output ℝ) : ℝ :=
  (Fintype.card Sample : ℝ)⁻¹ *
    ∑ sample,
      residual sample ⬝ᵥ inverseRescaling.mulVec (residual sample)

/-- The exact BP/MSE endpoint of the rescaling family. -/
theorem muPCEquilibratedQuadraticEnergy_one
    {Sample Output : Type*} [Fintype Sample] [Fintype Output]
    [DecidableEq Output]
    (residual : Sample → Output → ℝ) :
    muPCEquilibratedQuadraticEnergy residual 1 =
      muPCBatchSquaredError residual := by
  simp [muPCEquilibratedQuadraticEnergy, muPCBatchSquaredError]

/-- Exact deviation identity: all energy mismatch is carried by
`inverseRescaling - I`. -/
theorem muPCEquilibratedQuadraticEnergy_sub_loss
    {Sample Output : Type*} [Fintype Sample] [Fintype Output]
    [DecidableEq Output]
    (residual : Sample → Output → ℝ)
    (inverseRescaling : Matrix Output Output ℝ) :
    muPCEquilibratedQuadraticEnergy residual inverseRescaling -
        muPCBatchSquaredError residual =
      (Fintype.card Sample : ℝ)⁻¹ *
        ∑ sample,
          residual sample ⬝ᵥ
            (inverseRescaling - 1).mulVec (residual sample) := by
  unfold muPCEquilibratedQuadraticEnergy muPCBatchSquaredError
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro sample _
  rw [sub_mulVec, one_mulVec, dotProduct_sub]

/-- The residual quadratic form is a continuous readout of the inverse
rescaling matrix. -/
theorem continuous_muPCEquilibratedQuadraticEnergy
    {Sample Output : Type*} [Fintype Sample] [Fintype Output]
    (residual : Sample → Output → ℝ) :
    Continuous
      (fun inverseRescaling : Matrix Output Output ℝ =>
        muPCEquilibratedQuadraticEnergy residual inverseRescaling) := by
  unfold muPCEquilibratedQuadraticEnergy
  fun_prop

/-- Deterministic core of Theorem 1: if the inverse rescaling tends to the
identity, then the equilibrated quadratic energy tends to the MSE loss. -/
theorem muPCEquilibratedQuadraticEnergy_tendsto_loss
    {Sample Output Index : Type*}
    [Fintype Sample] [Fintype Output] [DecidableEq Output]
    {l : Filter Index}
    (residual : Sample → Output → ℝ)
    (inverseRescaling : Index → Matrix Output Output ℝ)
    (hrescaling : Tendsto inverseRescaling l (𝓝 1)) :
    Tendsto
      (fun index =>
        muPCEquilibratedQuadraticEnergy residual
          (inverseRescaling index))
      l (𝓝 (muPCBatchSquaredError residual)) := by
  have h :=
    (continuous_muPCEquilibratedQuadraticEnergy residual).continuousAt.tendsto.comp
      hrescaling
  rw [muPCEquilibratedQuadraticEnergy_one residual] at h
  change
    Tendsto
      ((fun matrix =>
        muPCEquilibratedQuadraticEnergy residual matrix) ∘
          inverseRescaling)
      l (𝓝 (muPCBatchSquaredError residual))
  exact h

/-! ## An executable aspect-ratio family -/

/-- A finite-dimensional diagonal inverse-rescaling family.  Each coordinate
has source-style perturbation `aspect * coefficient`; the inverse is explicit.
This is a deterministic model of the `depth / width → 0` mechanism, not a
replacement for the paper's changing-dimensional random-matrix argument. -/
noncomputable def muPCDiagonalAspectInverseRescaling
    {Output : Type*} [Fintype Output] [DecidableEq Output]
    (coefficient : Output → ℝ) (aspect : ℝ) :
    Matrix Output Output ℝ :=
  Matrix.diagonal
    (fun output => (1 + aspect * coefficient output)⁻¹)

/-- At zero aspect ratio the diagonal family is definitionally at the MSE
endpoint. -/
theorem muPCDiagonalAspectInverseRescaling_zero
    {Output : Type*} [Fintype Output] [DecidableEq Output]
    (coefficient : Output → ℝ) :
    muPCDiagonalAspectInverseRescaling coefficient 0 = 1 := by
  ext i j
  simp [muPCDiagonalAspectInverseRescaling]

/-- The finite-dimensional diagonal inverse rescaling is continuous at the
zero-aspect endpoint. -/
theorem muPCDiagonalAspectInverseRescaling_tendsto_one
    {Output : Type*} [Fintype Output] [DecidableEq Output]
    (coefficient : Output → ℝ) :
    Tendsto
      (muPCDiagonalAspectInverseRescaling coefficient)
      (𝓝 0) (𝓝 1) := by
  have hcontinuous :
      ContinuousAt
        (muPCDiagonalAspectInverseRescaling coefficient) 0 := by
    unfold muPCDiagonalAspectInverseRescaling
    change ContinuousAt
      (fun aspect : ℝ => fun i j =>
        if i = j then (1 + aspect * coefficient i)⁻¹ else 0) 0
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    by_cases hij : i = j
    · subst j
      simpa using
        ((continuousAt_const.add
          (continuousAt_id.mul continuousAt_const)).inv₀ (by norm_num))
    · simpa [hij] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0)
  rw [← muPCDiagonalAspectInverseRescaling_zero coefficient]
  exact hcontinuous

/-- Positive limit instance: any aspect schedule tending to zero recovers
the fixed finite-dimensional batch loss. -/
theorem muPCDiagonalAspectEnergy_tendsto_loss
    {Sample Output Index : Type*}
    [Fintype Sample] [Fintype Output] [DecidableEq Output]
    {l : Filter Index}
    (residual : Sample → Output → ℝ)
    (coefficient : Output → ℝ)
    (aspect : Index → ℝ)
    (haspect : Tendsto aspect l (𝓝 0)) :
    Tendsto
      (fun index =>
        muPCEquilibratedQuadraticEnergy residual
          (muPCDiagonalAspectInverseRescaling coefficient (aspect index)))
      l (𝓝 (muPCBatchSquaredError residual)) := by
  apply muPCEquilibratedQuadraticEnergy_tendsto_loss
  exact
    (muPCDiagonalAspectInverseRescaling_tendsto_one coefficient).comp
      haspect

/-- Concrete positive fixture: one output and zero aspect recover unit MSE. -/
theorem muPCDiagonalAspect_zero :
    muPCEquilibratedQuadraticEnergy
        (fun _ : Unit => fun _ : Unit => (1 : ℝ))
        (muPCDiagonalAspectInverseRescaling
          (fun _ : Unit => (1 : ℝ)) 0) =
      1 := by
  simp [muPCEquilibratedQuadraticEnergy,
    muPCDiagonalAspectInverseRescaling, dotProduct]

/-- Negative boundary: if the aspect ratio does not vanish, the energy need
not approach the loss.  At unit aspect and coefficient one it is exactly one
half of the unit MSE. -/
theorem muPCDiagonalAspect_nonzero :
    muPCEquilibratedQuadraticEnergy
        (fun _ : Unit => fun _ : Unit => (1 : ℝ))
        (muPCDiagonalAspectInverseRescaling
          (fun _ : Unit => (1 : ℝ)) 1) =
      1 / 2 ∧
    muPCBatchSquaredError
        (fun _ : Unit => fun _ : Unit => (1 : ℝ)) =
      1 := by
  norm_num [muPCEquilibratedQuadraticEnergy, muPCBatchSquaredError,
    muPCDiagonalAspectInverseRescaling, dotProduct]

/-! ## Energy convergence is not gradient convergence -/

/-- A smooth family whose value at one tends to zero while its derivative at
one is always one. -/
noncomputable def valueConvergentGradientWitness
    (index : ℕ) (parameter : ℝ) : ℝ :=
  parameter ^ (index + 1) / (index + 1 : ℝ)

theorem valueConvergentGradientWitness_hasDerivAt
    (index : ℕ) :
    HasDerivAt (valueConvergentGradientWitness index) 1 1 := by
  have hden : (index : ℝ) + 1 ≠ 0 := by positivity
  unfold valueConvergentGradientWitness
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul_const
      (hasDerivAt_pow (index + 1) (1 : ℝ))
      (((index : ℝ) + 1)⁻¹) using 1
  simp [hden, Nat.cast_add]

theorem valueConvergentGradientWitness_value_tendsto_zero :
    Tendsto
      (fun index : ℕ => valueConvergentGradientWitness index 1)
      atTop (𝓝 0) := by
  simpa [valueConvergentGradientWitness, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem constant_nonzero_gradient_not_tendsto_zero :
    ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
  simp [tendsto_const_nhds_iff]

/-- Negative crown: convergence of energy values, even for smooth energies,
does not by itself license the paper's gradient-correspondence conclusion. -/
theorem energyValueConvergence_does_not_imply_gradientConvergence :
    Tendsto
        (fun index : ℕ => valueConvergentGradientWitness index 1)
        atTop (𝓝 0) ∧
      (∀ index,
        HasDerivAt (valueConvergentGradientWitness index) 1 1) ∧
      ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
  exact ⟨valueConvergentGradientWitness_value_tendsto_zero,
    valueConvergentGradientWitness_hasDerivAt,
    constant_nonzero_gradient_not_tendsto_zero⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
