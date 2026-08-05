import Mettapedia.MachineLearning.NeuralNetworks.Architecture.MeanFieldSignalDepth

/-!
# Spatial-mode depth scales for normalized convolutional variance kernels

Xiao, Bahri, Sohl-Dickstein, Schoenholz, and Pennington,
*Dynamical Isometry and a Mean Field Theory of CNNs: How to Train
10,000-Layer Vanilla Convolutional Neural Networks*
(ICML 2018, arXiv:1806.05393), diagonalize the linearized covariance
recurrence into spatial Fourier modes.  A mode with averaging eigenvalue
`lambda` inherits multiplier `chi * lambda`, so distinct spatial modes can
have distinct propagation depths even when the zero-frequency multiplier is
critical.

This file isolates the exact finite algebra behind that conclusion.  The
Fourier characters are abstracted to arbitrary complex phases of unit norm.
Every normalized nonnegative variance kernel has mode gain of norm at most
one.  A point-mass kernel gives every such mode unit gain, whereas a diffuse
kernel can preserve the constant mode and annihilate a structured mode.  The
mode gain is then composed with the exact finite-depth recurrence from
`MeanFieldSignalDepth`.

The source's random-channel limit, Gaussian covariance map, construction of
orthogonal multi-channel convolution kernels, end-to-end Jacobian singular
value distribution, and empirical trainability claims are not formalized
here.  Runtime use requires a trace binding a concrete convolutional
linearization to the declared normalized kernel and phase family.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace ConvolutionalModeDepth

open MeanFieldSignalDepth

noncomputable section

/-- A nonnegative spatial variance profile with total mass one. -/
structure VarianceKernel (width : ℕ) where
  weight : Fin width → ℝ
  nonneg : ∀ index, 0 ≤ weight index
  sum_eq_one : ∑ index, weight index = 1

/-- The complex gain of one spatial phase under a normalized variance kernel. -/
def modeGain {width : ℕ}
    (kernel : VarianceKernel width) (phase : Fin width → ℂ) : ℂ :=
  ∑ index, (kernel.weight index : ℂ) * phase index

/-- Every normalized nonnegative kernel is nonexpansive on a phase family
whose entries all have unit norm. -/
theorem norm_modeGain_le_one
    {width : ℕ} (kernel : VarianceKernel width)
    (phase : Fin width → ℂ) (hphase : ∀ index, ‖phase index‖ = 1) :
    ‖modeGain kernel phase‖ ≤ 1 := by
  unfold modeGain
  calc
    ‖∑ index, (kernel.weight index : ℂ) * phase index‖
        ≤ ∑ index, ‖(kernel.weight index : ℂ) * phase index‖ := by
          simpa using
            (norm_sum_le Finset.univ
              (fun index => (kernel.weight index : ℂ) * phase index))
    _ = ∑ index, kernel.weight index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [norm_mul, Complex.norm_of_nonneg (kernel.nonneg index),
        hphase index, mul_one]
    _ = 1 := kernel.sum_eq_one

/-- The zero-frequency phase is preserved by every normalized kernel. -/
@[simp] theorem modeGain_constant_one
    {width : ℕ} (kernel : VarianceKernel width) :
    modeGain kernel (fun _ => 1) = 1 := by
  unfold modeGain
  simp only [mul_one]
  exact_mod_cast kernel.sum_eq_one

/-- A normalized point-mass variance kernel. -/
def pointKernel {width : ℕ} (center : Fin width) :
    VarianceKernel width where
  weight index := if index = center then 1 else 0
  nonneg index := by split <;> norm_num
  sum_eq_one := by simp

/-- A point-mass kernel transmits every phase exactly at its selected site. -/
@[simp] theorem modeGain_pointKernel
    {width : ℕ} (center : Fin width) (phase : Fin width → ℂ) :
    modeGain (pointKernel center) phase = phase center := by
  unfold modeGain pointKernel
  rw [Finset.sum_eq_single center]
  · simp
  · intro index _ hne
    simp [hne]
  · simp

/-- Exact finite residual of one spatial mode. -/
def modeResidual {width : ℕ}
    (correlationMultiplier : ℝ) (kernel : VarianceKernel width)
    (phase : Fin width → ℂ) (initial : ℝ) (depth : ℕ) : ℝ :=
  linearizedResidual
    (correlationMultiplier * ‖modeGain kernel phase‖) initial depth

/-- At critical correlation multiplier one, every normalized kernel preserves
the constant spatial mode at every finite depth. -/
@[simp] theorem critical_constantModeResidual
    {width : ℕ} (kernel : VarianceKernel width)
    (initial : ℝ) (depth : ℕ) :
    modeResidual 1 kernel (fun _ => 1) initial depth = initial := by
  simp [modeResidual]

/-- A point-mass variance profile preserves every unit-norm spatial mode at
criticality, not only the constant mode. -/
theorem critical_pointKernel_modeResidual
    {width : ℕ} (center : Fin width) (phase : Fin width → ℂ)
    (hphase : ‖phase center‖ = 1) (initial : ℝ) (depth : ℕ) :
    modeResidual 1 (pointKernel center) phase initial depth = initial := by
  simp [modeResidual, hphase]

/-- At critical correlation multiplier one, every nonzero mode whose kernel
gain has norm below one contracts strictly at each layer. -/
theorem critical_nonuniformMode_strictly_contracts
    {width : ℕ} {kernel : VarianceKernel width}
    {phase : Fin width → ℂ} {initial : ℝ}
    (hgainPositive : 0 < ‖modeGain kernel phase‖)
    (hgainStrict : ‖modeGain kernel phase‖ < 1)
    (hinitial : initial ≠ 0) (depth : ℕ) :
    |modeResidual 1 kernel phase initial (depth + 1)| <
      |modeResidual 1 kernel phase initial depth| := by
  simpa [modeResidual] using
    ordered_linearizedResidual_strictly_contracts
      hgainPositive hgainStrict hinitial depth

/-- A mode annihilated by the kernel is exactly zero after the first layer. -/
theorem modeGain_zero_annihilates
    {width : ℕ} {kernel : VarianceKernel width}
    {phase : Fin width → ℂ} (hgain : modeGain kernel phase = 0)
    (correlationMultiplier initial : ℝ) (depth : ℕ) :
    modeResidual correlationMultiplier kernel phase initial (depth + 1) = 0 := by
  simp [modeResidual, hgain, linearizedResidual]

/-! ## Executable two-site separation -/

/-- Uniform variance over two spatial sites. -/
def uniformTwoKernel : VarianceKernel 2 where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_two]

/-- The alternating two-site phase. -/
def alternatingTwoPhase : Fin 2 → ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1

theorem alternatingTwoPhase_unit (index : Fin 2) :
    ‖alternatingTwoPhase index‖ = 1 := by
  fin_cases index <;> norm_num [alternatingTwoPhase]

/-- The normalized diffuse kernel preserves the constant mode but annihilates
the alternating mode.  Average variance preservation therefore does not imply
spatial-mode preservation. -/
theorem uniformTwoKernel_separates_modes :
    modeGain uniformTwoKernel (fun _ => 1) = 1 ∧
      modeGain uniformTwoKernel alternatingTwoPhase = 0 := by
  constructor
  · simp
  · norm_num [modeGain, uniformTwoKernel, alternatingTwoPhase,
      Fin.sum_univ_two]

theorem uniformTwoKernel_alternating_annihilated
    (initial : ℝ) (depth : ℕ) :
    modeResidual 1 uniformTwoKernel alternatingTwoPhase
      initial (depth + 1) = 0 := by
  apply modeGain_zero_annihilates
  exact uniformTwoKernel_separates_modes.2

#print axioms norm_modeGain_le_one
#print axioms modeGain_constant_one
#print axioms modeGain_pointKernel
#print axioms critical_constantModeResidual
#print axioms critical_pointKernel_modeResidual
#print axioms critical_nonuniformMode_strictly_contracts
#print axioms modeGain_zero_annihilates
#print axioms uniformTwoKernel_separates_modes
#print axioms uniformTwoKernel_alternating_annihilated

end

end ConvolutionalModeDepth

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
