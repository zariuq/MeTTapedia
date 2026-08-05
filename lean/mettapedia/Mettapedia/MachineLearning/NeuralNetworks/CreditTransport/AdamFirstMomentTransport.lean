import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling

/-!
# Exact credit reconstruction from Adam's first moment

Adam's first-moment buffer is not the current raw credit after the first
optimizer step.  Nevertheless, an exact weighted credit aggregate can be
recovered from the incoming and outgoing buffers.  If

`mₜ = β mₜ₋₁ + (1 - β) gₜ`,

then after a finite chronological list of credits,

`mₖ - βᵏ m₀ = (1 - β) (βᵏ⁻¹ g₁ + ... + β gₖ₋₁ + gₖ)`.

This file proves that identity in an arbitrary real module.  It also records
two implementation boundaries: the initial moment must be corrected by
`βᵏ`, not merely by `β`, and decoupled weight decay can move a parameter even
when the reconstructed credit is zero.  Thus parameter displacement is not a
sound substitute for credit-support telemetry.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AdamFirstMomentTransport

noncomputable section

variable {Credit : Type*}
  [AddCommGroup Credit] [Module ℝ Credit]

/-- One vector-valued first-moment update. -/
def firstMomentStep
    (decay : ℝ) (previous gradient : Credit) : Credit :=
  decay • previous + (1 - decay) • gradient

/-- Run first-moment updates over credits in chronological order. -/
def firstMomentRun
    (decay : ℝ) : Credit → List Credit → Credit
  | previous, [] => previous
  | previous, gradient :: gradients =>
      firstMomentRun decay
        (firstMomentStep decay previous gradient) gradients

/-- The reverse-geometrically weighted aggregate represented by a sequence
of first-moment updates.  The newest credit has coefficient one. -/
def reverseGeometricCredit
    (decay : ℝ) : List Credit → Credit
  | [] => 0
  | gradient :: gradients =>
      decay ^ gradients.length • gradient +
        reverseGeometricCredit decay gradients

/-- Exact closed form for a finite first-moment run. -/
theorem firstMomentRun_eq
    (decay : ℝ) (previous : Credit) (gradients : List Credit) :
    firstMomentRun decay previous gradients =
      decay ^ gradients.length • previous +
        (1 - decay) • reverseGeometricCredit decay gradients := by
  induction gradients generalizing previous with
  | nil =>
      simp [firstMomentRun, reverseGeometricCredit]
  | cons gradient gradients inductionHypothesis =>
      rw [firstMomentRun, inductionHypothesis]
      simp only [reverseGeometricCredit, List.length_cons, pow_succ]
      simp only [firstMomentStep]
      module

/-- Subtracting the correctly decayed incoming moment isolates the weighted
credit innovation. -/
theorem firstMomentInnovation_eq
    (decay : ℝ) (previous : Credit) (gradients : List Credit) :
    firstMomentRun decay previous gradients -
        decay ^ gradients.length • previous =
      (1 - decay) • reverseGeometricCredit decay gradients := by
  rw [firstMomentRun_eq]
  module

/-- Reconstruct the credit aggregate from the two moment-buffer endpoints. -/
def reconstructedCredit
    (decay : ℝ) (previous : Credit) (gradients : List Credit) : Credit :=
  (1 / (1 - decay)) •
    (firstMomentRun decay previous gradients -
      decay ^ gradients.length • previous)

/-- Exact reconstruction whenever the first-moment decay is not one. -/
theorem reconstructedCredit_eq
    {decay : ℝ} (decayNeOne : decay ≠ 1)
    (previous : Credit) (gradients : List Credit) :
    reconstructedCredit decay previous gradients =
      reverseGeometricCredit decay gradients := by
  rw [reconstructedCredit, firstMomentInnovation_eq, smul_smul]
  have denominatorNeZero : 1 - decay ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm decayNeOne)
  have scaleEq : (1 / (1 - decay)) * (1 - decay) = 1 := by
    field_simp
  rw [scaleEq, one_smul]

/-- A single optimizer step reconstructs the current credit exactly. -/
theorem reconstructedCredit_singleton
    {decay : ℝ} (decayNeOne : decay ≠ 1)
    (previous gradient : Credit) :
    reconstructedCredit decay previous [gradient] = gradient := by
  rw [reconstructedCredit_eq decayNeOne]
  simp [reverseGeometricCredit]

/-- Two optimizer steps reconstruct `β g₁ + g₂`, not their unweighted sum. -/
theorem reconstructedCredit_pair
    {decay : ℝ} (decayNeOne : decay ≠ 1)
    (previous first second : Credit) :
    reconstructedCredit decay previous [first, second] =
      decay • first + second := by
  rw [reconstructedCredit_eq decayNeOne]
  simp [reverseGeometricCredit]

/-! ## Support and squared-mass invariance -/

variable {Index : Type*}

/-- Squared coordinate mass on a declared finite support. -/
def squaredMass
    (direction : Index → ℝ) (support : Finset Index) : ℝ :=
  ∑ index ∈ support, direction index ^ 2

/-- Uniform scaling multiplies every fixed-support squared mass by the same
square factor. -/
theorem squaredMass_scale
    (scale : ℝ) (direction : Index → ℝ) (support : Finset Index) :
    squaredMass (fun index => scale * direction index) support =
      scale ^ 2 * squaredMass direction support := by
  simp only [squaredMass, mul_pow]
  rw [Finset.mul_sum]

/-- Consequently, a nonzero uniform reconstruction scale preserves the
captured squared-mass fraction of every fixed support. -/
theorem squaredMassFraction_scale
    [Fintype Index]
    {scale : ℝ} (scaleNeZero : scale ≠ 0)
    (direction : Index → ℝ) (support : Finset Index)
    (totalNeZero : squaredMass direction Finset.univ ≠ 0) :
    squaredMass (fun index => scale * direction index) support /
        squaredMass (fun index => scale * direction index) Finset.univ =
      squaredMass direction support /
        squaredMass direction Finset.univ := by
  rw [squaredMass_scale, squaredMass_scale]
  have squareNeZero : scale ^ 2 ≠ 0 := pow_ne_zero _ scaleNeZero
  field_simp

/-- Nonzero uniform scaling also preserves coordinate support exactly. -/
theorem scaled_coordinate_eq_zero_iff
    {scale : ℝ} (scaleNeZero : scale ≠ 0)
    (direction : Index → ℝ) (index : Index) :
    scale * direction index = 0 ↔ direction index = 0 := by
  exact mul_eq_zero.trans (or_iff_right scaleNeZero)

/-- The tempting one-step correction is wrong once more than one optimizer
step has accumulated from a nonzero incoming moment. -/
def oneStepInitialCorrection
    (decay : ℝ) (previous : Credit) (gradients : List Credit) : Credit :=
  (1 / (1 - decay)) •
    (firstMomentRun decay previous gradients - decay • previous)

theorem oneStepInitialCorrection_fails_after_two_steps :
    oneStepInitialCorrection (1 / 2) (4 : ℝ) [0, 0] = -2 ∧
      reconstructedCredit (1 / 2) (4 : ℝ) [0, 0] = 0 ∧
      oneStepInitialCorrection (1 / 2) (4 : ℝ) [0, 0] ≠
        reconstructedCredit (1 / 2) (4 : ℝ) [0, 0] := by
  norm_num [oneStepInitialCorrection, reconstructedCredit,
    firstMomentRun, firstMomentStep]

/-- A zero reconstructed credit does not imply zero AdamW displacement:
decoupled weight decay supplies an independent parameter-dependent term. -/
theorem weightDecay_moves_with_zero_reconstructedCredit :
    reconstructedCredit (9 / 10) (0 : ℝ) [0] = 0 ∧
      OptimizerTransport.scalarAdamWDirection 0 2 (1 / 10) = 1 / 5 ∧
      OptimizerTransport.scalarAdamWDirection 0 2 (1 / 10) ≠ 0 := by
  norm_num [reconstructedCredit, firstMomentRun, firstMomentStep,
    OptimizerTransport.scalarAdamWDirection]

#print axioms firstMomentRun_eq
#print axioms firstMomentInnovation_eq
#print axioms reconstructedCredit_eq
#print axioms reconstructedCredit_singleton
#print axioms reconstructedCredit_pair
#print axioms squaredMass_scale
#print axioms squaredMassFraction_scale
#print axioms scaled_coordinate_eq_zero_iff
#print axioms oneStepInitialCorrection_fails_after_two_steps
#print axioms weightDecay_moves_with_zero_reconstructedCredit

end

end AdamFirstMomentTransport

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
