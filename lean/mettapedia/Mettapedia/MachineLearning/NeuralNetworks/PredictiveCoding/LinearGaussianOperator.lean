import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# Operator-level linear-Gaussian residual models

This file proves the Bayesian semantics once for an arbitrary finite
vector-valued residual operator.  A model has affine residual `A u + c`, an
injective rectangular matrix `A`, and an arbitrary positive-definite residual
precision `Λ`.  Its posterior precision is `Aᵀ Λ A`; the unique energy
equilibrium is exactly the conditional multivariate-Gaussian posterior mean.

Scalar and vector predictive-coding chains are adapters to this theorem.  No
chain-specific completion-of-squares argument is duplicated here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open MeasureTheory ProbabilityTheory Set

/-- A finite affine linear-Gaussian residual model with an injective latent
operator and a positive-definite residual precision. -/
structure LinearGaussianOperatorModel (Latent Residual : Type*)
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual] where
  residualMatrix : Matrix Residual Latent ℝ
  residualPrecision : Matrix Residual Residual ℝ
  residualOffset : Residual → ℝ
  residualMatrix_injective : Function.Injective residualMatrix.mulVec
  residualPrecision_posDef : residualPrecision.PosDef

section Bayesian

variable {Latent Residual : Type*}
  [Fintype Latent] [DecidableEq Latent]
  [Fintype Residual] [DecidableEq Residual]

/-- Euclidean latent-coordinate space. -/
abbrev LinearGaussianOperatorSpace (Latent : Type*) [Fintype Latent] :=
  EuclideanSpace ℝ Latent

/-- Affine residual `A u + c`. -/
noncomputable def LinearGaussianOperatorModel.residual
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) : Residual → ℝ :=
  model.residualMatrix.mulVec (fun i => u i) + model.residualOffset

/-- Posterior precision `Aᵀ Λ A`. -/
noncomputable def LinearGaussianOperatorModel.posteriorPrecision
    (model : LinearGaussianOperatorModel Latent Residual) :
    Matrix Latent Latent ℝ :=
  model.residualMatrix.transpose * model.residualPrecision * model.residualMatrix

/-- Natural parameter `-Aᵀ Λ c`. -/
noncomputable def LinearGaussianOperatorModel.naturalParameter
    (model : LinearGaussianOperatorModel Latent Residual) : Latent → ℝ :=
  -(model.residualMatrix.transpose.mulVec
    (model.residualPrecision.mulVec model.residualOffset))

/-- Canonical conditional posterior mean `(Aᵀ Λ A)⁻¹(-Aᵀ Λ c)`. -/
noncomputable def LinearGaussianOperatorModel.posteriorMean
    (model : LinearGaussianOperatorModel Latent Residual) :
    LinearGaussianOperatorSpace Latent :=
  WithLp.toLp 2 (model.posteriorPrecision⁻¹.mulVec model.naturalParameter)

/-- Conditional multivariate Gaussian induced by the affine residual energy. -/
noncomputable def LinearGaussianOperatorModel.posterior
    (model : LinearGaussianOperatorModel Latent Residual) :
    Measure (LinearGaussianOperatorSpace Latent) :=
  multivariateGaussian model.posteriorMean model.posteriorPrecision⁻¹

/-- Precision-weighted residual energy. -/
noncomputable def LinearGaussianOperatorModel.energy
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) : ℝ :=
  model.residual u ⬝ᵥ model.residualPrecision.mulVec (model.residual u)

/-- Energy equilibrium in unconstrained latent coordinates. -/
def LinearGaussianOperatorModel.Equilibrium
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) : Prop :=
  IsMinOn model.energy univ u

theorem LinearGaussianOperatorModel.posteriorPrecision_posDef
    (model : LinearGaussianOperatorModel Latent Residual) :
    model.posteriorPrecision.PosDef := by
  have h := model.residualPrecision_posDef.conjTranspose_mul_mul_same
    model.residualMatrix_injective
  simpa [LinearGaussianOperatorModel.posteriorPrecision] using h

theorem LinearGaussianOperatorModel.posterior_covariance_posDef
    (model : LinearGaussianOperatorModel Latent Residual) :
    model.posteriorPrecision⁻¹.PosDef :=
  model.posteriorPrecision_posDef.inv

/-- The posterior integral has the independently defined canonical mean. -/
theorem LinearGaussianOperatorModel.posterior_integral_id
    (model : LinearGaussianOperatorModel Latent Residual) :
    ∫ u, u ∂model.posterior = model.posteriorMean := by
  exact integral_id_multivariateGaussian

theorem LinearGaussianOperatorModel.precision_mul_posteriorMean
    (model : LinearGaussianOperatorModel Latent Residual) :
    model.posteriorPrecision.mulVec (fun i => model.posteriorMean i) =
      model.naturalParameter := by
  have hunit : IsUnit model.posteriorPrecision :=
    model.posteriorPrecision_posDef.isUnit
  have hdet : IsUnit model.posteriorPrecision.det :=
    (Matrix.isUnit_iff_isUnit_det model.posteriorPrecision).mp hunit
  change model.posteriorPrecision.mulVec
      (model.posteriorPrecision⁻¹.mulVec model.naturalParameter) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv model.posteriorPrecision hdet,
    Matrix.one_mulVec]

/-- The canonical mean makes the residual force `Aᵀ Λ r` vanish. -/
theorem LinearGaussianOperatorModel.posteriorMean_stationary
    (model : LinearGaussianOperatorModel Latent Residual) :
    model.residualMatrix.transpose.mulVec
        (model.residualPrecision.mulVec (model.residual model.posteriorMean)) = 0 := by
  let A := model.residualMatrix
  let Λ := model.residualPrecision
  let c := model.residualOffset
  let m := model.posteriorMean
  have hsolve := model.precision_mul_posteriorMean
  have hfirst : A.transpose.mulVec (Λ.mulVec (A.mulVec (fun i => m i))) =
      model.posteriorPrecision.mulVec (fun i => m i) := by
    simp [A, Λ, LinearGaussianOperatorModel.posteriorPrecision,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  change A.transpose.mulVec (Λ.mulVec (A.mulVec (fun i => m i) + c)) = 0
  rw [Matrix.mulVec_add, Matrix.mulVec_add, hfirst, hsolve]
  simp [LinearGaussianOperatorModel.naturalParameter, A, Λ, c]

theorem LinearGaussianOperatorModel.precision_dot_swap
    (model : LinearGaussianOperatorModel Latent Residual)
    (a b : Residual → ℝ) :
    a ⬝ᵥ model.residualPrecision.mulVec b =
      b ⬝ᵥ model.residualPrecision.mulVec a := by
  have hsym : model.residualPrecision.transpose = model.residualPrecision := by
    ext i j
    have h := model.residualPrecision_posDef.isHermitian.apply i j
    simpa using h
  calc
    a ⬝ᵥ model.residualPrecision.mulVec b =
        a ⬝ᵥ model.residualPrecision.transpose.mulVec b := by rw [hsym]
    _ = b ⬝ᵥ model.residualPrecision.mulVec a :=
      Matrix.dotProduct_transpose_mulVec model.residualPrecision a b

theorem LinearGaussianOperatorModel.posteriorPrecision_quadratic
    (model : LinearGaussianOperatorModel Latent Residual)
    (d : Latent → ℝ) :
    d ⬝ᵥ model.posteriorPrecision.mulVec d =
      model.residualMatrix.mulVec d ⬝ᵥ
        model.residualPrecision.mulVec (model.residualMatrix.mulVec d) := by
  unfold LinearGaussianOperatorModel.posteriorPrecision
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Exact operator-level completion of squares around the posterior mean. -/
theorem LinearGaussianOperatorModel.energy_sub_posteriorMean
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) :
    model.energy u - model.energy model.posteriorMean =
      (fun i => u i - model.posteriorMean i) ⬝ᵥ
        model.posteriorPrecision.mulVec
          (fun i => u i - model.posteriorMean i) := by
  let A := model.residualMatrix
  let Λ := model.residualPrecision
  let m := model.posteriorMean
  let d : Latent → ℝ := fun i => u i - m i
  let r := model.residual m
  have hr : model.residual u = r + A.mulVec d := by
    change A.mulVec (fun i => u i) + model.residualOffset =
      (A.mulVec (fun i => m i) + model.residualOffset) + A.mulVec d
    have hu : (fun i => u i) = (fun i => m i) + d := by
      funext i
      simp [d]
    rw [hu, Matrix.mulVec_add]
    abel
  have hstation := model.posteriorMean_stationary
  change A.transpose.mulVec (Λ.mulVec r) = 0 at hstation
  have hcross : A.mulVec d ⬝ᵥ Λ.mulVec r = 0 := by
    calc
      A.mulVec d ⬝ᵥ Λ.mulVec r =
          d ⬝ᵥ A.transpose.mulVec (Λ.mulVec r) := by
            symm
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = 0 := by rw [hstation, dotProduct_zero]
  have hcross' : r ⬝ᵥ Λ.mulVec (A.mulVec d) = 0 := by
    rw [model.precision_dot_swap r (A.mulVec d), hcross]
  unfold LinearGaussianOperatorModel.energy
  rw [hr]
  change (r + A.mulVec d) ⬝ᵥ Λ.mulVec (r + A.mulVec d) -
      r ⬝ᵥ Λ.mulVec r =
    d ⬝ᵥ model.posteriorPrecision.mulVec d
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    hcross, hcross', add_zero, zero_add]
  rw [model.posteriorPrecision_quadratic d]
  ring

theorem LinearGaussianOperatorModel.posteriorMean_isMinOn
    (model : LinearGaussianOperatorModel Latent Residual) :
    IsMinOn model.energy univ model.posteriorMean := by
  intro u _hu
  have hdiff := model.energy_sub_posteriorMean u
  have hnonneg := model.posteriorPrecision_posDef.posSemidef
    |>.dotProduct_mulVec_nonneg (fun i => u i - model.posteriorMean i)
  have hnonneg' : 0 ≤
      (fun i => u i - model.posteriorMean i) ⬝ᵥ
        model.posteriorPrecision.mulVec
          (fun i => u i - model.posteriorMean i) := by
    simpa using hnonneg
  change model.energy model.posteriorMean ≤ model.energy u
  apply sub_nonneg.mp
  rw [hdiff]
  exact hnonneg'

/-- The positive-definite operator energy has no equilibrium except its
posterior mean. -/
theorem LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) :
    model.Equilibrium u ↔ u = model.posteriorMean := by
  constructor
  · intro hu
    have hle := (isMinOn_univ_iff.mp hu) model.posteriorMean
    have hge := (isMinOn_univ_iff.mp model.posteriorMean_isMinOn) u
    have henergy : model.energy u = model.energy model.posteriorMean :=
      le_antisymm hle hge
    have hcompletion := model.energy_sub_posteriorMean u
    have hquad :
        (fun i => u i - model.posteriorMean i) ⬝ᵥ
          model.posteriorPrecision.mulVec
            (fun i => u i - model.posteriorMean i) = 0 := by
      linarith
    have hdiff : (fun i => u i - model.posteriorMean i) = 0 := by
      by_contra hne
      have hpos := model.posteriorPrecision_posDef.dotProduct_mulVec_pos hne
      have hpos' : 0 <
          (fun i => u i - model.posteriorMean i) ⬝ᵥ
            model.posteriorPrecision.mulVec
              (fun i => u i - model.posteriorMean i) := by
        simpa using hpos
      rw [hquad] at hpos'
      exact (lt_irrefl 0) hpos'
    apply PiLp.ext
    intro i
    have hi := congrFun hdiff i
    simpa using sub_eq_zero.mp hi
  · rintro rfl
    exact model.posteriorMean_isMinOn

/-- Operator-level Bayesian crown: energy equilibrium is exactly equality
with the conditional multivariate-Gaussian posterior mean. -/
theorem LinearGaussianOperatorModel.equilibrium_iff_eq_conditionalPosteriorMean
    (model : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) :
    model.Equilibrium u ↔ u = ∫ v, v ∂model.posterior := by
  rw [model.posterior_integral_id]
  exact model.equilibrium_iff_eq_posteriorMean u

end Bayesian

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
