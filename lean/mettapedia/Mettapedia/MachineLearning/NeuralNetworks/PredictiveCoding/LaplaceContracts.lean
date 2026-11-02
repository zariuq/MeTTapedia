import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.EPCChartDescent
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.RankedDAGTensorSubstitution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Laplace approximation: values, coordinates and learning derivatives

A Laplace value and the derivative of that value have different preservation
obligations. A stationary energy removes the mode-motion term from the energy,
not generally from log curvature. The nonlinear example below has an exact
Laplace integral but a biased mode-held learning derivative.

The convention is negative log evidence, with the volume correction
`(log det H)/2 - (d/2) log(2π)`. Classical background: Tierney and Kadane,
*Accurate Approximations for Posterior Moments and Marginal Densities*, JASA
81 (1986), 82–86, DOI 10.1080/01621459.1986.10478240.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LaplaceContracts
open MeasureTheory Real Matrix
open scoped NNReal ENNReal

noncomputable def energy (θ u v : ℝ) : ℝ := (u^2 + (v + u^2/2 - θ)^2)/2
noncomputable def density (θ : ℝ) (z : ℝ × ℝ) : ℝ := Real.exp (-energy θ z.1 z.2)

theorem energy_nonnegative (θ u v : ℝ) : 0 ≤ energy θ u v := by unfold energy; positivity

theorem energy_zero_iff (θ u v : ℝ) : energy θ u v = 0 ↔ u = 0 ∧ v = θ := by
  unfold energy
  constructor
  · intro h
    have hu : u = 0 := by nlinarith [sq_nonneg (v+u^2/2-θ), sq_nonneg u]
    subst u
    constructor
    · rfl
    · nlinarith [sq_nonneg (v-θ)]
  · rintro ⟨rfl, rfl⟩; ring

theorem unique_mode (θ : ℝ) :
    (∀ u v, energy θ 0 θ ≤ energy θ u v) ∧
    (∀ u v, energy θ u v = energy θ 0 θ → u = 0 ∧ v = θ) := by
  have zero : energy θ 0 θ = 0 := by norm_num [energy]
  simp only [zero]
  exact ⟨energy_nonnegative θ, fun u v => (energy_zero_iff θ u v).mp⟩

theorem gaussian_shift_integral (a : ℝ) :
    (∫ x : ℝ, Real.exp (-(x-a)^2/2)) = Real.sqrt (2*Real.pi) := by
  rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-x^2/2)) a]
  have eq : (fun x : ℝ => Real.exp (-x^2/2)) = fun x => Real.exp (-(1/2 : ℝ)*x^2) := by
    funext x; congr 1; ring
  rw [eq, integral_gaussian]
  congr 1
  ring

theorem density_factor (θ u v : ℝ) : density θ (u,v) =
    Real.exp (-u^2/2) * Real.exp (-(v-(θ-u^2/2))^2/2) := by
  rw [← Real.exp_add]
  unfold density energy
  congr 1
  ring

theorem inner_integral (θ u : ℝ) :
    (∫ v : ℝ, density θ (u,v)) = Real.exp (-u^2/2) * Real.sqrt (2*Real.pi) := by
  simp_rw [density_factor]
  rw [integral_const_mul, gaussian_shift_integral]

theorem density_integrable (θ : ℝ) : Integrable (density θ) (volume.prod volume) := by
  apply (integrable_prod_iff (by unfold density energy; fun_prop)).mpr
  constructor
  · apply ae_of_all
    intro u
    have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).comp_sub_right (θ-u^2/2)
    have eq : (fun v => density θ (u,v)) =
        fun v => Real.exp (-u^2/2) * Real.exp (-(1/2 : ℝ)*(v-(θ-u^2/2))^2) := by
      funext v; rw [density_factor]; congr 2; ring
    rw [eq]
    exact h.const_mul _
  · have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).mul_const (Real.sqrt (2*Real.pi))
    have eq : (fun u => ∫ v : ℝ, ‖density θ (u,v)‖) =
        fun u => Real.exp (-(1/2 : ℝ)*u^2) * Real.sqrt (2*Real.pi) := by
      funext u
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), density]
      change (∫ v : ℝ, density θ (u,v)) = _
      rw [inner_integral]
      congr 2; ring
    rw [eq]
    exact h

/-- The actual two-dimensional integral is constant, not an assumed normalizer. -/
theorem normalizer (θ : ℝ) : (∫ z : ℝ × ℝ, density θ z ∂volume.prod volume) = 2*Real.pi := by
  rw [integral_prod _ (density_integrable θ)]
  simp_rw [inner_integral]
  rw [integral_mul_const]
  have h := gaussian_shift_integral 0
  simp only [sub_zero] at h
  rw [h, Real.mul_self_sqrt (by positivity)]

/-- The exact normalized density is a probability density. -/
theorem normalized_density (θ : ℝ) :
    (∫ z : ℝ × ℝ, density θ z / (2*Real.pi) ∂volume.prod volume) = 1 := by
  rw [integral_div, normalizer, div_self (by positivity)]

theorem energy_du (θ u v : ℝ) :
    HasDerivAt (fun x => energy θ x v) (u + (v+u^2/2-θ)*u) u := by
  have hr : HasDerivAt (fun x : ℝ => v+x^2/2-θ) u u := by
    apply (((((hasDerivAt_id u).pow 2).div_const 2).const_add v).sub_const θ).congr_deriv
    norm_num
  apply ((((hasDerivAt_id u).pow 2).add (hr.pow 2)).div_const 2).congr_deriv
  norm_num; ring

theorem energy_dv (θ u v : ℝ) : HasDerivAt (fun y => energy θ u y) (v+u^2/2-θ) v := by
  have hr := ((hasDerivAt_id v).add_const (u^2/2)).sub_const θ
  apply (((hr.pow 2).const_add (u^2)).div_const 2).congr_deriv
  norm_num

theorem energy_dθ (θ u v : ℝ) : HasDerivAt (fun t => energy t u v) (-(v+u^2/2-θ)) θ := by
  have hr := (hasDerivAt_const θ (v+u^2/2)).sub (hasDerivAt_id θ)
  apply (((hr.pow 2).const_add (u^2)).div_const 2).congr_deriv
  norm_num; ring

noncomputable def hessian (θ u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deriv (fun x => deriv (fun a => energy θ a v) x) u,
     deriv (fun y => deriv (fun a => energy θ a y) u) v;
     deriv (fun x => deriv (fun b => energy θ x b) v) u,
     deriv (fun y => deriv (fun b => energy θ u b) y) v]

theorem hessian_formula (θ u v : ℝ) : hessian θ u v = !![1+v-θ+3*u^2/2, u; u, 1] := by
  have hr : HasDerivAt (fun x : ℝ => v+x^2/2-θ) u u := by
    apply (((((hasDerivAt_id u).pow 2).div_const 2).const_add v).sub_const θ).congr_deriv
    norm_num
  have huu : HasDerivAt (fun x : ℝ => x + (v+x^2/2-θ)*x)
      (1 + (u*u + (v+u^2/2-θ)*1)) u :=
    (hasDerivAt_id u).add (hr.mul (hasDerivAt_id u))
  have huv := (((hasDerivAt_id v).add_const (u^2/2)).sub_const θ).mul_const u |>.const_add u
  have hvv := ((hasDerivAt_id v).add_const (u^2/2)).sub_const θ
  dsimp only [id_eq, Pi.add_apply, Pi.mul_apply] at huu huv hvv
  simp only [hessian, fun x => (energy_du θ x v).deriv, fun y => (energy_du θ u y).deriv,
    fun x => (energy_dv θ x v).deriv, fun y => (energy_dv θ u y).deriv,
    huu.deriv, huv.deriv, hr.deriv, hvv.deriv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

theorem hessian_det (θ u v : ℝ) : (hessian θ u v).det = 1+v-θ+u^2/2 := by
  rw [hessian_formula, Matrix.det_fin_two]
  simp
  ring

theorem mode_hessian (θ : ℝ) : hessian θ 0 θ = 1 := by
  rw [hessian_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

noncomputable def laplaceObjective (θ u v : ℝ) : ℝ :=
  energy θ u v + Real.log (hessian θ u v).det / 2 - Real.log (2*Real.pi)

theorem laplace_exact (θ : ℝ) : laplaceObjective θ 0 θ =
    -Real.log (∫ z : ℝ × ℝ, density θ z ∂volume.prod volume) := by
  simp [laplaceObjective, normalizer, energy, mode_hessian]

theorem mode_held_gradient (θ : ℝ) :
    HasDerivAt (fun t => laplaceObjective t 0 θ) (-(1/2)) θ := by
  have he := energy_dθ θ 0 θ
  norm_num at he
  have hd : HasDerivAt (fun t => (hessian t 0 θ).det) (-1) θ := by
    simpa [hessian_det] using
      (hasDerivAt_id θ).const_sub (1+θ)
  have hn : (hessian θ 0 θ).det ≠ 0 := by simp [mode_hessian]
  apply ((he.add ((hd.log hn).div_const 2)).sub_const (Real.log (2*Real.pi))).congr_deriv
  norm_num [mode_hessian]

theorem full_gradient (θ : ℝ) : HasDerivAt (fun t => laplaceObjective t 0 t) 0 θ := by
  have eq : (fun t => laplaceObjective t 0 t) = fun _ => -Real.log (2*Real.pi) := by
    funext t; rw [laplace_exact, normalizer]
  rw [eq]
  exact hasDerivAt_const _ _

section GeneralCalculus
variable {V U : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Full differentiation of Laplace's objective at a stationary energy. The
curvature can be the Hessian or another explicitly declared approximation. -/
theorem laplace_chain_rule {n : Nat} (E : ℝ × V → ℝ)
    (H : ℝ × V → Matrix (Fin n) (Fin n) ℝ) (mode : ℝ → V) (θ : ℝ)
    (eθ hθ : ℝ) (hz : V →L[ℝ] ℝ) (velocity : V) (constant : ℝ)
    (he : HasFDerivAt E (eθ • ContinuousLinearMap.fst ℝ ℝ V) (θ, mode θ))
    (hh : HasFDerivAt (fun p => Real.log (H p).det)
      (hθ • ContinuousLinearMap.fst ℝ ℝ V + hz.comp (ContinuousLinearMap.snd ℝ ℝ V)) (θ, mode θ))
    (hm : HasDerivAt mode velocity θ) :
    HasDerivAt (fun t => E (t,mode t) + Real.log (H (t,mode t)).det / 2 - constant)
      (eθ + hθ/2 + hz velocity / 2) θ := by
  have path := (hasDerivAt_id θ).prodMk hm
  have he' := he.comp_hasDerivAt θ path
  have hh' := hh.comp_hasDerivAt θ path
  apply ((he'.add (hh'.div_const 2)).sub_const constant).congr_deriv
  simp
  ring

/-- At a critical point the second-derivative chain rule loses its chart
curvature term. This is derived from the actual Fréchet derivatives. -/
theorem hessian_pullback_at_critical (chart : U → V) (E : V → ℝ) (x : U)
    (hc : Differentiable ℝ chart) (he : Differentiable ℝ E)
    (hc2 : DifferentiableAt ℝ (fderiv ℝ chart) x)
    (he2 : DifferentiableAt ℝ (fderiv ℝ E) (chart x))
    (stationary : fderiv ℝ E (chart x) = 0) (u v : U) :
    fderiv ℝ (fderiv ℝ (E ∘ chart)) x u v =
      fderiv ℝ (fderiv ℝ E) (chart x) (fderiv ℝ chart x u) (fderiv ℝ chart x v) := by
  have first : fderiv ℝ (E ∘ chart) = fun y => (fderiv ℝ E (chart y)).comp (fderiv ℝ chart y) := by
    funext y
    exact fderiv_comp y (he _) (hc _)
  have hcomp : DifferentiableAt ℝ (fun y => fderiv ℝ E (chart y)) x := he2.comp x (hc x)
  have second : fderiv ℝ (fun y => fderiv ℝ E (chart y)) x =
      (fderiv ℝ (fderiv ℝ E) (chart x)).comp (fderiv ℝ chart x) :=
    fderiv_comp x he2 (hc x)
  rw [first, fderiv_clm_comp hcomp hc2, second]
  simp [stationary, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

/-- Global minima transport under a bijection of the state space. This does
not assert equality of gradient trajectories. -/
theorem minimum_transport {X Y : Type} (chart : X ≃ Y) (E : Y → ℝ) (x : X) :
    (∀ y, E (chart x) ≤ E (chart y)) ↔ ∀ z, E (chart x) ≤ E z := by
  constructor
  · intro h z; simpa using h (chart.symm z)
  · intro h y; exact h (chart y)

theorem hessian_determinant_transport {n : Type} [Fintype n] [DecidableEq n]
    (H J : Matrix n n ℝ) (volume : J.det = 1) :
    (J.transpose * H * J).det = H.det := by simp [Matrix.det_mul, Matrix.det_transpose, volume]

end GeneralCalculus

section FiniteCoordinates
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinate matrix of the actual second Fréchet derivative. -/
noncomputable def coordinateHessian (E : (ι → ℝ) → ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ E) x (Pi.single i 1) (Pi.single j 1)

noncomputable def coordinateJacobian (chart : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ chart x (Pi.single j 1) i

theorem bilinear_coordinates (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (u v : ι → ℝ) :
    B u v = ∑ i, ∑ j, u i * B (Pi.single i 1) (Pi.single j 1) * v j := by
  have expand (w : ι → ℝ) : w = ∑ i, w i • Pi.single i 1 := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [expand u, expand v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix congruence is obtained from the differentiated chart, rather than
supplied as a transformation certificate. -/
theorem coordinateHessian_transport (chart : (ι → ℝ) → (ι → ℝ)) (E : (ι → ℝ) → ℝ) (x : ι → ℝ)
    (hc : Differentiable ℝ chart) (he : Differentiable ℝ E)
    (hc2 : DifferentiableAt ℝ (fderiv ℝ chart) x)
    (he2 : DifferentiableAt ℝ (fderiv ℝ E) (chart x))
    (stationary : fderiv ℝ E (chart x) = 0) :
    coordinateHessian (E ∘ chart) x =
      (coordinateJacobian chart x).transpose * coordinateHessian E (chart x) * coordinateJacobian chart x := by
  ext i j
  rw [coordinateHessian, hessian_pullback_at_critical chart E x hc he hc2 he2 stationary]
  rw [bilinear_coordinates]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coordinateJacobian, coordinateHessian,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The stationary Laplace value is invariant under a unit-volume chart.
The determinant premise is on the actual first derivative. -/
theorem laplace_value_transport (chart : (ι → ℝ) → (ι → ℝ)) (E : (ι → ℝ) → ℝ) (x : ι → ℝ)
    (hc : Differentiable ℝ chart) (he : Differentiable ℝ E)
    (hc2 : DifferentiableAt ℝ (fderiv ℝ chart) x)
    (he2 : DifferentiableAt ℝ (fderiv ℝ E) (chart x))
    (stationary : fderiv ℝ E (chart x) = 0)
    (volume : (coordinateJacobian chart x).det = 1) :
    (E ∘ chart) x + Real.log (coordinateHessian (E ∘ chart) x).det / 2 =
      E (chart x) + Real.log (coordinateHessian E (chart x)).det / 2 := by
  rw [coordinateHessian_transport chart E x hc he hc2 he2 stationary,
    hessian_determinant_transport _ _ volume]
  rfl

/-- A nondegenerate minimum remains admissible for the ordinary Laplace
approximation. This supplies the positivity condition for the log-curvature
identity above; a generic stationary saddle is not a Gaussian mode. -/
theorem laplace_admissibility_transport (chart : (ι → ℝ) → (ι → ℝ)) (E : (ι → ℝ) → ℝ) (x : ι → ℝ)
    (hc : Differentiable ℝ chart) (he : Differentiable ℝ E)
    (hc2 : DifferentiableAt ℝ (fderiv ℝ chart) x)
    (he2 : DifferentiableAt ℝ (fderiv ℝ E) (chart x))
    (stationary : fderiv ℝ E (chart x) = 0)
    (invertible : IsUnit (coordinateJacobian chart x).det)
    (positive : (coordinateHessian E (chart x)).PosDef) :
    (coordinateHessian (E ∘ chart) x).PosDef := by
  rw [coordinateHessian_transport chart E x hc he hc2 he2 stationary]
  have injective := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr invertible)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    positive.conjTranspose_mul_mul_same injective

omit [DecidableEq ι] in
/-- Measure transport is a separate obligation from local Hessian transport.
Once discharged, it preserves every nonnegative unnormalized query mass. -/
theorem density_observation_transport (chart : (ι → ℝ) → (ι → ℝ))
    (preserves : MeasurePreserving chart volume volume)
    (p f : (ι → ℝ) → ℝ≥0∞) (hp : Measurable p) (hf : Measurable f) :
    (∫⁻ x, p (chart x) * f (chart x)) = ∫⁻ x, p x * f x :=
  preserves.lintegral_comp (hp.mul hf)

end FiniteCoordinates

section RankedGraphs
variable {Node Edge Coord : Type} [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]

/-- The existing ranked graph's nilpotence proves unit Jacobian determinant;
this is not an extra volume-preservation assertion on the model. -/
theorem ranked_error_det (G : RankedDAGTensor Node Edge Coord) :
    (rankedDAGErrorJacobianMatrix G).det = 1 := by
  have hn : IsNilpotent (rankedDAGFeedforwardMatrix G) :=
    ⟨_, rankedDAGFeedforwardMatrix_nilpotent G⟩
  have hp := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hn).eq_zero
  have hv := congrArg (Polynomial.eval (1 : ℝ)) (sub_eq_zero.mp hp)
  simpa [Matrix.eval_charpoly, rankedDAGErrorJacobianMatrix] using hv

theorem ranked_inverse_det (G : RankedDAGTensor Node Edge Coord) :
    (rankedDAGResolventMatrix G).det = 1 := by
  have h := congrArg Matrix.det (rankedDAG_resolvent_mul_errorJacobian G)
  simpa [Matrix.det_mul, ranked_error_det] using h

theorem ranked_actual_jacobian (G : RankedDAGTensor Node Edge Coord) (x : Coord → ℝ) :
    coordinateJacobian (rankedDAGErrorToState G) x = rankedDAGResolventMatrix G := by
  ext i j
  simp [coordinateJacobian, (rankedDAGErrorToState_hasFDerivAt G x).fderiv,
    rankedDAGInverseJacobian, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ranked_preserves_volume (G : RankedDAGTensor Node Edge Coord) :
    MeasurePreserving (rankedDAGErrorToState G) volume volume := by
  have hl : MeasurePreserving (Matrix.toLin' (rankedDAGResolventMatrix G)) volume volume := by
    constructor
    · exact (rankedDAGInverseJacobian G).continuous.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [ranked_inverse_det]; norm_num)]
      simp [ranked_inverse_det]
  exact hl.comp (measurePreserving_add_right volume G.offset)

/-- Stationary Laplace values for the established finite ranked-DAG chart. -/
theorem ranked_laplace_transport (G : RankedDAGTensor Node Edge Coord)
    (E : (Coord → ℝ) → ℝ) (x : Coord → ℝ) (he : Differentiable ℝ E)
    (he2 : DifferentiableAt ℝ (fderiv ℝ E) (rankedDAGErrorToState G x))
    (stationary : fderiv ℝ E (rankedDAGErrorToState G x) = 0) :
    (E ∘ rankedDAGErrorToState G) x +
        Real.log (coordinateHessian (E ∘ rankedDAGErrorToState G) x).det / 2 =
      E (rankedDAGErrorToState G x) +
        Real.log (coordinateHessian E (rankedDAGErrorToState G x)).det / 2 := by
  have hc2 : DifferentiableAt ℝ (fderiv ℝ (rankedDAGErrorToState G)) x := by
    have eq : fderiv ℝ (rankedDAGErrorToState G) = fun _ => rankedDAGInverseJacobian G :=
      funext (fun y => (rankedDAGErrorToState_hasFDerivAt G y).fderiv)
    rw [eq]
    exact differentiableAt_const _
  exact laplace_value_transport _ _ _
    (fun y => (rankedDAGErrorToState_hasFDerivAt G y).differentiableAt) he hc2 he2 stationary
    (by rw [ranked_actual_jacobian, ranked_inverse_det])

end RankedGraphs

/-- A nonlinear triangular chart and its actual inverse. -/
noncomputable def shear : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun z := (z.1, z.2+z.1^2/2)
  invFun z := (z.1, z.2-z.1^2/2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

theorem shear_preserves_volume : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
  apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product (g := fun x y : ℝ => y+x^2/2)
  · fun_prop
  · apply Filter.Eventually.of_forall
    intro x
    exact map_add_right_eq_self volume (x^2/2)

/-- Unnormalized query masses transport, not just the normalizing constant. -/
theorem shear_density_observation (p : ℝ × ℝ → ℝ≥0∞) (f : ℝ × ℝ → ℝ≥0∞)
    (hp : Measurable p) (hf : Measurable f) :
    (∫⁻ z, p (shear z) * f (shear z) ∂volume.prod volume) =
      ∫⁻ z, p z * f z ∂volume.prod volume :=
  shear_preserves_volume.lintegral_comp (hp.mul hf)

noncomputable def shearDerivative (u : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ + u • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem shear_hasFDerivAt (z : ℝ × ℝ) : HasFDerivAt shear (shearDerivative z.1) z := by
  have hfst := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)
  have hsnd := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)
  have h := hfst.prodMk (hsnd.add ((hfst.pow 2).mul_const (1/2)))
  have hd : HasFDerivAt (fun x : ℝ × ℝ => (x.1, x.2+x.1^2*(1/2)))
      (shearDerivative z.1) z := by
    apply h.congr_fderiv
    ext <;> simp [shearDerivative]
  change HasFDerivAt (fun x : ℝ × ℝ => (x.1, x.2+x.1^2/2)) _ z
  simpa only [div_eq_mul_inv, one_mul] using hd

noncomputable def shearJacobian (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(shearDerivative u (1,0)).1, (shearDerivative u (0,1)).1;
     (shearDerivative u (1,0)).2, (shearDerivative u (0,1)).2]

theorem shearJacobian_det (u : ℝ) : (shearJacobian u).det = 1 := by
  simp [shearJacobian, shearDerivative, Matrix.det_fin_two]

/-- The computed Hessian is the chart pullback plus a term proportional to
the residual. That term vanishes at the actual mode. -/
theorem hessian_shear (θ u v : ℝ) :
    hessian θ u v = (shearJacobian u).transpose * shearJacobian u +
      !![v+u^2/2-θ, 0; 0, 0] := by
  rw [hessian_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearJacobian, shearDerivative, Matrix.mul_apply, Fin.sum_univ_two]
  ring

noncomputable def stateEnergy (θ : ℝ) (z : ℝ × ℝ) : ℝ := (z.1^2+(z.2-θ)^2)/2

theorem energy_is_pullback (θ u v : ℝ) : energy θ u v = stateEnergy θ (shear (u,v)) := rfl

/-- Explicit Euler steps use the actual coordinate derivatives. -/
noncomputable def coordinateStep (E : ℝ × ℝ → ℝ) (η : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1-η*deriv (fun x => E (x,z.2)) z.1, z.2-η*deriv (fun y => E (z.1,y)) z.2)

theorem stateEnergy_du (θ u v : ℝ) : HasDerivAt (fun x => stateEnergy θ (x,v)) u u := by
  apply ((((hasDerivAt_id u).pow 2).add_const ((v-θ)^2)).div_const 2).congr_deriv
  norm_num

theorem stateEnergy_dv (θ u v : ℝ) : HasDerivAt (fun y => stateEnergy θ (u,y)) (v-θ) v := by
  apply (((((hasDerivAt_id v).sub_const θ).pow 2).const_add (u^2)).div_const 2).congr_deriv
  norm_num

/-- Even a unit-volume, smooth, invertible change of coordinates does not
conjugate finite gradient steps. Both gradients here are differentiated. -/
theorem finite_steps_differ :
    coordinateStep (stateEnergy 0) 1 (shear (1,0)) = (0,0) ∧
    shear (coordinateStep (fun z => energy 0 z.1 z.2) 1 (1,0)) = (-(1/2), -(3/8)) ∧
    coordinateStep (stateEnergy 0) 1 (shear (1,0)) ≠
      shear (coordinateStep (fun z => energy 0 z.1 z.2) 1 (1,0)) := by
  have hs : coordinateStep (stateEnergy 0) 1 (shear (1,0)) = (0,0) := by
    simp only [coordinateStep, shear, Equiv.coe_fn_mk,
      (stateEnergy_du _ _ _).deriv, (stateEnergy_dv _ _ _).deriv]
    norm_num
  have he : shear (coordinateStep (fun z => energy 0 z.1 z.2) 1 (1,0)) =
      (-(1/2), -(3/8)) := by
    simp only [coordinateStep, (energy_du _ _ _).deriv, (energy_dv _ _ _).deriv]
    norm_num [shear]
  exact ⟨hs, he, by rw [hs, he]; norm_num⟩

section GaussianLearning

section OperatorCurvature
variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- Reuse completion of squares for the established rectangular residual
operator. The entire restriction to a line is a quadratic polynomial. -/
theorem operator_line_energy (model : LinearGaussianOperatorModel L R)
    (u v : LinearGaussianOperatorSpace L) (t : ℝ) :
    model.energy (u + t • v) / 2 =
      model.energy u / 2 + t / 2 *
        ((fun i => u i-model.posteriorMean i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => v i) +
          (fun i => v i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => u i-model.posteriorMean i)) +
      t^2 / 2 * ((fun i => v i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => v i)) := by
  have h := model.energy_sub_posteriorMean (u+t • v)
  have h0 := model.energy_sub_posteriorMean u
  have path : (fun i => (u+t • v) i-model.posteriorMean i) =
      (fun i => u i-model.posteriorMean i) + t • (fun i => v i) := by
    ext i
    simp
    ring
  rw [path, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  nlinarith only [h, h0]

/-- The actual second derivative along every direction is state-independent.
Consequently motion of the mode cannot create a missing curvature term in
this linear-Gaussian family. -/
theorem operator_line_curvature (model : LinearGaussianOperatorModel L R)
    (u v : LinearGaussianOperatorSpace L) (t : ℝ) :
    deriv (fun s => deriv (fun r => model.energy (u+r • v)/2) s) t =
      (fun i => v i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => v i) := by
  let b := (fun i => u i-model.posteriorMean i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => v i) +
    (fun i => v i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => u i-model.posteriorMean i)
  let q := (fun i => v i) ⬝ᵥ model.posteriorPrecision.mulVec (fun i => v i)
  have first (s : ℝ) : HasDerivAt (fun r => model.energy (u+r • v)/2) (b/2+s*q) s := by
    have eq : (fun r => model.energy (u+r • v)/2) =
        fun r => model.energy u/2 + r/2*b + r^2/2*q := funext (operator_line_energy model u v)
    rw [eq]
    apply (((((hasDerivAt_id s).div_const 2).mul_const b).const_add (model.energy u/2)).add
      ((((hasDerivAt_id s).pow 2).div_const 2).mul_const q)).congr_deriv
    norm_num
    ring
  simp only [fun s => (first s).deriv]
  change deriv (fun s : ℝ => b/2+s*q) t = q
  have hd : HasDerivAt (fun s : ℝ => b/2+s*q) q t := by
    simpa using ((hasDerivAt_id t).mul_const q).const_add (b/2)
  exact hd.deriv

end OperatorCurvature

noncomputable def gaussianEnergy (a m c x : ℝ) : ℝ := a/2*(x-m)^2+c

theorem gaussian_normalizer (a m c : ℝ) :
    (∫ x : ℝ, Real.exp (-gaussianEnergy a m c x)) =
      Real.exp (-c) * Real.sqrt (2*Real.pi/a) := by
  have eq : (fun x => Real.exp (-gaussianEnergy a m c x)) =
      fun x => Real.exp (-c) * Real.exp (-(a/2)*(x-m)^2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    unfold gaussianEnergy
    ring
  rw [eq, integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(a/2)*x^2)) m,
    integral_gaussian]
  congr 2
  ring

/-- The linear-Gaussian Laplace value is the actual log integral. -/
theorem gaussian_log_evidence (a m c : ℝ) (ha : 0 < a) :
    -Real.log (∫ x : ℝ, Real.exp (-gaussianEnergy a m c x)) =
      c + Real.log a / 2 - Real.log (2*Real.pi)/2 := by
  rw [gaussian_normalizer, Real.log_mul (Real.exp_ne_zero _) (by positivity),
    Real.log_exp, Real.log_sqrt (by positivity), Real.log_div (by positivity) ha.ne']
  ring

/-- The normalized energy density is the existing Gaussian density, with
variance equal to inverse precision. No new probability construction is used. -/
theorem gaussian_posterior_density (a m c x : ℝ) (ha : 0 < a) :
    Real.exp (-gaussianEnergy a m c x) /
        (∫ y : ℝ, Real.exp (-gaussianEnergy a m c y)) =
      ProbabilityTheory.gaussianPDFReal m ⟨a⁻¹, (inv_pos.mpr ha).le⟩ x := by
  rw [gaussian_normalizer, ProbabilityTheory.gaussianPDFReal_def]
  change Real.exp (-gaussianEnergy a m c x) / (Real.exp (-c) * Real.sqrt (2*Real.pi/a)) =
    (Real.sqrt (2*Real.pi*a⁻¹))⁻¹ * Real.exp (-(x-m)^2/(2*a⁻¹))
  have hexp : Real.exp (-gaussianEnergy a m c x) =
      Real.exp (-c) * Real.exp (-(x-m)^2/(2*a⁻¹)) := by
    rw [← Real.exp_add]
    congr 1
    unfold gaussianEnergy
    field_simp
    ring
  rw [hexp]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  simp only [div_eq_mul_inv]
  ring

theorem gaussian_normalized (a m c : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-gaussianEnergy a m c x) /
      (∫ y : ℝ, Real.exp (-gaussianEnergy a m c y))) = 1 := by
  simp_rw [gaussian_posterior_density a m c _ ha]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one _ (by
    apply ne_of_gt
    exact_mod_cast inv_pos.mpr ha)

/-- Parameter-dependent precision and offset may both be learned. Translation
of the Gaussian mean contributes no missing curvature term. -/
theorem gaussian_learning (a c mean : ℝ → ℝ) (θ da dc : ℝ)
    (ha : 0 < a θ) (hda : HasDerivAt a da θ) (hdc : HasDerivAt c dc θ) :
    HasDerivAt (fun t => -Real.log (∫ x : ℝ, Real.exp (-gaussianEnergy (a t) (mean t) (c t) x)))
      (dc + da/(2*a θ)) θ := by
  have derivative := (hdc.add ((hda.log ha.ne').div_const 2)).sub_const (Real.log (2*Real.pi)/2)
  have agrees : (fun t => -Real.log (∫ x : ℝ, Real.exp (-gaussianEnergy (a t) (mean t) (c t) x))) =ᶠ[nhds θ]
      (fun t => c t + Real.log (a t)/2 - Real.log (2*Real.pi)/2) := by
    filter_upwards [hda.continuousAt.eventually (lt_mem_nhds ha)] with t ht
    exact gaussian_log_evidence _ _ _ ht
  apply (derivative.congr_of_eventuallyEq agrees).congr_deriv
  ring

/-! A Gaussian latent variable and a Gaussian measurement. `a` is the positive
noise variance; logarithmic standard-deviation scores multiply `d/da` by `2a`. -/
noncomputable def noiseEnergy (e v a z : ℝ) : ℝ :=
  z^2/2 + (e-v*z)^2/(2*a) + Real.log a/2 + Real.log (2*Real.pi)
noncomputable def noiseMode (e v a : ℝ) : ℝ := v*e/(a+v^2)
noncomputable def noisePrecision (v a : ℝ) : ℝ := (a+v^2)/a

/-- Completing the square identifies the actual mode and precision. -/
theorem noise_complete_square (e v a z : ℝ) (ha : 0 < a) :
    noiseEnergy e v a z = gaussianEnergy (noisePrecision v a) (noiseMode e v a)
      (noiseEnergy e v a (noiseMode e v a)) z := by
  have hv : a+v^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg v))
  unfold noiseEnergy gaussianEnergy noisePrecision noiseMode
  field_simp [ha.ne', hv]
  ring

theorem noise_mode_minimizes (e v a z : ℝ) (ha : 0 < a) :
    noiseEnergy e v a (noiseMode e v a) ≤ noiseEnergy e v a z := by
  rw [noise_complete_square e v a z ha]
  unfold gaussianEnergy noisePrecision
  have hn : 0 ≤ (a+v^2)/a/2*(z-noiseMode e v a)^2 := by positivity
  linarith

theorem noise_partial (e v a z : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b => noiseEnergy e v b z)
      (1/(2*a) - (e-v*z)^2/(2*a^2)) a := by
  have hq := (hasDerivAt_const a ((e-v*z)^2)).div ((hasDerivAt_id a).const_mul 2) (by positivity)
  have hl := ((hasDerivAt_id a).log ha.ne').div_const 2
  apply (((hq.const_add (z^2/2)).add hl).add_const (Real.log (2*Real.pi))).congr_deriv
  simp only [id_eq]
  field_simp
  ring

noncomputable def localLogScaleScore (e v a : ℝ) : ℝ :=
  2*a*deriv (fun b => noiseEnergy e v b (noiseMode e v a)) a

theorem local_score_formula (e v a : ℝ) (ha : 0 < a) :
    localLogScaleScore e v a = 1-e^2*a/(a+v^2)^2 := by
  rw [localLogScaleScore, (noise_partial e v a _ ha).deriv]
  have hv : a+v^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg v))
  unfold noiseMode
  field_simp [ha.ne', hv]
  ring

theorem local_score_lower_bound (e v a : ℝ) (ha : 0 < a) (hv : v ≠ 0) :
    1-e^2/(4*v^2) ≤ localLogScaleScore e v a := by
  rw [local_score_formula e v a ha]
  have denom : 0 < (a+v^2)^2 := sq_pos_of_pos (add_pos_of_pos_of_nonneg ha (sq_nonneg v))
  have bound : e^2*a/(a+v^2)^2 ≤ e^2/(4*v^2) := by
    apply (div_le_div_iff₀ denom (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg (a-v^2))]
  linarith

noncomputable def noiseMarginalNLL (e v a : ℝ) : ℝ :=
  e^2/(2*(a+v^2)) + Real.log (a+v^2)/2 + Real.log (2*Real.pi)/2

/-- The marginal objective is derived from integrating the joint energy. -/
theorem noise_evidence (e v a : ℝ) (ha : 0 < a) :
    -Real.log (∫ z : ℝ, Real.exp (-noiseEnergy e v a z)) = noiseMarginalNLL e v a := by
  have eq : (fun z => Real.exp (-noiseEnergy e v a z)) = fun z =>
      Real.exp (-gaussianEnergy (noisePrecision v a) (noiseMode e v a)
        (noiseEnergy e v a (noiseMode e v a)) z) := by
    funext z
    rw [noise_complete_square e v a z ha]
  rw [eq]
  rw [gaussian_log_evidence _ _ _ (by unfold noisePrecision; positivity)]
  have hsum : 0 < a+v^2 := add_pos_of_pos_of_nonneg ha (sq_nonneg v)
  rw [noisePrecision, Real.log_div hsum.ne' ha.ne']
  unfold noiseEnergy noiseMode noiseMarginalNLL
  field_simp [ha.ne', hsum.ne']
  ring

theorem noise_marginal_derivative (e v a : ℝ) (ha : 0 < a) :
    HasDerivAt (noiseMarginalNLL e v)
      (1/(2*(a+v^2)) - e^2/(2*(a+v^2)^2)) a := by
  have hsum : 0 < a+v^2 := add_pos_of_pos_of_nonneg ha (sq_nonneg v)
  have hx := (hasDerivAt_id a).add_const (v^2)
  have hq := (hasDerivAt_const a (e^2)).div (hx.const_mul 2) (by positivity)
  have hl := (hx.log hsum.ne').div_const 2
  apply ((hq.add hl).add_const (Real.log (2*Real.pi)/2)).congr_deriv
  simp only [id_eq]
  field_simp
  ring

noncomputable def evidenceLogScaleScore (e v a : ℝ) : ℝ := 2*a*deriv (noiseMarginalNLL e v) a

theorem evidence_score_formula (e v a : ℝ) (ha : 0 < a) :
    evidenceLogScaleScore e v a = a*(a+v^2-e^2)/(a+v^2)^2 := by
  rw [evidenceLogScaleScore, (noise_marginal_derivative e v a ha).deriv]
  field_simp

theorem interior_stationary_iff (e v a : ℝ) (ha : 0 < a) :
    evidenceLogScaleScore e v a = 0 ↔ a = e^2-v^2 := by
  rw [evidence_score_formula e v a ha]
  have hsum : a+v^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg v))
  simp only [div_eq_zero_iff, mul_eq_zero, ha.ne', false_or, pow_ne_zero 2 hsum, or_false]
  constructor <;> intro h <;> linarith

theorem boundary_regime (e v a : ℝ) (ha : 0 < a) (small : e^2 ≤ v^2) :
    0 < evidenceLogScaleScore e v a := by
  rw [evidence_score_formula e v a ha]
  have hsum : 0 < a+v^2 := add_pos_of_pos_of_nonneg ha (sq_nonneg v)
  exact div_pos (mul_pos ha (by linarith)) (sq_pos_of_pos hsum)

/-- The evidence derivative differentiates the integral, not just a separately
declared surrogate objective. -/
theorem noise_integral_derivative (e v a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b => -Real.log (∫ z : ℝ, Real.exp (-noiseEnergy e v b z)))
      (1/(2*(a+v^2)) - e^2/(2*(a+v^2)^2)) a := by
  apply (noise_marginal_derivative e v a ha).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ha] with b hb
  exact noise_evidence e v b hb

/-- When the empirical squared residual exceeds the latent contribution, the
positive stationary variance is a global evidence optimum. -/
theorem interior_global_minimum (e v a : ℝ) (ha : 0 < a) (he : v^2 < e^2) :
    noiseMarginalNLL e v (e^2-v^2) ≤ noiseMarginalNLL e v a := by
  have hepos : 0 < e^2 := lt_of_le_of_lt (sq_nonneg v) he
  have hsum : 0 < a+v^2 := add_pos_of_pos_of_nonneg ha (sq_nonneg v)
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hsum hepos)
  rw [Real.log_div hsum.ne' hepos.ne'] at hl
  simp only [inv_div] at hl
  unfold noiseMarginalNLL
  have hcancel : e^2-v^2+v^2 = e^2 := by ring
  rw [hcancel]
  have heq : e^2/(2*e^2) = 1/2 := by
    rw [mul_comm 2, ← div_div, div_self hepos.ne']
  rw [heq]
  have hal : e^2/(2*(a+v^2)) = (e^2/(a+v^2))/2 := by rw [mul_comm 2, ← div_div]
  rw [hal]
  linarith

/-- A concrete regime separates the local scale update from evidence
learning: the local score stays positive even at the evidence optimum. -/
theorem noise_bias_control :
    (∀ a : ℝ, 0 < a → (7/16 : ℝ) ≤ localLogScaleScore (3/2) 1 a) ∧
    evidenceLogScaleScore (3/2) 1 (5/4) = 0 ∧
    localLogScaleScore (3/2) 1 (5/4) = 4/9 := by
  constructor
  · intro a ha
    convert local_score_lower_bound (3/2) 1 a ha (by norm_num) using 1
    norm_num
  · constructor
    · norm_num [evidence_score_formula (3/2) 1 (5/4) (by norm_num)]
    · norm_num [local_score_formula (3/2) 1 (5/4) (by norm_num)]

end GaussianLearning

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LaplaceContracts


