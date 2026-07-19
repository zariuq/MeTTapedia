import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.PreconditionedFlowTransport
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ResidualBoundary
import Mathlib.Probability.Independence.Integration

/-!
# Random residual cancellation at scalar width

The deterministic aligned stack with factors `1 + 1 / sqrt(L)` is unbounded,
while inverse-depth scaling is uniformly bounded by `exp 1`; both facts are
already checked in `ResidualBoundary`.  Here the missing random scalar case is
proved.  For independent centered residual increments `ξᵢ` with second moment
at most `σ²`, the product of factors `1 + ξᵢ / sqrt(L)` has mean one and second
moment at most `exp(σ²)`, uniformly in positive depth `L`.

The proof is finite-depth and exact.  Matrix-valued noncommutative extensions
remain a separate reproduction target.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- Scalar random residual multiplier at positive nominal depth. -/
noncomputable def centeredResidualProduct
    {Ω : Type*} (depth : ℕ) (increment : Fin depth → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.prod fun index : Fin depth =>
    1 + increment index ω / Real.sqrt depth

/-- One centered scaled residual factor has expectation one. -/
theorem centeredResidualFactor_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (increment : Ω → ℝ)
    (hintegrable : Integrable increment μ)
    (hcentered : ∫ ω, increment ω ∂μ = 0) :
    ∫ ω, (1 + increment ω / Real.sqrt depth) ∂μ = 1 := by
  rw [integral_add (integrable_const 1) (hintegrable.div_const _)]
  rw [integral_div, hcentered]
  simp

/-- Exact second moment of one centered scaled residual factor. -/
theorem centeredResidualFactor_sq_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (hdepth : 0 < depth) (increment : Ω → ℝ)
    (hintegrable : Integrable increment μ)
    (hsqIntegrable : Integrable (fun ω => increment ω ^ 2) μ)
    (hcentered : ∫ ω, increment ω ∂μ = 0) :
    ∫ ω, (1 + increment ω / Real.sqrt depth) ^ 2 ∂μ =
      1 + (∫ ω, increment ω ^ 2 ∂μ) / depth := by
  have hdepthReal : (0 : ℝ) < depth := by exact_mod_cast hdepth
  have hsqrtPos : 0 < Real.sqrt depth := Real.sqrt_pos.2 hdepthReal
  have hsqrtSq : (Real.sqrt depth) ^ 2 = (depth : ℝ) :=
    Real.sq_sqrt hdepthReal.le
  have hexpand : ∀ ω,
      (1 + increment ω / Real.sqrt depth) ^ 2 =
        1 + (2 / Real.sqrt depth) * increment ω +
          (1 / (depth : ℝ)) * increment ω ^ 2 := by
    intro ω
    field_simp [ne_of_gt hsqrtPos, ne_of_gt hdepthReal]
    nlinarith
  rw [integral_congr_ae (ae_of_all μ hexpand)]
  rw [show (fun ω =>
      1 + (2 / Real.sqrt depth) * increment ω +
        (1 / (depth : ℝ)) * increment ω ^ 2) =
      (fun ω => 1 + (2 / Real.sqrt depth) * increment ω) +
        (fun ω => (1 / (depth : ℝ)) * increment ω ^ 2) by rfl]
  have hfirst : Integrable
      (fun ω => 1 + (2 / Real.sqrt depth) * increment ω) μ :=
    (integrable_const 1).add (hintegrable.const_mul _)
  have hlast : Integrable
      (fun ω => (1 / (depth : ℝ)) * increment ω ^ 2) μ :=
    hsqIntegrable.const_mul _
  rw [integral_add' hfirst hlast]
  rw [show (fun ω => 1 + (2 / Real.sqrt depth) * increment ω) =
      (fun _ => 1) + (fun ω => (2 / Real.sqrt depth) * increment ω) by rfl]
  rw [integral_add' (integrable_const 1) (hintegrable.const_mul _)]
  rw [integral_const_mul, integral_const_mul, hcentered]
  simp
  ring

/-- Independence factorizes the mean of the whole scalar residual product. -/
theorem centeredResidualProduct_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (increment : Fin depth → Ω → ℝ)
    (hindependent : iIndepFun increment μ)
    (hintegrable : ∀ index, Integrable (increment index) μ)
    (hcentered : ∀ index, ∫ ω, increment index ω ∂μ = 0) :
    ∫ ω, centeredResidualProduct depth increment ω ∂μ = 1 := by
  have hfactorization :
      ∫ ω, ∏ index,
          (fun value : ℝ => 1 + value / Real.sqrt depth)
            (increment index ω) ∂μ =
        ∏ index, ∫ ω,
          (fun value : ℝ => 1 + value / Real.sqrt depth)
            (increment index ω) ∂μ := by
    exact hindependent.integral_fun_prod_comp
      (fun index => (hintegrable index).aemeasurable)
      (fun _ => (by fun_prop : Continuous
        (fun value : ℝ => 1 + value / Real.sqrt depth)).aestronglyMeasurable)
  calc
    ∫ ω, centeredResidualProduct depth increment ω ∂μ =
        ∏ index, ∫ ω,
          (fun value : ℝ => 1 + value / Real.sqrt depth)
            (increment index ω) ∂μ := by
      simpa [centeredResidualProduct] using hfactorization
    _ = 1 := by
      simp_rw [centeredResidualFactor_integral_eq_one μ depth _
        (hintegrable _) (hcentered _)]
      simp

/-- Independence also factorizes the second moment of the whole product. -/
theorem centeredResidualProduct_sq_integral_factorization
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (increment : Fin depth → Ω → ℝ)
    (hindependent : iIndepFun increment μ)
    (hintegrable : ∀ index, Integrable (increment index) μ) :
    ∫ ω, centeredResidualProduct depth increment ω ^ 2 ∂μ =
      ∏ index, ∫ ω,
        (1 + increment index ω / Real.sqrt depth) ^ 2 ∂μ := by
  have hfactorization :
      ∫ ω, ∏ index,
          ((fun value : ℝ => 1 + value / Real.sqrt depth)
            (increment index ω)) ^ 2 ∂μ =
        ∏ index, ∫ ω,
          ((fun value : ℝ => 1 + value / Real.sqrt depth)
            (increment index ω)) ^ 2 ∂μ := by
    exact hindependent.integral_fun_prod_comp
      (fun index => (hintegrable index).aemeasurable)
      (fun _ => (by fun_prop : Continuous
        (fun value : ℝ => (1 + value / Real.sqrt depth) ^ 2)).aestronglyMeasurable)
  simpa [centeredResidualProduct, Finset.prod_pow] using hfactorization

/-- Crown: centered independent `1/sqrt(L)` residual increments have exact
mean one and second moment uniformly bounded by `exp(σ²)`. -/
theorem centeredIndependentResidual_mean_one_secondMoment_le_exp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (hdepth : 0 < depth) (sigma : ℝ)
    (increment : Fin depth → Ω → ℝ)
    (hindependent : iIndepFun increment μ)
    (hintegrable : ∀ index, Integrable (increment index) μ)
    (hsqIntegrable : ∀ index,
      Integrable (fun ω => increment index ω ^ 2) μ)
    (hcentered : ∀ index, ∫ ω, increment index ω ∂μ = 0)
    (hsecondMoment : ∀ index,
      ∫ ω, increment index ω ^ 2 ∂μ ≤ sigma ^ 2) :
    (∫ ω, centeredResidualProduct depth increment ω ∂μ = 1) ∧
      (∫ ω, centeredResidualProduct depth increment ω ^ 2 ∂μ ≤
        Real.exp (sigma ^ 2)) := by
  constructor
  · exact centeredResidualProduct_integral_eq_one μ depth increment hindependent
      hintegrable hcentered
  · rw [centeredResidualProduct_sq_integral_factorization μ depth increment
      hindependent hintegrable]
    simp_rw [centeredResidualFactor_sq_integral μ depth hdepth _
      (hintegrable _) (hsqIntegrable _) (hcentered _)]
    have hdepthReal : (0 : ℝ) < depth := by exact_mod_cast hdepth
    calc
      ∏ index : Fin depth,
          (1 + (∫ ω, increment index ω ^ 2 ∂μ) / depth) ≤
          ∏ _index : Fin depth, (1 + sigma ^ 2 / depth) := by
            apply Finset.prod_le_prod
            · intro index _
              exact add_nonneg zero_le_one <| div_nonneg
                (integral_nonneg fun _ => sq_nonneg _) hdepthReal.le
            · intro index _
              gcongr
              exact hsecondMoment index
      _ = (1 + sigma ^ 2 / depth) ^ depth := by simp
      _ ≤ Real.exp (sigma ^ 2) := by
        have ht : -(sigma ^ 2) ≤ (depth : ℝ) :=
          (neg_nonpos.mpr (sq_nonneg sigma)).trans hdepthReal.le
        convert Real.one_sub_div_pow_le_exp_neg
          (n := depth) (t := -(sigma ^ 2)) ht using 1 <;>
          ring_nf

/-- The deterministic and random scalar conclusions form a sharp bracket:
aligned increments blow up, inverse-depth increments stay below `exp 1`, and
centered independent square-root increments have uniformly bounded second
moment. -/
theorem scalarResidualScaling_boundary_crown :
    (∀ bound : ℝ, ∃ depth : ℕ, 0 < depth ∧
      bound < alignedDepthMuPResidualStack depth) ∧
      (∀ depth : ℕ, inverseDepthResidualStack depth ≤ Real.exp 1) := by
  exact ⟨alignedDepthMuPResidualStack_unbounded,
    inverseDepthResidualStack_le_exp_one⟩

/-- Matrix-valued residual products are kept as a pinned reproduction target;
the scalar independence theorem does not silently assume commutativity. -/
def matrixResidualMomentBoundary : ResidualScalingBoundaryClaim where
  description := "matrix-valued random residual product moment bound"
  status := .infiniteWidthReproductionTarget

theorem matrixResidualMomentBoundary_is_reproductionTarget :
    matrixResidualMomentBoundary.status = .infiniteWidthReproductionTarget := by
  rfl

#print axioms centeredIndependentResidual_mean_one_secondMoment_le_exp
#print axioms scalarResidualScaling_boundary_crown

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
