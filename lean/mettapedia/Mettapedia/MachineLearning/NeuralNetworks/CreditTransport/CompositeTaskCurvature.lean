import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-!
# Composite task curvature and affine readout transport

The registered TGAD objective is a nonnegative weighted sum of primary and
auxiliary losses.  This file proves that directional upper models compose with
those weights and transport exactly through an affine readout.  It also records
the boundary that an affine pullback does not cover a nonlinear decoder map.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CompositeTaskCurvature

open scoped InnerProductSpace
open DirectionalTaskDescent

noncomputable section

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-! ## Nonnegative task aggregation -/

/-- A finite weighted task objective. -/
def weightedTaskLoss {Site : Type*}
    (sites : Finset Site) (weight : Site → ℝ)
    (loss : Site → Parameter → ℝ) (parameter : Parameter) : ℝ :=
  ∑ site ∈ sites, weight site * loss site parameter

/-- The corresponding weighted sum of declared task gradients. -/
def weightedTaskGradient {Site : Type*}
    (sites : Finset Site) (weight : Site → ℝ)
    (gradient : Site → Parameter) : Parameter :=
  ∑ site ∈ sites, weight site • gradient site

/-- The corresponding weighted sum of directional curvature bounds. -/
def weightedTaskCurvature {Site : Type*}
    (sites : Finset Site) (weight curvature : Site → ℝ) : ℝ :=
  ∑ site ∈ sites, weight site * curvature site

theorem weightedTask_upper_sum_eq
    {Site : Type*} [DecidableEq Site]
    (sites : Finset Site) (weight : Site → ℝ)
    (loss : Site → Parameter → ℝ) (gradient : Site → Parameter)
    (curvature : Site → ℝ) (parameter direction : Parameter) (step : ℝ) :
    ∑ site ∈ sites, weight site *
        (loss site parameter - step * ⟪gradient site, direction⟫_ℝ +
          step ^ 2 * curvature site / 2) =
      weightedTaskLoss sites weight loss parameter -
        step * ⟪weightedTaskGradient sites weight gradient, direction⟫_ℝ +
          step ^ 2 * weightedTaskCurvature sites weight curvature / 2 := by
  induction sites using Finset.induction_on with
  | empty =>
      simp [weightedTaskLoss, weightedTaskGradient, weightedTaskCurvature]
  | @insert site sites hsite ih =>
      simp [weightedTaskLoss, weightedTaskGradient, weightedTaskCurvature,
        hsite, ih, inner_add_left, sum_inner, real_inner_smul_left]
      ring

/-- Nonnegative weighted sums preserve directional task upper models. -/
theorem weightedTask_hasDirectionalTaskUpperModelAt
    {Site : Type*} [DecidableEq Site]
    (sites : Finset Site) (weight : Site → ℝ)
    (loss : Site → Parameter → ℝ) (gradient : Site → Parameter)
    (curvature : Site → ℝ) (parameter direction : Parameter)
    (hweight : ∀ site ∈ sites, 0 ≤ weight site)
    (hcomponent : ∀ site ∈ sites,
      HasDirectionalTaskUpperModelAt
        (loss site) parameter (gradient site) direction (curvature site)) :
    HasDirectionalTaskUpperModelAt
      (weightedTaskLoss sites weight loss) parameter
      (weightedTaskGradient sites weight gradient) direction
      (weightedTaskCurvature sites weight curvature) := by
  intro step hstep
  have hsum :
      ∑ site ∈ sites, weight site * loss site (parameter - step • direction) ≤
        ∑ site ∈ sites, weight site *
          (loss site parameter - step * ⟪gradient site, direction⟫_ℝ +
            step ^ 2 * curvature site / 2) := by
    exact Finset.sum_le_sum fun site hsite =>
      mul_le_mul_of_nonneg_left
        (hcomponent site hsite step hstep) (hweight site hsite)
  calc
    weightedTaskLoss sites weight loss (parameter - step • direction) =
        ∑ site ∈ sites, weight site *
          loss site (parameter - step • direction) := rfl
    _ ≤ ∑ site ∈ sites, weight site *
          (loss site parameter - step * ⟪gradient site, direction⟫_ℝ +
            step ^ 2 * curvature site / 2) := hsum
    _ = weightedTaskLoss sites weight loss parameter -
          step * ⟪weightedTaskGradient sites weight gradient, direction⟫_ℝ +
          step ^ 2 * weightedTaskCurvature sites weight curvature / 2 :=
      weightedTask_upper_sum_eq sites weight loss gradient curvature
        parameter direction step

/-! ## The registered TGAD loss schema -/

/-- The eight component families occurring in the registered TGAD task loss. -/
inductive TGADTaskSite
  | primary
  | operatorBag
  | lengthBucket
  | nextSign
  | nextLogBucket
  | nextResidueTwo
  | nextResidueThree
  | nextResidueFive
  deriving DecidableEq, Fintype

/-- Exact-real idealization of the source weights.  The next-term heads are
inactive when their target is unavailable. -/
def tgadTaskWeight (auxiliary nextTermAvailable : Bool) : TGADTaskSite → ℝ
  | .primary => 1
  | .operatorBag => if auxiliary then 1 / 5 else 0
  | .lengthBucket => if auxiliary then 1 / 10 else 0
  | .nextSign => if auxiliary && nextTermAvailable then 1 / 10 else 0
  | .nextLogBucket => if auxiliary && nextTermAvailable then 1 / 10 else 0
  | .nextResidueTwo => if auxiliary && nextTermAvailable then 1 / 10 else 0
  | .nextResidueThree => if auxiliary && nextTermAvailable then 1 / 10 else 0
  | .nextResidueFive => if auxiliary && nextTermAvailable then 1 / 10 else 0

theorem tgadTaskWeight_nonneg
    (auxiliary nextTermAvailable : Bool) (site : TGADTaskSite) :
    0 ≤ tgadTaskWeight auxiliary nextTermAvailable site := by
  cases auxiliary <;> cases nextTermAvailable <;> cases site <;>
    norm_num [tgadTaskWeight]

/-- The idealized registered task objective over its active component heads. -/
def tgadTaskLoss
    (auxiliary nextTermAvailable : Bool)
    (loss : TGADTaskSite → Parameter → ℝ) : Parameter → ℝ :=
  weightedTaskLoss Finset.univ
    (tgadTaskWeight auxiliary nextTermAvailable) loss

/-- Its declared aggregate gradient. -/
def tgadTaskGradient
    (auxiliary nextTermAvailable : Bool)
    (gradient : TGADTaskSite → Parameter) : Parameter :=
  weightedTaskGradient Finset.univ
    (tgadTaskWeight auxiliary nextTermAvailable) gradient

/-- Its declared aggregate directional curvature. -/
def tgadTaskCurvature
    (auxiliary nextTermAvailable : Bool)
    (curvature : TGADTaskSite → ℝ) : ℝ :=
  weightedTaskCurvature Finset.univ
    (tgadTaskWeight auxiliary nextTermAvailable) curvature

/-- Componentwise directional certificates compose into the registered TGAD
task objective. -/
theorem tgadTask_hasDirectionalTaskUpperModelAt
    (auxiliary nextTermAvailable : Bool)
    (loss : TGADTaskSite → Parameter → ℝ)
    (gradient : TGADTaskSite → Parameter)
    (curvature : TGADTaskSite → ℝ)
    (parameter direction : Parameter)
    (hcomponent : ∀ site,
      HasDirectionalTaskUpperModelAt
        (loss site) parameter (gradient site) direction (curvature site)) :
    HasDirectionalTaskUpperModelAt
      (tgadTaskLoss auxiliary nextTermAvailable loss) parameter
      (tgadTaskGradient auxiliary nextTermAvailable gradient) direction
      (tgadTaskCurvature auxiliary nextTermAvailable curvature) := by
  apply weightedTask_hasDirectionalTaskUpperModelAt
  · intro site _
    exact tgadTaskWeight_nonneg auxiliary nextTermAvailable site
  · intro site _
    exact hcomponent site

/-! ## Affine readout transport -/

variable {Logit : Type*}
  [NormedAddCommGroup Logit] [InnerProductSpace ℝ Logit]
  [CompleteSpace Parameter] [CompleteSpace Logit]

/-- A frozen affine readout from a representation or adapter coordinate into
one task head's logits. -/
def affineReadout (linear : Parameter →L[ℝ] Logit) (bias : Logit)
    (parameter : Parameter) : Logit :=
  linear parameter + bias

/-- Directional upper models pull back exactly through an affine readout; the
parameter gradient is the adjoint transport of the logit gradient. -/
theorem affineReadout_hasDirectionalTaskUpperModelAt
    (linear : Parameter →L[ℝ] Logit) (bias : Logit)
    {loss : Logit → ℝ} {parameter direction : Parameter}
    {logitGradient : Logit} {curvature : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss
        (affineReadout linear bias parameter) logitGradient
        (linear direction) curvature) :
    HasDirectionalTaskUpperModelAt
      (fun candidate => loss (affineReadout linear bias candidate))
      parameter (linear.adjoint logitGradient) direction curvature := by
  intro step hstep
  have haffine :
      affineReadout linear bias (parameter - step • direction) =
        affineReadout linear bias parameter - step • linear direction := by
    simp only [affineReadout, map_sub, map_smul]
    abel
  have h := certificate step hstep
  change loss (affineReadout linear bias (parameter - step • direction)) ≤
    loss (affineReadout linear bias parameter) -
      step * ⟪linear.adjoint logitGradient, direction⟫_ℝ +
        step ^ 2 * curvature / 2
  rw [haffine]
  simpa [ContinuousLinearMap.adjoint_inner_left] using h

/-- A global logit-space smoothness model yields the sharper affine-head
curvature `beta * ‖A d‖²`, not the coarser full-network parameter norm. -/
theorem affineReadout_hasDirectionalTaskUpperModelAt_of_smooth
    (linear : Parameter →L[ℝ] Logit) (bias : Logit)
    {loss : Logit → ℝ} {parameter direction : Parameter}
    {logitGradient : Logit} {beta : ℝ}
    (certificate : HasSmoothTaskUpperModelAt loss
      (affineReadout linear bias parameter) logitGradient beta) :
    HasDirectionalTaskUpperModelAt
      (fun candidate => loss (affineReadout linear bias candidate))
      parameter (linear.adjoint logitGradient) direction
      (beta * ‖linear direction‖ ^ 2) := by
  exact affineReadout_hasDirectionalTaskUpperModelAt linear bias
    (certificate.toDirectional (linear direction))

/-! ## Nonlinear readout remainder -/

/-- A source-level nonlinear forward map can be compared with its declared
Jacobian along one parameter direction. -/
def directionalReadoutResidual
    (forward : Parameter → Logit) (linearization : Parameter →L[ℝ] Logit)
    (parameter direction : Parameter) (step : ℝ) : Logit :=
  forward (parameter - step • direction) -
    (forward parameter - step • linearization direction)

/-- Smooth logit loss plus an explicit nonlinear readout-remainder budget
gives a finite-step task upper bound.  This is the honest bridge for a neural
decoder: the affine theorem is recovered when the residual budget is zero. -/
theorem nonlinearReadout_task_upper_of_residual
    (forward : Parameter → Logit) (linearization : Parameter →L[ℝ] Logit)
    {loss : Logit → ℝ} {parameter direction : Parameter}
    {logitGradient : Logit} {beta step residualBudget : ℝ}
    (certificate : HasSmoothTaskUpperModelAt loss
      (forward parameter) logitGradient beta)
    (hbeta : 0 ≤ beta) (hstep : 0 ≤ step)
    (hbudget : 0 ≤ residualBudget)
    (hresidual :
      ‖directionalReadoutResidual forward linearization
        parameter direction step‖ ≤ residualBudget) :
    loss (forward (parameter - step • direction)) ≤
      loss (forward parameter) -
        step * ⟪linearization.adjoint logitGradient, direction⟫_ℝ +
        ‖logitGradient‖ * residualBudget +
        beta *
          (step * ‖linearization direction‖ + residualBudget) ^ 2 / 2 := by
  let residual := directionalReadoutResidual forward linearization
    parameter direction step
  let displacement := step • linearization direction - residual
  have hreconstruct :
      forward (parameter - step • direction) =
        forward parameter - displacement := by
    dsimp [displacement, residual, directionalReadoutResidual]
    abel
  have hupper := certificate displacement 1 (by norm_num)
  have hupper' :
      loss (forward (parameter - step • direction)) ≤
        loss (forward parameter) -
          step * ⟪linearization.adjoint logitGradient, direction⟫_ℝ +
          ⟪logitGradient, residual⟫_ℝ + beta * ‖displacement‖ ^ 2 / 2 := by
    rw [hreconstruct]
    calc
      loss (forward parameter - displacement) ≤
          loss (forward parameter) - ⟪logitGradient, displacement⟫_ℝ +
            beta * ‖displacement‖ ^ 2 / 2 := by
        simpa using hupper
      _ = loss (forward parameter) -
          step * ⟪linearization.adjoint logitGradient, direction⟫_ℝ +
          ⟪logitGradient, residual⟫_ℝ + beta * ‖displacement‖ ^ 2 / 2 := by
        simp only [displacement, inner_sub_right, real_inner_smul_right,
          ContinuousLinearMap.adjoint_inner_left]
        ring
  have hresidual' : ‖residual‖ ≤ residualBudget := by
    exact hresidual
  have hdisplacement :
      ‖displacement‖ ≤
        step * ‖linearization direction‖ + residualBudget := by
    calc
      ‖displacement‖ = ‖step • linearization direction - residual‖ := rfl
      _ ≤ ‖step • linearization direction‖ + ‖residual‖ := norm_sub_le _ _
      _ = step * ‖linearization direction‖ + ‖residual‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
      _ ≤ step * ‖linearization direction‖ + residualBudget :=
        add_le_add le_rfl hresidual'
  have hsumNonneg :
      0 ≤ step * ‖linearization direction‖ + residualBudget :=
    add_nonneg (mul_nonneg hstep (norm_nonneg _)) hbudget
  have hdisplacementSq :
      ‖displacement‖ ^ 2 ≤
        (step * ‖linearization direction‖ + residualBudget) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 hdisplacement
  have hcurvature :
      beta * ‖displacement‖ ^ 2 / 2 ≤
        beta *
          (step * ‖linearization direction‖ + residualBudget) ^ 2 / 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdisplacementSq hbeta) (by norm_num)
  have hinner :
      ⟪logitGradient, residual⟫_ℝ ≤
        ‖logitGradient‖ * residualBudget :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hresidual' (norm_nonneg _))
  linarith

/-- The preceding remainder bound is a strict task-descent certificate when
its nonlinear and logit-curvature costs fit under the first-order margin. -/
theorem nonlinearReadout_strict_descent_of_residual
    (forward : Parameter → Logit) (linearization : Parameter →L[ℝ] Logit)
    {loss : Logit → ℝ} {parameter direction : Parameter}
    {logitGradient : Logit} {beta step residualBudget : ℝ}
    (certificate : HasSmoothTaskUpperModelAt loss
      (forward parameter) logitGradient beta)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hbudget : 0 ≤ residualBudget)
    (hresidual :
      ‖directionalReadoutResidual forward linearization
        parameter direction step‖ ≤ residualBudget)
    (htrust :
      ‖logitGradient‖ * residualBudget +
          beta *
            (step * ‖linearization direction‖ + residualBudget) ^ 2 / 2 <
        step * ⟪linearization.adjoint logitGradient, direction⟫_ℝ) :
    loss (forward (parameter - step • direction)) < loss (forward parameter) := by
  have hupper := nonlinearReadout_task_upper_of_residual
    forward linearization certificate hbeta hstep.le hbudget hresidual
  linarith

/-! ## Exact fixtures and scope boundaries -/

def twoSiteWeight : Bool → ℝ
  | false => 1
  | true => 1 / 5

def twoSiteLoss : Bool → ℝ → ℝ
  | false => fun x => x ^ 2 / 2
  | true => fun x => (x - 1) ^ 2 / 2

def twoSiteGradientAtZero : Bool → ℝ
  | false => 0
  | true => -1

def twoSiteCurvature (direction : ℝ) (_site : Bool) : ℝ := direction ^ 2

theorem twoSite_component_directional
    (site : Bool) (direction : ℝ) :
    HasDirectionalTaskUpperModelAt
      (twoSiteLoss site) 0 (twoSiteGradientAtZero site) direction
      (twoSiteCurvature direction site) := by
  intro step _
  cases site
  · simp [twoSiteLoss, twoSiteGradientAtZero, twoSiteCurvature]
    ring_nf
    exact le_rfl
  · simp [twoSiteLoss, twoSiteGradientAtZero, twoSiteCurvature]
    ring_nf
    exact le_rfl

/-- A nontrivial two-head objective satisfies the aggregate directional model. -/
theorem twoSite_weighted_directional_positive :
    HasDirectionalTaskUpperModelAt
      (weightedTaskLoss Finset.univ twoSiteWeight twoSiteLoss)
      0
      (weightedTaskGradient Finset.univ twoSiteWeight twoSiteGradientAtZero)
      (-1 / 5)
      (weightedTaskCurvature Finset.univ twoSiteWeight
        (twoSiteCurvature (-1 / 5))) := by
  apply weightedTask_hasDirectionalTaskUpperModelAt
  · intro site _
    cases site <;> norm_num [twoSiteWeight]
  · intro site _
    exact twoSite_component_directional site (-1 / 5)

def looseZeroLoss (_site : Bool) (_x : ℝ) : ℝ := 0

def looseZeroGradient (_site : Bool) : ℝ := 0

def signedWeight : Bool → ℝ
  | false => -1
  | true => 0

def looseCurvature : Bool → ℝ
  | false => 1
  | true => 0

theorem looseZero_component_directional (site : Bool) :
    HasDirectionalTaskUpperModelAt
      (looseZeroLoss site) 0 (looseZeroGradient site) 1
      (looseCurvature site) := by
  intro step _
  cases site
  · simp [looseZeroLoss, looseZeroGradient, looseCurvature]
    positivity
  · simp [looseZeroLoss, looseZeroGradient, looseCurvature]

/-- Negative task weights can reverse a valid loose upper bound, so the
nonnegativity premise in task aggregation is substantive. -/
theorem signedWeight_breaks_directional_aggregation :
    ¬ HasDirectionalTaskUpperModelAt
      (weightedTaskLoss Finset.univ signedWeight looseZeroLoss)
      0
      (weightedTaskGradient Finset.univ signedWeight looseZeroGradient)
      1
      (weightedTaskCurvature Finset.univ signedWeight looseCurvature) := by
  intro certificate
  have h := certificate 1 (by norm_num)
  norm_num [weightedTaskLoss, weightedTaskGradient, weightedTaskCurvature,
    signedWeight, looseZeroLoss, looseZeroGradient, looseCurvature] at h

def squareReadout (parameter : ℝ) : ℝ := parameter ^ 2

/-- Transporting only the pointwise Jacobian through a nonlinear readout is
unsound: the square map has zero derivative at zero but nonzero finite-step
curvature. -/
theorem nonlinearReadout_not_licensed_by_pointwise_linearization :
    ¬ HasDirectionalTaskUpperModelAt
      (fun parameter : ℝ => squareReadout parameter) 0 0 1 0 := by
  intro certificate
  have h := certificate 1 (by norm_num)
  norm_num [squareReadout] at h

#print axioms weightedTask_hasDirectionalTaskUpperModelAt
#print axioms tgadTask_hasDirectionalTaskUpperModelAt
#print axioms affineReadout_hasDirectionalTaskUpperModelAt
#print axioms affineReadout_hasDirectionalTaskUpperModelAt_of_smooth
#print axioms nonlinearReadout_task_upper_of_residual
#print axioms nonlinearReadout_strict_descent_of_residual
#print axioms twoSite_weighted_directional_positive
#print axioms signedWeight_breaks_directional_aggregation
#print axioms nonlinearReadout_not_licensed_by_pointwise_linearization

end

end CompositeTaskCurvature

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
