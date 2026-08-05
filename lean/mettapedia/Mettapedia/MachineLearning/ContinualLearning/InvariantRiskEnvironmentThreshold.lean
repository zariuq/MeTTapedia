import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Environment-count and normalized-solution geometry for invariant risk

This file isolates two linear-algebraic mechanisms behind the finite-
environment boundary in Rosenfeld, Ravikumar, and Risteski, *The Risks of
Invariant Risk Minimization* (ICLR 2021, arXiv:2010.05761).

First, fewer scalar environment constraints than nuisance coordinates always
leave a nonzero invisible direction.  At equal dimension this conclusion is
not automatic: the identity constraint map is an explicit boundary example.

Second, suppose a constraint family has a nonzero minimum-norm solution
`base` at scalar right-hand side one.  Every solution at nonnegative scale can
be decomposed as `scale • base + residual`, with the residual orthogonal to
`base`.  Requiring unit norm forces

`scale ≤ 1 / ‖base‖`,

and equality uniquely removes the residual.  This is the normalized
minimum-norm core of the source's Lemma C.1.  For linearly independent
environment vectors, the file also constructs `base` using the inverse Gram
matrix and proves the required minimum-norm certificate.

These theorems do not formalize the source's Gaussian data model, logistic
risk comparison, or its complete environment threshold theorem.  They make
the geometric boundaries available without attributing those stronger
statistical conclusions to linear algebra alone.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace InvariantRiskEnvironmentThreshold

open scoped RealInnerProductSpace

/-! ## Fewer constraints than nuisance dimensions -/

/-- If the number of scalar environment constraints is strictly smaller than
the nuisance dimension, every linear constraint map has a nonzero invisible
direction. -/
theorem exists_nonzero_environment_invisible_direction
    {environmentCount nuisanceDimension : ℕ}
    (hlt : environmentCount < nuisanceDimension)
    (constraints :
      (Fin nuisanceDimension → ℝ) →ₗ[ℝ]
        (Fin environmentCount → ℝ)) :
    ∃ direction : Fin nuisanceDimension → ℝ,
      direction ≠ 0 ∧ constraints direction = 0 := by
  have hfinrank :
      Module.finrank ℝ (Fin environmentCount → ℝ) <
        Module.finrank ℝ (Fin nuisanceDimension → ℝ) := by
    simpa using hlt
  have hker :
      LinearMap.ker constraints ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨direction, hdirection, hne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact
    ⟨direction, hne, LinearMap.mem_ker.mp hdirection⟩

/-- At the dimension boundary, invisible directions are not forced: the
identity environment constraint has trivial kernel. -/
theorem equal_environment_identity_has_no_nonzero_invisible_direction
    (dimension : ℕ) :
    ¬ ∃ direction : Fin dimension → ℝ,
      direction ≠ 0 ∧
        LinearMap.id (R := ℝ) (M := Fin dimension → ℝ) direction = 0 := by
  simp

/-! ## Normalized minimum-norm solutions -/

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A unit-norm solution decomposed into a multiple of a declared
minimum-norm base solution and an orthogonal residual. -/
structure OrthogonalUnitSolution (base : V) where
  scale : ℝ
  residual : V
  scale_nonnegative : 0 ≤ scale
  residual_orthogonal : inner ℝ base residual = 0
  unit_norm : ‖scale • base + residual‖ = 1

/-- The canonical normalized solution: rescale the nonzero minimum-norm base
solution and add no invisible residual. -/
noncomputable def canonicalUnitSolution
    (base : V)
    (hbase : base ≠ 0) : OrthogonalUnitSolution base where
  scale := 1 / ‖base‖
  residual := 0
  scale_nonnegative := by positivity
  residual_orthogonal := by simp
  unit_norm := by
    rw [add_zero, norm_smul, Real.norm_eq_abs]
    have hnorm : 0 < ‖base‖ := norm_pos_iff.mpr hbase
    rw [abs_of_pos (one_div_pos.mpr hnorm)]
    field_simp

/-- Pythagoras turns a unit-norm orthogonal solution into an exact budget:
the squared base component plus the squared invisible residual is one. -/
theorem orthogonalUnitSolution_budget
    {base : V}
    (solution : OrthogonalUnitSolution base) :
    (solution.scale * ‖base‖) ^ 2 +
        ‖solution.residual‖ ^ 2 = 1 := by
  have hinner :
      inner ℝ
        (solution.scale • base)
        solution.residual = 0 := by
    rw [real_inner_smul_left, solution.residual_orthogonal,
      mul_zero]
  have hpythagoras :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
  rw [solution.unit_norm, norm_smul,
    Real.norm_eq_abs,
    abs_of_nonneg solution.scale_nonnegative] at hpythagoras
  simpa [pow_two] using hpythagoras.symm

/-- A unit-norm solution cannot carry a larger nonnegative right-hand-side
scale than the normalized minimum-norm solution. -/
theorem orthogonalUnitSolution_scale_le
    {base : V}
    (hbase : base ≠ 0)
    (solution : OrthogonalUnitSolution base) :
    solution.scale ≤ 1 / ‖base‖ := by
  have hnorm : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hbudget := orthogonalUnitSolution_budget solution
  have hresidualSq : 0 ≤ ‖solution.residual‖ ^ 2 :=
    sq_nonneg ‖solution.residual‖
  have hcomponentNonnegative :
      0 ≤ solution.scale * ‖base‖ :=
    mul_nonneg solution.scale_nonnegative hnorm.le
  have hcomponent :
      solution.scale * ‖base‖ ≤ 1 := by
    nlinarith
  exact (le_div_iff₀ hnorm).2 hcomponent

/-- Reaching the maximal scale forces the invisible residual to vanish. -/
theorem orthogonalUnitSolution_residual_eq_zero_of_scale_eq
    {base : V}
    (hbase : base ≠ 0)
    (solution : OrthogonalUnitSolution base)
    (hscale : solution.scale = 1 / ‖base‖) :
    solution.residual = 0 := by
  have hnorm : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hbudget := orthogonalUnitSolution_budget solution
  rw [hscale] at hbudget
  have hnormalize : (1 / ‖base‖) * ‖base‖ = 1 := by
    field_simp
  rw [hnormalize, one_pow] at hbudget
  have hresidualNorm : ‖solution.residual‖ = 0 := by
    nlinarith [sq_nonneg ‖solution.residual‖]
  exact norm_eq_zero.mp hresidualNorm

/-- The maximal unit vector is unique inside the orthogonal solution
decomposition. -/
theorem orthogonalUnitSolution_vector_eq_canonical_of_scale_eq
    {base : V}
    (hbase : base ≠ 0)
    (solution : OrthogonalUnitSolution base)
    (hscale : solution.scale = 1 / ‖base‖) :
    solution.scale • base + solution.residual =
      (1 / ‖base‖) • base := by
  rw [hscale,
    orthogonalUnitSolution_residual_eq_zero_of_scale_eq
      hbase solution hscale,
    add_zero]

/-! ## Constraint-certified minimum-norm geometry -/

variable {W : Type*}
variable [AddCommGroup W] [Module ℝ W]

/-- A nonzero base solution of a linear constraint is minimum-norm when it is
orthogonal to every homogeneous invisible direction.  This is the coordinate-
free premise supplied by the inverse-basis construction in the source's
Lemma C.1. -/
structure MinimumNormConstraintBase
    (constraints : V →ₗ[ℝ] W)
    (target : W)
    (base : V) : Prop where
  base_nonzero : base ≠ 0
  maps_base : constraints base = target
  orthogonal_kernel :
    ∀ residual, constraints residual = 0 →
      inner ℝ base residual = 0

/-- The declared base has minimum norm in its affine constraint fiber. -/
theorem MinimumNormConstraintBase.norm_le_of_maps_to_target
    {constraints : V →ₗ[ℝ] W}
    {target : W}
    {base candidate : V}
    (certificate :
      MinimumNormConstraintBase constraints target base)
    (hcandidate : constraints candidate = target) :
    ‖base‖ ≤ ‖candidate‖ := by
  let residual := candidate - base
  have hresidual : constraints residual = 0 := by
    simp [residual, hcandidate, certificate.maps_base]
  have horthogonal :
      inner ℝ base residual = 0 :=
    certificate.orthogonal_kernel residual hresidual
  have hpythagoras :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
  have hdecomposition : base + residual = candidate := by
    simp [residual]
  rw [hdecomposition] at hpythagoras
  nlinarith [norm_nonneg base, norm_nonneg candidate,
    sq_nonneg ‖residual‖]

/-- Equality in the minimum-norm comparison is unique: another point in the
same affine fiber with the same norm is the base itself. -/
theorem MinimumNormConstraintBase.eq_of_maps_to_target_of_norm_eq
    {constraints : V →ₗ[ℝ] W}
    {target : W}
    {base candidate : V}
    (certificate :
      MinimumNormConstraintBase constraints target base)
    (hcandidate : constraints candidate = target)
    (hnorm : ‖candidate‖ = ‖base‖) :
    candidate = base := by
  let residual := candidate - base
  have hresidual : constraints residual = 0 := by
    simp [residual, hcandidate, certificate.maps_base]
  have horthogonal :
      inner ℝ base residual = 0 :=
    certificate.orthogonal_kernel residual hresidual
  have hpythagoras :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
  have hdecomposition : base + residual = candidate := by
    simp [residual]
  rw [hdecomposition, hnorm] at hpythagoras
  have hresidualNorm : ‖residual‖ = 0 := by
    nlinarith [norm_nonneg residual]
  have hresidualZero : residual = 0 :=
    norm_eq_zero.mp hresidualNorm
  simpa [residual] using sub_eq_zero.mp hresidualZero

/-- A unit candidate satisfying the scaled constraint inherits the normalized
maximum-scale bound from the orthogonal decomposition. -/
theorem MinimumNormConstraintBase.unit_candidate_scale_le
    {constraints : V →ₗ[ℝ] W}
    {target : W}
    {base candidate : V}
    {scale : ℝ}
    (certificate :
      MinimumNormConstraintBase constraints target base)
    (hscale : 0 ≤ scale)
    (hcandidate : constraints candidate = scale • target)
    (hunit : ‖candidate‖ = 1) :
    scale ≤ 1 / ‖base‖ := by
  let residual := candidate - scale • base
  have hresidual : constraints residual = 0 := by
    simp [residual, hcandidate, certificate.maps_base]
  have horthogonal :
      inner ℝ base residual = 0 :=
    certificate.orthogonal_kernel residual hresidual
  let solution : OrthogonalUnitSolution base :=
    { scale := scale
      residual := residual
      scale_nonnegative := hscale
      residual_orthogonal := horthogonal
      unit_norm := by
        simpa [residual] using hunit }
  exact
    orthogonalUnitSolution_scale_le
      certificate.base_nonzero solution

/-- At maximal scale, a unit constraint candidate is exactly the canonical
normalized base vector. -/
theorem MinimumNormConstraintBase.unit_candidate_eq_canonical_of_scale_eq
    {constraints : V →ₗ[ℝ] W}
    {target : W}
    {base candidate : V}
    {scale : ℝ}
    (certificate :
      MinimumNormConstraintBase constraints target base)
    (hscaleNonnegative : 0 ≤ scale)
    (hcandidate : constraints candidate = scale • target)
    (hunit : ‖candidate‖ = 1)
    (hscale : scale = 1 / ‖base‖) :
    candidate = (1 / ‖base‖) • base := by
  let residual := candidate - scale • base
  have hresidual : constraints residual = 0 := by
    simp [residual, hcandidate, certificate.maps_base]
  have horthogonal :
      inner ℝ base residual = 0 :=
    certificate.orthogonal_kernel residual hresidual
  let solution : OrthogonalUnitSolution base :=
    { scale := scale
      residual := residual
      scale_nonnegative := hscaleNonnegative
      residual_orthogonal := horthogonal
      unit_norm := by
        simpa [residual] using hunit }
  have hcanonical :=
    orthogonalUnitSolution_vector_eq_canonical_of_scale_eq
      certificate.base_nonzero solution hscale
  simpa [solution, residual] using hcanonical

/-! ## Constructing the minimum-norm base from independent environments -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The environment constraint map records the inner product with each
environment vector. -/
noncomputable def environmentConstraintMap
    (environments : ι → V) :
    V →ₗ[ℝ] (ι → ℝ) where
  toFun point environment :=
    inner ℝ (environments environment) point
  map_add' := by
    intro first second
    ext environment
    simp only [Pi.add_apply, inner_add_right]
  map_smul' := by
    intro scalar point
    ext environment
    simp only [Pi.smul_apply, smul_eq_mul, real_inner_smul_right,
      RingHom.id_apply]

/-- The Gram-inverse construction of the base satisfying a vector of
environment constraints. -/
noncomputable def gramMinimumNormBase
    (environments : ι → V)
    (target : ι → ℝ) : V :=
  ∑ environment,
    (Matrix.mulVec (Matrix.gram ℝ environments)⁻¹ target)
        environment •
      environments environment

/-- Independent environment vectors make their Gram matrix nonsingular. -/
theorem gram_isUnit_det_of_linearIndependent
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments) :
    IsUnit (Matrix.gram ℝ environments).det := by
  exact
    isUnit_iff_ne_zero.mpr <|
      (Matrix.det_gram_ne_zero_iff_linearIndependent).2
        hindependent

/-- The Gram-inverse base realizes every declared environment target. -/
theorem environmentConstraintMap_gramMinimumNormBase
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    (target : ι → ℝ) :
    environmentConstraintMap environments
        (gramMinimumNormBase environments target) =
      target := by
  let gram := Matrix.gram ℝ environments
  have hunit : IsUnit gram.det := by
    simpa [gram] using
      gram_isUnit_det_of_linearIndependent hindependent
  have hsolve :
      Matrix.mulVec gram (Matrix.mulVec gram⁻¹ target) =
        target := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gram hunit,
      Matrix.one_mulVec]
  ext environment
  have hcomponent := congrFun hsolve environment
  simpa [environmentConstraintMap, gramMinimumNormBase, gram,
    inner_sum, Matrix.mulVec, dotProduct, mul_comm] using hcomponent

/-- A homogeneous invisible direction is orthogonal to the Gram-inverse
base, because that base lies in the span of the environment vectors. -/
theorem gramMinimumNormBase_orthogonal_kernel
    (environments : ι → V)
    (target : ι → ℝ)
    (residual : V)
    (hresidual :
      environmentConstraintMap environments residual = 0) :
    inner ℝ (gramMinimumNormBase environments target) residual = 0 := by
  rw [gramMinimumNormBase, sum_inner]
  apply Finset.sum_eq_zero
  intro environment _
  have hcoordinate :=
    congrFun hresidual environment
  change inner ℝ (environments environment) residual = 0 at hcoordinate
  simp [real_inner_smul_left, hcoordinate]

/-- Linear independence constructs the advertised minimum-norm certificate
for every nonzero target, rather than assuming such a base exists. -/
theorem linearlyIndependent_environment_minimumNormConstraintBase
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    {target : ι → ℝ}
    (htarget : target ≠ 0) :
    MinimumNormConstraintBase
      (environmentConstraintMap environments)
      target
      (gramMinimumNormBase environments target) := by
  refine
    { base_nonzero := ?_
      maps_base :=
        environmentConstraintMap_gramMinimumNormBase
          hindependent target
      orthogonal_kernel := ?_ }
  · intro hbase
    have hmaps :=
      environmentConstraintMap_gramMinimumNormBase
        hindependent target
    rw [hbase, map_zero] at hmaps
    exact htarget hmaps.symm
  · intro residual hresidual
    exact
      gramMinimumNormBase_orthogonal_kernel
        environments target residual hresidual

/-- The complete constructive scale bound: independent environments and a
nonzero target determine a unique minimum-norm base, which bounds every
unit-norm solution of the scaled constraint. -/
theorem linearlyIndependent_environment_unit_candidate_scale_le
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    {target : ι → ℝ}
    (htarget : target ≠ 0)
    {candidate : V}
    {scale : ℝ}
    (hscale : 0 ≤ scale)
    (hcandidate :
      environmentConstraintMap environments candidate =
        scale • target)
    (hunit : ‖candidate‖ = 1) :
    scale ≤
      1 / ‖gramMinimumNormBase environments target‖ := by
  exact
    MinimumNormConstraintBase.unit_candidate_scale_le
      (linearlyIndependent_environment_minimumNormConstraintBase
        hindependent htarget)
      hscale hcandidate hunit

/-- Equality in the constructive scale bound uniquely selects the normalized
Gram-inverse base. -/
theorem linearlyIndependent_environment_unit_candidate_unique
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    {target : ι → ℝ}
    (htarget : target ≠ 0)
    {candidate : V}
    {scale : ℝ}
    (hscaleNonnegative : 0 ≤ scale)
    (hcandidate :
      environmentConstraintMap environments candidate =
        scale • target)
    (hunit : ‖candidate‖ = 1)
    (hscale :
      scale =
        1 / ‖gramMinimumNormBase environments target‖) :
    candidate =
      (1 / ‖gramMinimumNormBase environments target‖) •
        gramMinimumNormBase environments target := by
  exact
    MinimumNormConstraintBase.unit_candidate_eq_canonical_of_scale_eq
      (linearlyIndependent_environment_minimumNormConstraintBase
        hindependent htarget)
      hscaleNonnegative hcandidate hunit hscale

/-! ## Source-shaped maximal normalized direction -/

/-- The largest nonnegative scale permitted by the normalized
inverse-Gram base. -/
noncomputable def normalizedEnvironmentMaximalScale
    (environments : ι → V)
    (target : ι → ℝ) : ℝ :=
  1 / ‖gramMinimumNormBase environments target‖

/-- The inverse-Gram base normalized to unit length. -/
noncomputable def normalizedEnvironmentMaximizingDirection
    (environments : ι → V)
    (target : ι → ℝ) : V :=
  normalizedEnvironmentMaximalScale environments target •
    gramMinimumNormBase environments target

/-- A pointwise positive variance vector is nonzero when there is at least one
environment. -/
theorem positiveVarianceTarget_ne_zero
    {κ : Type*}
    [Nonempty κ]
    {variance : κ → ℝ}
    (hvariance : ∀ environment, 0 < variance environment) :
    variance ≠ 0 := by
  intro hzero
  let environment : κ := Classical.choice inferInstance
  have hcoordinate :
      variance environment = 0 :=
    congrFun hzero environment
  linarith [hvariance environment]

/-- The inverse-Gram direction has unit norm for every independent
environment family and nonzero target. -/
theorem normalizedEnvironmentMaximizingDirection_unit
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    {target : ι → ℝ}
    (htarget : target ≠ 0) :
    ‖normalizedEnvironmentMaximizingDirection
        environments target‖ = 1 := by
  have certificate :=
    linearlyIndependent_environment_minimumNormConstraintBase
      hindependent htarget
  have hnorm :
      0 < ‖gramMinimumNormBase environments target‖ :=
    norm_pos_iff.mpr certificate.base_nonzero
  rw [normalizedEnvironmentMaximizingDirection,
    normalizedEnvironmentMaximalScale, norm_smul,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnorm)]
  field_simp

/-- The normalized inverse-Gram direction realizes the maximal scaled
environment target. -/
theorem normalizedEnvironmentMaximizingDirection_maps
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    (target : ι → ℝ) :
    environmentConstraintMap environments
        (normalizedEnvironmentMaximizingDirection
          environments target) =
      normalizedEnvironmentMaximalScale environments target •
        target := by
  rw [normalizedEnvironmentMaximizingDirection, map_smul,
    environmentConstraintMap_gramMinimumNormBase
      hindependent target]

/-- Source-shaped geometric form of Lemma C.1: for independent environment
means and positive variances, the normalized inverse-Gram direction satisfies
all variance-scaled equations, maximizes their common nonnegative scale among
unit directions, and is the unique direction attaining that maximum. -/
theorem linearlyIndependent_positiveVariance_unique_maximalDirection
    [Nonempty ι]
    {environments : ι → V}
    (hindependent : LinearIndependent ℝ environments)
    {variance : ι → ℝ}
    (hvariance : ∀ environment, 0 < variance environment) :
    ‖normalizedEnvironmentMaximizingDirection
        environments variance‖ = 1 ∧
      environmentConstraintMap environments
          (normalizedEnvironmentMaximizingDirection
            environments variance) =
        normalizedEnvironmentMaximalScale environments variance •
          variance ∧
      ∀ (candidate : V) (scale : ℝ),
        0 ≤ scale →
        ‖candidate‖ = 1 →
        environmentConstraintMap environments candidate =
          scale • variance →
        scale ≤
            normalizedEnvironmentMaximalScale
              environments variance ∧
          (scale =
              normalizedEnvironmentMaximalScale
                environments variance →
            candidate =
              normalizedEnvironmentMaximizingDirection
                environments variance) := by
  have htarget :
      variance ≠ 0 :=
    positiveVarianceTarget_ne_zero hvariance
  refine
    ⟨normalizedEnvironmentMaximizingDirection_unit
        hindependent htarget,
      normalizedEnvironmentMaximizingDirection_maps
        hindependent variance,
      ?_⟩
  intro candidate scale hscale hunit hcandidate
  constructor
  · simpa [normalizedEnvironmentMaximalScale] using
      linearlyIndependent_environment_unit_candidate_scale_le
        hindependent htarget hscale hcandidate hunit
  · intro hmaximal
    simpa [normalizedEnvironmentMaximizingDirection,
      normalizedEnvironmentMaximalScale] using
      linearlyIndependent_environment_unit_candidate_unique
        hindependent htarget hscale hcandidate hunit
          (by simpa [normalizedEnvironmentMaximalScale] using hmaximal)

/-! ## Positive and negative executable fixtures -/

private abbrev Plane :=
  EuclideanSpace ℝ (Fin 2)

/-- The two coordinate axes provide a concrete independent environment
family for the Gram-inverse construction. -/
private noncomputable def standardPlaneEnvironments :
    Fin 2 → Plane :=
  EuclideanSpace.basisFun (Fin 2) ℝ

private theorem standardPlaneEnvironments_linearIndependent :
    LinearIndependent ℝ standardPlaneEnvironments := by
  simpa [standardPlaneEnvironments] using
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent

/-- The constructive theorem produces a genuine minimum-norm certificate
for a two-environment target. -/
theorem standardPlane_environment_minimumNormCertificate :
    MinimumNormConstraintBase
      (environmentConstraintMap standardPlaneEnvironments)
      (1 : Fin 2 → ℝ)
      (gramMinimumNormBase
        standardPlaneEnvironments (1 : Fin 2 → ℝ)) := by
  exact
    linearlyIndependent_environment_minimumNormConstraintBase
      standardPlaneEnvironments_linearIndependent one_ne_zero

/-- Repeated environment vectors are an explicit negative boundary: their
Gram matrix is singular, so the inverse-Gram certificate is unavailable. -/
theorem repeatedPlaneEnvironments_gram_not_isUnit :
    let repeated : Fin 2 → Plane :=
      fun _ ↦ EuclideanSpace.basisFun (Fin 2) ℝ 0
    ¬ IsUnit (Matrix.gram ℝ repeated).det := by
  dsimp only
  intro hunit
  have hindependent :
      LinearIndependent ℝ
        (fun _ : Fin 2 ↦
          EuclideanSpace.basisFun (Fin 2) ℝ 0) :=
    Matrix.linearIndependent_of_det_gram_ne_zero hunit.ne_zero
  have hinjective := hindependent.injective
  have hequal :
      (0 : Fin 2) = 1 :=
    hinjective rfl
  norm_num at hequal

private noncomputable def horizontalBase : Plane :=
  EuclideanSpace.single 0 2

/-- The first-coordinate constraint used to instantiate the abstract
minimum-norm certificate on a nontrivial fiber. -/
private noncomputable def horizontalConstraint :
    Plane →ₗ[ℝ] ℝ where
  toFun := fun point ↦ point 0
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro scalar point
    simp

private theorem horizontalConstraint_certificate :
    MinimumNormConstraintBase
      horizontalConstraint (2 : ℝ) horizontalBase := by
  refine
    { base_nonzero := ?_
      maps_base := ?_
      orthogonal_kernel := ?_ }
  · simp [horizontalBase]
  · norm_num [horizontalConstraint, horizontalBase]
  · intro residual hresidual
    change residual 0 = 0 at hresidual
    simp [horizontalBase, EuclideanSpace.inner_single_left,
      hresidual]

/-- A concrete two-dimensional base has canonical maximal scale `1 / 2`. -/
theorem horizontalBase_every_orthogonal_unit_scale_le_half
    (solution : OrthogonalUnitSolution horizontalBase) :
    solution.scale ≤ (1 / 2 : ℝ) := by
  have hbase : horizontalBase ≠ 0 := by
    simp [horizontalBase]
  have hle :=
    orthogonalUnitSolution_scale_le hbase solution
  norm_num [horizontalBase, EuclideanSpace.norm_eq,
    EuclideanSpace.single] at hle ⊢
  exact hle

/-- On the first-coordinate fiber, the unit candidate with positive maximal
scale is uniquely the normalized horizontal base. -/
theorem horizontalConstraint_unit_candidate_unique
    (candidate : Plane)
    (hcandidate : horizontalConstraint candidate = 1)
    (hunit : ‖candidate‖ = 1) :
    candidate = (1 / 2 : ℝ) • horizontalBase := by
  have hnormalize :
      (1 / ‖horizontalBase‖ : ℝ) = 1 / 2 := by
    norm_num [horizontalBase]
  have hcanonical :=
    MinimumNormConstraintBase.unit_candidate_eq_canonical_of_scale_eq
      horizontalConstraint_certificate
      (candidate := candidate)
      (scale := (1 / 2 : ℝ))
      (by norm_num)
      (by simpa using hcandidate)
      hunit
      hnormalize.symm
  simpa [hnormalize] using hcanonical

/-- Orthogonality is essential.  Without it, cancellation can produce a unit
vector at scale two even though the normalized base scale is one. -/
theorem without_orthogonality_scale_bound_fails :
    let base : ℝ := 1
    let scale : ℝ := 2
    let residual : ℝ := -1
    ‖scale • base + residual‖ = 1 ∧
      1 / ‖base‖ < scale := by
  norm_num

#print axioms exists_nonzero_environment_invisible_direction
#print axioms equal_environment_identity_has_no_nonzero_invisible_direction
#print axioms orthogonalUnitSolution_budget
#print axioms orthogonalUnitSolution_scale_le
#print axioms orthogonalUnitSolution_residual_eq_zero_of_scale_eq
#print axioms orthogonalUnitSolution_vector_eq_canonical_of_scale_eq
#print axioms MinimumNormConstraintBase.norm_le_of_maps_to_target
#print axioms MinimumNormConstraintBase.eq_of_maps_to_target_of_norm_eq
#print axioms MinimumNormConstraintBase.unit_candidate_scale_le
#print axioms
  MinimumNormConstraintBase.unit_candidate_eq_canonical_of_scale_eq
#print axioms gram_isUnit_det_of_linearIndependent
#print axioms environmentConstraintMap_gramMinimumNormBase
#print axioms gramMinimumNormBase_orthogonal_kernel
#print axioms linearlyIndependent_environment_minimumNormConstraintBase
#print axioms linearlyIndependent_environment_unit_candidate_scale_le
#print axioms linearlyIndependent_environment_unit_candidate_unique
#print axioms positiveVarianceTarget_ne_zero
#print axioms normalizedEnvironmentMaximizingDirection_unit
#print axioms normalizedEnvironmentMaximizingDirection_maps
#print axioms
  linearlyIndependent_positiveVariance_unique_maximalDirection
#print axioms standardPlane_environment_minimumNormCertificate
#print axioms repeatedPlaneEnvironments_gram_not_isUnit
#print axioms horizontalBase_every_orthogonal_unit_scale_le_half
#print axioms horizontalConstraint_unit_candidate_unique
#print axioms without_orthogonality_scale_bound_fails

end InvariantRiskEnvironmentThreshold

end Mettapedia.MachineLearning.ContinualLearning
