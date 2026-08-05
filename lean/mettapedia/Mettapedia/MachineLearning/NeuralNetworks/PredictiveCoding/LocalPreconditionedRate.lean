import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalityCeiling
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DepthPathology
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.PosDef

/-!
# Rate ceilings for block-local preconditioned settling

This file studies one-step, memoryless preconditioned relaxation for a
quadratic chain energy.  The preconditioner is represented by its positive
definite metric `M`: the error update is `I - M⁻¹ A`, where `A` is the energy
Hessian.  In the `M` inner product, `M⁻¹ A` is self-adjoint and its Rayleigh
quotient is the generalized quotient `xᴴ A x / xᴴ M x`.

The block-local ceiling below uses the full class of positive-definite block
metrics, not only diagonal or scalar Jacobi metrics.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Matrix

/-! ## Generalized self-adjoint preconditioned operators -/

/-- The memoryless preconditioned energy operator `M⁻¹ A`. -/
noncomputable def metricPreconditionedOperator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) : Module.End ℝ (ι → ℝ) :=
  Matrix.toLin' (M⁻¹ * A)

/-- A Hermitian energy Hessian remains self-adjoint after left
preconditioning, when self-adjointness is measured in the metric supplied by
the positive-definite preconditioner denominator. -/
theorem metricPreconditionedOperator_isSymmetric {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) (hM : M.PosDef) (hA : A.IsHermitian) :
    @LinearMap.IsSymmetric ℝ (ι → ℝ) inferInstance
      (M.toNormedAddCommGroup hM).toSeminormedAddCommGroup
      (M.toInnerProductSpace hM.posSemidef)
      (metricPreconditionedOperator M A) := by
  letI := hM.isUnit.invertible
  intro x y
  change (M *ᵥ y) ⬝ᵥ star ((M⁻¹ * A) *ᵥ x) =
    (M *ᵥ ((M⁻¹ * A) *ᵥ y)) ⬝ᵥ star x
  simp only [star_mulVec]
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_vecMul,
    conjTranspose_mul, hA.eq, Matrix.conjTranspose_nonsing_inv,
    hM.isHermitian.eq, Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.mul_one, ← dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible, Matrix.one_mul, dotProduct_comm]

/-- In the metric inner product, the preconditioned Rayleigh numerator is
exactly the original energy quadratic form. -/
theorem metricPreconditionedOperator_inner_self {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) (hM : M.PosDef) (hA : A.IsHermitian)
    (x : ι → ℝ) :
    @inner ℝ (ι → ℝ)
      (M.toInnerProductSpace hM.posSemidef).toInner
      (metricPreconditionedOperator M A x) x =
      star x ⬝ᵥ (A *ᵥ x) := by
  letI := hM.isUnit.invertible
  change (M *ᵥ x) ⬝ᵥ star ((M⁻¹ * A) *ᵥ x) =
    star x ⬝ᵥ (A *ᵥ x)
  simp only [star_mulVec]
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_vecMul,
    conjTranspose_mul, hA.eq, Matrix.conjTranspose_nonsing_inv,
    hM.isHermitian.eq, Matrix.mul_assoc,
    Matrix.inv_mul_of_invertible, Matrix.mul_one,
    ← dotProduct_mulVec]

/-- The metric norm squared is the metric quadratic form. -/
theorem metric_norm_sq {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (x : ι → ℝ) :
    @norm (ι → ℝ) (M.toNormedAddCommGroup hM).toNorm x ^ 2 =
      star x ⬝ᵥ (M *ᵥ x) := by
  rw [← @real_inner_self_eq_norm_sq (ι → ℝ)
    (M.toNormedAddCommGroup hM).toSeminormedAddCommGroup
    (M.toInnerProductSpace hM.posSemidef) x]
  change (M *ᵥ x) ⬝ᵥ star x = star x ⬝ᵥ (M *ᵥ x)
  exact dotProduct_comm _ _

/-- Every nonzero test vector bounds an actual generalized eigenvalue of the
preconditioned operator.  This is the finite-dimensional Rayleigh principle,
stated directly in the original energy and metric quadratic forms. -/
theorem exists_preconditioned_eigenvalue_le_generalizedRayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M A : Matrix ι ι ℝ) (hM : M.PosDef) (hA : A.PosSemidef)
    (v : ι → ℝ) (hv : v ≠ 0) :
    ∃ μ : ℝ,
      Module.End.HasEigenvalue (metricPreconditionedOperator M A) μ ∧
        0 ≤ μ ∧
        μ ≤ (star v ⬝ᵥ (A *ᵥ v)) / (star v ⬝ᵥ (M *ᵥ v)) := by
  let normed := M.toNormedAddCommGroup hM
  let innerProduct := M.toInnerProductSpace hM.posSemidef
  let μ : ℝ :=
    ⨅ x : {x : ι → ℝ // x ≠ 0},
      RCLike.re (@inner ℝ (ι → ℝ) innerProduct.toInner
        (metricPreconditionedOperator M A x) x) /
        @norm (ι → ℝ) normed.toNorm x ^ 2
  have heigen : Module.End.HasEigenvalue
      (metricPreconditionedOperator M A) μ := by
    exact @LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
      ℝ inferInstance (ι → ℝ) normed innerProduct inferInstance
      (metricPreconditionedOperator M A) inferInstance
      (metricPreconditionedOperator_isSymmetric M A hM hA.isHermitian)
  have hquotientNonneg (x : {x : ι → ℝ // x ≠ 0}) :
      0 ≤ RCLike.re (@inner ℝ (ι → ℝ) innerProduct.toInner
        (metricPreconditionedOperator M A x) x) /
        @norm (ι → ℝ) normed.toNorm x ^ 2 := by
    rw [metricPreconditionedOperator_inner_self M A hM hA.isHermitian x,
      metric_norm_sq M hM x]
    exact div_nonneg (hA.dotProduct_mulVec_nonneg x)
      (hM.posSemidef.dotProduct_mulVec_nonneg x)
  letI : Nonempty {x : ι → ℝ // x ≠ 0} := ⟨⟨v, hv⟩⟩
  have hμnonneg : 0 ≤ μ := le_ciInf hquotientNonneg
  refine ⟨μ, heigen, hμnonneg, ?_⟩
  have hb : BddBelow
      (Set.range fun x : {x : ι → ℝ // x ≠ 0} =>
        RCLike.re (@inner ℝ (ι → ℝ) innerProduct.toInner
          (metricPreconditionedOperator M A x) x) /
          @norm (ι → ℝ) normed.toNorm x ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hquotientNonneg x
  have hle : μ ≤
      RCLike.re (@inner ℝ (ι → ℝ) innerProduct.toInner
        (metricPreconditionedOperator M A v) v) /
        @norm (ι → ℝ) normed.toNorm v ^ 2 :=
    ciInf_le hb (⟨v, hv⟩ : {x : ι → ℝ // x ≠ 0})
  rw [metricPreconditionedOperator_inner_self M A hM hA.isHermitian v,
    metric_norm_sq M hM v] at hle
  simpa using hle

/-- Error propagation for one memoryless preconditioned gradient step. -/
noncomputable def metricPreconditionedErrorOperator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) : Module.End ℝ (ι → ℝ) :=
  LinearMap.id - metricPreconditionedOperator M A

/-- A generalized energy eigenvalue `μ` becomes the error-propagation
eigenvalue `1 - μ`. -/
theorem metricPreconditionedErrorOperator_hasEigenvalue_one_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (metricPreconditionedOperator M A) μ) :
    Module.End.HasEigenvalue (metricPreconditionedErrorOperator M A) (1 - μ) := by
  rw [metricPreconditionedErrorOperator,
    show LinearMap.id = (1 : ℝ) • (LinearMap.id :
      Module.End ℝ (ι → ℝ)) by simp,
    Module.End.hasEigenvalue_sub'_iff]
  simpa using hμ

/-! ## The full block-metric class -/

/-- A vector with `blocks` contiguous blocks, each of width `width`.
The first coordinate is the within-block coordinate and the second chooses
the block, matching `Matrix.blockDiagonal`. -/
abbrev UniformBlockVector (width blocks : ℕ) :=
  Fin width × Fin blocks → ℝ

/-- The full block-diagonal metric assembled from arbitrary within-block
matrices. -/
noncomputable def uniformBlockMetric (width blocks : ℕ)
    (localMetric : Fin blocks → Matrix (Fin width) (Fin width) ℝ) :
    Matrix (Fin width × Fin blocks) (Fin width × Fin blocks) ℝ :=
  Matrix.blockDiagonal localMetric

/-- Restriction of a block vector to one contiguous block. -/
def uniformBlockSlice {width blocks : ℕ}
    (x : UniformBlockVector width blocks) (block : Fin blocks) :
    Fin width → ℝ :=
  fun within => x (within, block)

theorem uniformBlockMetric_mulVec_apply (width blocks : ℕ)
    (localMetric : Fin blocks → Matrix (Fin width) (Fin width) ℝ)
    (x : UniformBlockVector width blocks) (within : Fin width)
    (block : Fin blocks) :
    (uniformBlockMetric width blocks localMetric *ᵥ x) (within, block) =
      (localMetric block *ᵥ uniformBlockSlice x block) within := by
  classical
  simp [uniformBlockMetric, Matrix.mulVec, dotProduct,
    uniformBlockSlice, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

/-- The quadratic form of an arbitrary block-diagonal metric is the sum of
the quadratic forms of all its blocks. -/
theorem uniformBlockMetric_quadratic_eq_sum (width blocks : ℕ)
    (localMetric : Fin blocks → Matrix (Fin width) (Fin width) ℝ)
    (x : UniformBlockVector width blocks) :
    star x ⬝ᵥ (uniformBlockMetric width blocks localMetric *ᵥ x) =
      ∑ block : Fin blocks,
        star (uniformBlockSlice x block) ⬝ᵥ
          (localMetric block *ᵥ uniformBlockSlice x block) := by
  classical
  simp only [dotProduct, Fintype.sum_prod_type,
    uniformBlockMetric_mulVec_apply]
  rw [Finset.sum_comm]
  rfl

/-- Arbitrary positive-definite blocks assemble to a positive-definite global
metric.  Thus the quantified class contains every uniform blockwise
preconditioner, including coupled within-block metrics. -/
theorem uniformBlockMetric_posDef (width blocks : ℕ)
    (localMetric : Fin blocks → Matrix (Fin width) (Fin width) ℝ)
    (hlocal : ∀ block, (localMetric block).PosDef) :
    (uniformBlockMetric width blocks localMetric).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_blockDiagonal_iff.mpr
      (fun block => (hlocal block).isHermitian)
  · intro x hx
    rw [uniformBlockMetric_quadratic_eq_sum]
    have hex : ∃ index, x index ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext index
      exact h index
    obtain ⟨⟨within, block⟩, hcoordinate⟩ := hex
    have hslice : uniformBlockSlice x block ≠ 0 := by
      intro hzero
      apply hcoordinate
      exact congrFun hzero within
    apply Finset.sum_pos'
    · intro other _
      exact (hlocal other).posSemidef.dotProduct_mulVec_nonneg _
    · exact ⟨block, Finset.mem_univ _,
        (hlocal block).dotProduct_mulVec_pos hslice⟩

/-! ## A genuinely coupled block fixture -/

/-- A symmetric, non-diagonal positive-definite two-coordinate metric. -/
def coupledTwoMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 2 else 1

theorem coupledTwoMetric_posDef : coupledTwoMetric.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [coupledTwoMetric, eq_comm]
  · intro x hx
    simp only [dotProduct, mulVec, Fin.sum_univ_two]
    norm_num [coupledTwoMetric]
    have hcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoord with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1)]

theorem coupledTwoMetric_has_nonzero_offDiagonal : coupledTwoMetric 0 1 ≠ 0 := by
  norm_num [coupledTwoMetric]

/-- Positive anti-vacuity fixture: repeating the coupled two-coordinate
metric produces a member of the full block-local positive-definite class. -/
theorem coupledTwoMetric_uniformBlock_member (blocks : ℕ) :
    (uniformBlockMetric 2 blocks (fun _ => coupledTwoMetric)).PosDef := by
  exact uniformBlockMetric_posDef 2 blocks _ (fun _ => coupledTwoMetric_posDef)

/-! ## The concrete Dirichlet chain energy -/

/-- Edge indices for a path divided into `blocks + 1` consecutive blocks of
`width + 1` vertices: left boundary, within-block edges, inter-block edges,
and right boundary. -/
abbrev UniformPathEdge (width blocks : ℕ) :=
  Unit ⊕ ((Fin (blocks + 1) × Fin width) ⊕ (Fin blocks ⊕ Unit))

private theorem sum_two_distinct_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (a b : ι) (hab : a ≠ b) :
    (∑ i, if i = a then f i else if i = b then -f i else 0) =
      f a - f b := by
  rw [show (∑ i, if i = a then f i else if i = b then -f i else 0) =
      (∑ i, if i = a then f i else 0) +
        ∑ i, if i = b then -f i else 0 by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hia : i = a
    · subst i
      simp [hab]
    · by_cases hib : i = b <;> simp [hia, hib, hab.symm]]
  simp [sub_eq_add_neg]

/-- Signed edge-vertex incidence matrix for the zero-Dirichlet path. -/
def uniformPathIncidence (width blocks : ℕ) :
    Matrix (UniformPathEdge width blocks)
      (Fin (width + 1) × Fin (blocks + 1)) ℝ :=
  fun edge node =>
    match edge with
    | Sum.inl _ => if node = (0, 0) then 1 else 0
    | Sum.inr (Sum.inl (block, between)) =>
        if node = (between.succ, block) then 1
        else if node = (between.castSucc, block) then -1 else 0
    | Sum.inr (Sum.inr (Sum.inl betweenBlocks)) =>
        if node = (0, betweenBlocks.succ) then 1
        else if node = (Fin.last width, betweenBlocks.castSucc) then -1 else 0
    | Sum.inr (Sum.inr (Sum.inr _)) =>
        if node = (Fin.last width, Fin.last blocks) then 1 else 0

/-- Hessian of the concrete unit path energy, derived as `BᴴB` from the
incidence matrix. -/
noncomputable def uniformPathHessian (width blocks : ℕ) :
    Matrix (Fin (width + 1) × Fin (blocks + 1))
      (Fin (width + 1) × Fin (blocks + 1)) ℝ :=
  (uniformPathIncidence width blocks)ᴴ * uniformPathIncidence width blocks

theorem uniformPathHessian_posSemidef (width blocks : ℕ) :
    (uniformPathHessian width blocks).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem uniformPathIncidence_mulVec_left (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1)) (edgeUnit : Unit) :
    (uniformPathIncidence width blocks *ᵥ x) (Sum.inl edgeUnit) = x (0, 0) := by
  classical
  cases edgeUnit
  simp [uniformPathIncidence, Matrix.mulVec, dotProduct]

theorem uniformPathIncidence_mulVec_internal (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1))
    (block : Fin (blocks + 1)) (between : Fin width) :
    (uniformPathIncidence width blocks *ᵥ x)
        (Sum.inr (Sum.inl (block, between))) =
      x (between.succ, block) - x (between.castSucc, block) := by
  classical
  have hne : (between.succ, block) ≠ (between.castSucc, block) :=
    fun h => (Fin.ne_of_gt between.castSucc_lt_succ) (congrArg Prod.fst h)
  simp only [uniformPathIncidence, Matrix.mulVec, dotProduct,
    ite_mul, one_mul, neg_one_mul, zero_mul]
  exact sum_two_distinct_coordinates x _ _ hne

theorem uniformPathIncidence_mulVec_cross (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1))
    (betweenBlocks : Fin blocks) :
    (uniformPathIncidence width blocks *ᵥ x)
        (Sum.inr (Sum.inr (Sum.inl betweenBlocks))) =
      x (0, betweenBlocks.succ) -
        x (Fin.last width, betweenBlocks.castSucc) := by
  classical
  have hne : (0, betweenBlocks.succ) ≠
      (Fin.last width, betweenBlocks.castSucc) :=
    fun h => (Fin.ne_of_gt betweenBlocks.castSucc_lt_succ)
      (congrArg Prod.snd h)
  simp only [uniformPathIncidence, Matrix.mulVec, dotProduct,
    ite_mul, one_mul, neg_one_mul, zero_mul]
  exact sum_two_distinct_coordinates x _ _ hne

theorem uniformPathIncidence_mulVec_right (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1)) (edgeUnit : Unit) :
    (uniformPathIncidence width blocks *ᵥ x)
        (Sum.inr (Sum.inr (Sum.inr edgeUnit))) =
      x (Fin.last width, Fin.last blocks) := by
  classical
  cases edgeUnit
  simp [uniformPathIncidence, Matrix.mulVec, dotProduct]

/-- The Hessian quadratic form is exactly the squared norm of the residual
vector produced by the incidence matrix. -/
theorem uniformPathHessian_quadratic_eq_incidence_norm (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1)) :
    star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) =
      star (uniformPathIncidence width blocks *ᵥ x) ⬝ᵥ
        (uniformPathIncidence width blocks *ᵥ x) := by
  classical
  unfold uniformPathHessian
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose,
    star_star]

/-- Expanded content of the concrete path energy: two boundary residuals,
all within-block differences, and all inter-block differences. -/
theorem uniformPathHessian_quadratic_eq_edge_sum (width blocks : ℕ)
    (x : UniformBlockVector (width + 1) (blocks + 1)) :
    star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) =
      x (0, 0) ^ 2 +
        (∑ block : Fin (blocks + 1), ∑ between : Fin width,
          (x (between.succ, block) - x (between.castSucc, block)) ^ 2) +
        (∑ betweenBlocks : Fin blocks,
          (x (0, betweenBlocks.succ) -
            x (Fin.last width, betweenBlocks.castSucc)) ^ 2) +
        x (Fin.last width, Fin.last blocks) ^ 2 := by
  rw [uniformPathHessian_quadratic_eq_incidence_norm]
  simp only [dotProduct, Pi.star_apply, star_trivial, ← pow_two,
    Fintype.sum_sum_type, Fintype.sum_unique,
    Fintype.sum_prod_type, uniformPathIncidence_mulVec_left,
    uniformPathIncidence_mulVec_internal,
    uniformPathIncidence_mulVec_cross,
    uniformPathIncidence_mulVec_right]
  ring

/-- Lift one scalar value per block to a vector that is constant inside each
block. -/
def liftUniformBlockProfile {width blocks : ℕ}
    (profile : Fin blocks → ℝ) : UniformBlockVector width blocks :=
  fun node => profile node.2

/-- A constant vector supported on exactly one contiguous block. -/
def singleBlockConstant {width blocks : ℕ}
    (block : Fin blocks) (amplitude : ℝ) : UniformBlockVector width blocks :=
  fun node => if node.2 = block then amplitude else 0

/-- A block-constant profile has no within-block residuals; its fine path
energy is exactly the scalar Dirichlet energy of the block profile. -/
theorem liftUniformBlockProfile_pathEnergy (width blocks : ℕ)
    (profile : Fin (blocks + 1) → ℝ) :
    star (liftUniformBlockProfile (width := width + 1) profile) ⬝ᵥ
        (uniformPathHessian width blocks *ᵥ
          liftUniformBlockProfile (width := width + 1) profile) =
      profile 0 ^ 2 +
        (∑ betweenBlocks : Fin blocks,
          (profile betweenBlocks.succ - profile betweenBlocks.castSucc) ^ 2) +
        profile (Fin.last blocks) ^ 2 := by
  rw [uniformPathHessian_quadratic_eq_edge_sum]
  simp [liftUniformBlockProfile]

/-- Every nonzero block-constant component pays at least its squared
amplitude in the concrete path energy.  This is the local fact that converts
global stability into a denominator bound without assuming a preconditioner
norm estimate. -/
theorem singleBlockConstant_sq_le_pathEnergy (width blocks : ℕ)
    (block : Fin (blocks + 1)) (amplitude : ℝ) :
    amplitude ^ 2 ≤
      star (singleBlockConstant (width := width + 1) block amplitude) ⬝ᵥ
        (uniformPathHessian width blocks *ᵥ
          singleBlockConstant (width := width + 1) block amplitude) := by
  classical
  rw [uniformPathHessian_quadratic_eq_incidence_norm]
  simp only [dotProduct, Pi.star_apply, star_trivial, ← pow_two]
  refine Fin.cases ?_ (fun previous => ?_) block
  · let leftEdge : UniformPathEdge width blocks := Sum.inl ()
    calc
      amplitude ^ 2 =
          (uniformPathIncidence width blocks *ᵥ
            singleBlockConstant (width := width + 1) (0 : Fin (blocks + 1)) amplitude)
              leftEdge ^ 2 := by
                simp [leftEdge, uniformPathIncidence_mulVec_left,
                  singleBlockConstant]
      _ ≤ ∑ edge : UniformPathEdge width blocks,
          (uniformPathIncidence width blocks *ᵥ
            singleBlockConstant (width := width + 1) (0 : Fin (blocks + 1)) amplitude)
              edge ^ 2 := by
        exact Finset.single_le_sum (fun _ _ => sq_nonneg _)
          (Finset.mem_univ leftEdge)
  · let crossEdge : UniformPathEdge width blocks :=
      Sum.inr (Sum.inr (Sum.inl previous))
    calc
      amplitude ^ 2 =
          (uniformPathIncidence width blocks *ᵥ
            singleBlockConstant (width := width + 1) previous.succ amplitude)
              crossEdge ^ 2 := by
                rw [uniformPathIncidence_mulVec_cross]
                have hne : previous.castSucc ≠ previous.succ :=
                  Fin.ne_of_lt previous.castSucc_lt_succ
                simp [singleBlockConstant, hne]
      _ ≤ ∑ edge : UniformPathEdge width blocks,
          (uniformPathIncidence width blocks *ᵥ
            singleBlockConstant (width := width + 1) previous.succ amplitude)
              edge ^ 2 := by
        exact Finset.single_le_sum (fun _ _ => sq_nonneg _)
          (Finset.mem_univ crossEdge)

theorem uniformBlockSlice_singleBlockConstant {width blocks : ℕ}
    (chosen other : Fin blocks) (amplitude : ℝ) :
    uniformBlockSlice (singleBlockConstant (width := width) chosen amplitude) other =
      if other = chosen then (fun _ : Fin width => amplitude) else 0 := by
  funext within
  by_cases h : other = chosen <;>
    simp [uniformBlockSlice, singleBlockConstant, h]

theorem uniformBlockMetric_singleBlockConstant (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (block : Fin (blocks + 1)) (amplitude : ℝ) :
    star (singleBlockConstant (width := width + 1) block amplitude) ⬝ᵥ
        (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ
          singleBlockConstant (width := width + 1) block amplitude) =
      star (fun _ : Fin (width + 1) => amplitude) ⬝ᵥ
        (localMetric block *ᵥ (fun _ : Fin (width + 1) => amplitude)) := by
  classical
  rw [uniformBlockMetric_quadratic_eq_sum]
  have hterm (other : Fin (blocks + 1)) :
      star (uniformBlockSlice
          (singleBlockConstant (width := width + 1) block amplitude) other) ⬝ᵥ
          (localMetric other *ᵥ uniformBlockSlice
            (singleBlockConstant (width := width + 1) block amplitude) other) =
        if other = block then
          star (fun _ : Fin (width + 1) => amplitude) ⬝ᵥ
            (localMetric block *ᵥ (fun _ : Fin (width + 1) => amplitude))
        else 0 := by
    by_cases h : other = block
    · subst other
      simp [uniformBlockSlice_singleBlockConstant]
    · simp [uniformBlockSlice_singleBlockConstant, h]
  simp_rw [hterm]
  simp

theorem uniformBlockMetric_liftProfile (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (profile : Fin (blocks + 1) → ℝ) :
    star (liftUniformBlockProfile (width := width + 1) profile) ⬝ᵥ
        (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ
          liftUniformBlockProfile (width := width + 1) profile) =
      ∑ block : Fin (blocks + 1),
        star (fun _ : Fin (width + 1) => profile block) ⬝ᵥ
          (localMetric block *ᵥ
            (fun _ : Fin (width + 1) => profile block)) := by
  rw [uniformBlockMetric_quadratic_eq_sum]
  rfl

/-- Stability of the full memoryless step forces every local block metric to
pay for a constant displacement on that block.  The estimate is derived
from the concrete path energy and does not assume an operator-norm bound on
the preconditioner. -/
theorem stable_uniformBlockMetric_profile_denominator (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (hstable : ∀ x : UniformBlockVector (width + 1) (blocks + 1),
      star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) ≤
        2 * (star x ⬝ᵥ
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ x)))
    (profile : Fin (blocks + 1) → ℝ) :
    (∑ block, profile block ^ 2) ≤
      2 * (star (liftUniformBlockProfile (width := width + 1) profile) ⬝ᵥ
        (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ
          liftUniformBlockProfile (width := width + 1) profile)) := by
  rw [uniformBlockMetric_liftProfile]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro block _
  calc
    profile block ^ 2 ≤
        star (singleBlockConstant (width := width + 1) block (profile block)) ⬝ᵥ
          (uniformPathHessian width blocks *ᵥ
            singleBlockConstant (width := width + 1) block (profile block)) :=
      singleBlockConstant_sq_le_pathEnergy width blocks block (profile block)
    _ ≤ 2 *
        (star (singleBlockConstant (width := width + 1) block (profile block)) ⬝ᵥ
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ
            singleBlockConstant (width := width + 1) block (profile block))) :=
      hstable _
    _ = 2 *
        (star (fun _ : Fin (width + 1) => profile block) ⬝ᵥ
          (localMetric block *ᵥ
            (fun _ : Fin (width + 1) => profile block))) := by
      rw [uniformBlockMetric_singleBlockConstant]

/-- Variational block-local rate ceiling.  Any nonzero block profile with
Dirichlet energy at most `ε` times its squared mass produces a genuine
preconditioned eigenvalue at most `2ε`, for every stable positive-definite
block metric. -/
theorem stable_uniformBlockMetric_has_slow_eigenvalue_of_profile
    (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (hlocal : ∀ block, (localMetric block).PosDef)
    (hstable : ∀ x : UniformBlockVector (width + 1) (blocks + 1),
      star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) ≤
        2 * (star x ⬝ᵥ
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ x)))
    (profile : Fin (blocks + 1) → ℝ) (hprofile : profile ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hprofileEnergy :
      star (liftUniformBlockProfile (width := width + 1) profile) ⬝ᵥ
          (uniformPathHessian width blocks *ᵥ
            liftUniformBlockProfile (width := width + 1) profile) ≤
        ε * ∑ block, profile block ^ 2) :
    ∃ μ rate : ℝ,
      Module.End.HasEigenvalue
        (metricPreconditionedOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) μ ∧
      Module.End.HasEigenvalue
        (metricPreconditionedErrorOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) rate ∧
      rate = 1 - μ ∧ 0 ≤ μ ∧ μ ≤ 2 * ε := by
  let M := uniformBlockMetric (width + 1) (blocks + 1) localMetric
  let A := uniformPathHessian width blocks
  let v := liftUniformBlockProfile (width := width + 1) profile
  have hM : M.PosDef := uniformBlockMetric_posDef _ _ _ hlocal
  have hA : A.PosSemidef := uniformPathHessian_posSemidef width blocks
  have hv : v ≠ 0 := by
    intro hzero
    apply hprofile
    funext block
    have hcoordinate := congrFun hzero ((0 : Fin (width + 1)), block)
    simpa [v, liftUniformBlockProfile] using hcoordinate
  obtain ⟨μ, hμ, hμnonneg, hμle⟩ :=
    exists_preconditioned_eigenvalue_le_generalizedRayleigh
      M A hM hA v hv
  refine ⟨μ, 1 - μ, hμ,
    metricPreconditionedErrorOperator_hasEigenvalue_one_sub M A μ hμ,
    rfl, hμnonneg, ?_⟩
  let mass : ℝ := ∑ block, profile block ^ 2
  let denominator : ℝ := star v ⬝ᵥ (M *ᵥ v)
  let numerator : ℝ := star v ⬝ᵥ (A *ᵥ v)
  have hdenominator : 0 < denominator := hM.dotProduct_mulVec_pos hv
  have hmass : mass ≤ 2 * denominator := by
    simpa [mass, denominator, M, v] using
      stable_uniformBlockMetric_profile_denominator
        width blocks localMetric hstable profile
  have hnumerator : numerator ≤ ε * mass := by
    simpa [numerator, A, v] using hprofileEnergy
  have hscaled : ε * mass ≤ 2 * ε * denominator := by
    nlinarith [mul_le_mul_of_nonneg_left hmass hε]
  have hquotient : numerator / denominator ≤ 2 * ε := by
    apply (div_le_iff₀ hdenominator).mpr
    nlinarith
  exact hμle.trans hquotient

/-! ## The smooth block profile -/

/-- Discrete Green identity on `interior` unconstrained vertices, including
the two endpoint flux terms.  This algebraic form is reusable independently
of the sine witness. -/
theorem discrete_dirichlet_green_identity (interior : ℕ) (v : ℕ → ℝ) :
    (∑ edge ∈ Finset.range (interior + 1),
        (v (edge + 1) - v edge) ^ 2) =
      (∑ node ∈ Finset.range interior,
        v (node + 1) *
          (2 * v (node + 1) - v node - v (node + 2))) +
      v 0 * (v 0 - v 1) +
      v (interior + 1) * (v (interior + 1) - v interior) := by
  induction interior with
  | zero =>
      simp
      ring
  | succ interior ih =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      ring

theorem pathSlowMode_discrete_laplacian (segments node : ℕ)
    (hnode : node ≠ 0) :
    2 * pathSlowMode segments node - pathSlowMode segments (node - 1) -
        pathSlowMode segments (node + 1) =
      2 * (1 - pathRelaxationRate segments) * pathSlowMode segments node := by
  have heigen := pathSlowMode_interior_eigenrelation segments node hnode
  linarith

/-- Exact Dirichlet energy of the first sine mode on the `blocks + 1`
interior block coordinates. -/
theorem pathSlowMode_dirichlet_energy_exact (blocks : ℕ) :
    (∑ edge ∈ Finset.range (blocks + 2),
        (pathSlowMode (blocks + 2) (edge + 1) -
          pathSlowMode (blocks + 2) edge) ^ 2) =
      2 * (1 - pathRelaxationRate (blocks + 2)) *
        ∑ node ∈ Finset.range (blocks + 1),
          pathSlowMode (blocks + 2) (node + 1) ^ 2 := by
  let v := pathSlowMode (blocks + 2)
  have hsegments : 0 < blocks + 2 := by omega
  have hboundary := pathSlowMode_boundary_zero (blocks + 2) hsegments
  rw [show blocks + 2 = (blocks + 1) + 1 by omega]
  rw [discrete_dirichlet_green_identity (blocks + 1) v]
  have hright : v (blocks + 1 + 1) = 0 := by
    simpa [v] using hboundary.2
  have hleft : v 0 = 0 := by
    simpa [v] using hboundary.1
  rw [hright, hleft]
  simp only [zero_mul, zero_sub, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro node hnode
  have hlaplacian := pathSlowMode_discrete_laplacian
    (blocks + 2) (node + 1) (by omega)
  have hsub : node + 1 - 1 = node := by omega
  rw [hsub] at hlaplacian
  dsimp [v]
  norm_num [Nat.add_assoc] at hlaplacian ⊢
  rw [hlaplacian]
  ring

/-- First sine mode sampled once per block. -/
noncomputable def blockSineProfile (blocks : ℕ) : Fin (blocks + 1) → ℝ :=
  fun block => pathSlowMode (blocks + 2) (block.val + 1)

theorem blockSineProfile_nonzero (blocks : ℕ) : blockSineProfile blocks ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (0 : Fin (blocks + 1))
  have hden : (1 : ℝ) < (blocks : ℝ) + 2 := by
    nlinarith [Nat.cast_nonneg blocks (α := ℝ)]
  have hanglePos : 0 < Real.pi / ((blocks : ℝ) + 2) := by
    positivity
  have hangleLt : Real.pi / ((blocks : ℝ) + 2) < Real.pi :=
    div_lt_self Real.pi_pos hden
  have hsin := Real.sin_pos_of_pos_of_lt_pi hanglePos hangleLt
  norm_num [blockSineProfile, pathSlowMode] at hcoordinate
  exact hsin.ne' hcoordinate

theorem blockSineProfile_pathEnergy_exact (width blocks : ℕ) :
    star (liftUniformBlockProfile (width := width + 1)
        (blockSineProfile blocks)) ⬝ᵥ
        (uniformPathHessian width blocks *ᵥ
          liftUniformBlockProfile (width := width + 1)
            (blockSineProfile blocks)) =
      2 * (1 - pathRelaxationRate (blocks + 2)) *
        ∑ block, blockSineProfile blocks block ^ 2 := by
  rw [liftUniformBlockProfile_pathEnergy]
  have hexact := pathSlowMode_dirichlet_energy_exact blocks
  conv_lhs at hexact =>
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ]
  have hboundary := pathSlowMode_boundary_zero (blocks + 2) (by omega)
  rw [hboundary.1, hboundary.2] at hexact
  norm_num [Nat.add_assoc] at hexact
  have hcross :
      (∑ between : Fin blocks,
        (blockSineProfile blocks between.succ -
          blockSineProfile blocks between.castSucc) ^ 2) =
        ∑ i ∈ Finset.range blocks,
          (pathSlowMode (blocks + 2) (i + 2) -
            pathSlowMode (blocks + 2) (i + 1)) ^ 2 := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < blocks := Finset.mem_range.mp hi
    simp [blockSineProfile, hil, Nat.add_assoc]
  have hmass :
      (∑ block : Fin (blocks + 1), blockSineProfile blocks block ^ 2) =
        ∑ i ∈ Finset.range (blocks + 1),
          pathSlowMode (blocks + 2) (i + 1) ^ 2 := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < blocks + 1 := Finset.mem_range.mp hi
    simp [blockSineProfile, hil]
  rw [hcross, hmass]
  simpa [blockSineProfile, Nat.add_assoc, add_comm, add_left_comm, add_assoc]
    using hexact

/-- L2 crown in block-count form.  Every stable memoryless preconditioned
Richardson step whose metric is block diagonal with fixed block width has an
actual error mode whose gap is at most
`2 * (π / (numberOfBlocks + 1))²`. -/
theorem stable_uniformBlockMetric_spectralGap_ceiling
    (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (hlocal : ∀ block, (localMetric block).PosDef)
    (hstable : ∀ x : UniformBlockVector (width + 1) (blocks + 1),
      star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) ≤
        2 * (star x ⬝ᵥ
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ x))) :
    ∃ μ rate : ℝ,
      Module.End.HasEigenvalue
        (metricPreconditionedOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) μ ∧
      Module.End.HasEigenvalue
        (metricPreconditionedErrorOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) rate ∧
      rate = 1 - μ ∧ 0 ≤ μ ∧
      μ ≤ 2 * (Real.pi / ((blocks + 2 : ℕ) : ℝ)) ^ 2 := by
  apply stable_uniformBlockMetric_has_slow_eigenvalue_of_profile
    width blocks localMetric hlocal hstable
    (blockSineProfile blocks) (blockSineProfile_nonzero blocks)
    ((Real.pi / ((blocks + 2 : ℕ) : ℝ)) ^ 2) (sq_nonneg _)
  rw [blockSineProfile_pathEnergy_exact]
  let mass : ℝ := ∑ block, blockSineProfile blocks block ^ 2
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hgap := (pathRelaxationRate_gap_bound (blocks + 2)).2
  change 2 * (1 - pathRelaxationRate (blocks + 2)) * mass ≤
    (Real.pi / ((blocks + 2 : ℕ) : ℝ)) ^ 2 * mass
  have hcoefficient :
      2 * (1 - pathRelaxationRate (blocks + 2)) ≤
        (Real.pi / ((blocks + 2 : ℕ) : ℝ)) ^ 2 := by
    linarith
  exact mul_le_mul_of_nonneg_right hcoefficient hmass

theorem blockCount_ceiling_le_totalDepth_ceiling (width blocks : ℕ) :
    2 * (Real.pi / ((blocks + 2 : ℕ) : ℝ)) ^ 2 ≤
      2 * Real.pi ^ 2 * ((width + 1 : ℕ) : ℝ) ^ 2 /
        (((width + 1) * (blocks + 1) : ℕ) : ℝ) ^ 2 := by
  have hwidth : (((width + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hblocks : (((blocks + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have heq :
      2 * Real.pi ^ 2 * ((width + 1 : ℕ) : ℝ) ^ 2 /
          (((width + 1) * (blocks + 1) : ℕ) : ℝ) ^ 2 =
        2 * (Real.pi / ((blocks + 1 : ℕ) : ℝ)) ^ 2 := by
    norm_num [Nat.cast_mul]
    field_simp [hwidth, hblocks]
  rw [heq]
  have hdenominator : ((blocks + 1 : ℕ) : ℝ) ≤
      ((blocks + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show blocks + 1 ≤ blocks + 2 by omega)
  have hdiv : Real.pi / ((blocks + 2 : ℕ) : ℝ) ≤
      Real.pi / ((blocks + 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hdenominator
  have hleft : 0 ≤ Real.pi / ((blocks + 2 : ℕ) : ℝ) := by positivity
  have hright : 0 ≤ Real.pi / ((blocks + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- L2 crown in total-depth form.  For total interior depth
`n = blockWidth * numberOfBlocks`, the explicit ceiling is
`2π² * blockWidth² / n²`. -/
theorem stable_uniformBlockMetric_totalDepth_spectralGap_ceiling
    (width blocks : ℕ)
    (localMetric : Fin (blocks + 1) →
      Matrix (Fin (width + 1)) (Fin (width + 1)) ℝ)
    (hlocal : ∀ block, (localMetric block).PosDef)
    (hstable : ∀ x : UniformBlockVector (width + 1) (blocks + 1),
      star x ⬝ᵥ (uniformPathHessian width blocks *ᵥ x) ≤
        2 * (star x ⬝ᵥ
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric *ᵥ x))) :
    ∃ μ rate : ℝ,
      Module.End.HasEigenvalue
        (metricPreconditionedOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) μ ∧
      Module.End.HasEigenvalue
        (metricPreconditionedErrorOperator
          (uniformBlockMetric (width + 1) (blocks + 1) localMetric)
          (uniformPathHessian width blocks)) rate ∧
      rate = 1 - μ ∧ 0 ≤ μ ∧
      μ ≤ 2 * Real.pi ^ 2 * ((width + 1 : ℕ) : ℝ) ^ 2 /
        (((width + 1) * (blocks + 1) : ℕ) : ℝ) ^ 2 := by
  obtain ⟨μ, rate, hμ, hrate, hratedef, hμnonneg, hgap⟩ :=
    stable_uniformBlockMetric_spectralGap_ceiling
      width blocks localMetric hlocal hstable
  exact ⟨μ, rate, hμ, hrate, hratedef, hμnonneg,
    hgap.trans (blockCount_ceiling_le_totalDepth_ceiling width blocks)⟩

/-! ## Compatibility fixtures for the earlier depth no-go results -/

/-- Restatement fixture for the scalar-Jacobi endpoint (`w = 1`): its exact
first-mode rate is `cos (π / n)`, with the same inverse-square gap law as the
block-local ceiling. -/
theorem scalarJacobi_inverseSquareGap (segments : ℕ) :
    0 ≤ 1 - pathRelaxationRate segments ∧
      1 - pathRelaxationRate segments ≤
        (Real.pi / (segments : ℝ)) ^ 2 / 2 := by
  exact pathRelaxationRate_gap_bound segments

/-- Restatement fixture for the inference-rate no-go: equal depth credit is
possible exactly when every rate used along the chain is one. -/
theorem localRate_equalization_noGo
    (inferenceRate : ℕ → ℝ) (depth : ℕ) :
    InferenceRatesEqualizeDepthCredit inferenceRate depth ↔
      ∀ j, 0 < j → j ≤ depth → inferenceRate j = 1 := by
  exact inferenceRatesEqualizeDepthCredit_iff_all_unit inferenceRate depth

/-- Restatement fixture for the Depth-μP no-go: its paired width/depth
factors cancel each other and leave geometric inference attenuation intact. -/
theorem depthMuP_localityAttenuation_unchanged
    (width depth distance : ℕ) (inferenceRate : ℝ)
    (hwidth : 0 < width) (hdepth : 0 < depth) :
    depthMuPAdamLearningRateScale width depth *
        depthMuPHiddenMultiplier width depth * inferenceRate ^ distance =
      inferenceRate ^ distance := by
  exact depthMuPScaling_leaves_depthCredit_unchanged
    width depth distance inferenceRate hwidth hdepth

#print axioms stable_uniformBlockMetric_spectralGap_ceiling
#print axioms stable_uniformBlockMetric_totalDepth_spectralGap_ceiling

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
