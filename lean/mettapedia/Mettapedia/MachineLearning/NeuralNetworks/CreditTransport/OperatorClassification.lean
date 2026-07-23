import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrecisionSemantics
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DepthScalingVector
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom
import Mathlib.Analysis.Matrix.PosDef

/-!
# Linear operator classification

This file classifies finite-dimensional affine dynamics using independently
checkable certificates.  Euclidean integrability is defined by vanishing work
around every parallelogram and then characterized by matrix symmetry.  Metric
gradient structure and monotonicity remain separate predicates: a field may
fail Euclidean integrability while being a gradient flow in a positive-definite
metric, and a monotone operator may preserve norm instead of contracting.

The exact two-dimensional fixtures distinguish gradient, metric-gradient,
primal-dual, rotational, and unconstrained recurrence behavior without using
shared fixed points as evidence of shared operator class.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace OperatorClassification

open Matrix
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

noncomputable section

/-! ## Work around affine loops -/

variable {Index : Type*} [Fintype Index]

/-- Affine vector field with linear part `A` and offset `b`. -/
def affineField (A : Matrix Index Index ℝ) (b x : Index → ℝ) : Index → ℝ :=
  A *ᵥ x + b

/-- Exact line integral of an affine field along the unit-speed segment from
`x` to `x + d`. -/
def affineSegmentWork (A : Matrix Index Index ℝ) (b x d : Index → ℝ) : ℝ :=
  affineField A b x ⬝ᵥ d + (1 / 2 : ℝ) * ((A *ᵥ d) ⬝ᵥ d)

/-- Oriented work around the parallelogram based at `x` with sides `u` and
`v`. -/
def parallelogramCirculation (A : Matrix Index Index ℝ)
    (b x u v : Index → ℝ) : ℝ :=
  affineSegmentWork A b x u +
    affineSegmentWork A b (x + u) v +
    affineSegmentWork A b (x + u + v) (-u) +
    affineSegmentWork A b (x + v) (-v)

/-- Observable Euclidean integrability criterion for an affine field: every
parallelogram has zero circulation. -/
def EuclideanIntegrable (A : Matrix Index Index ℝ) (b : Index → ℝ) : Prop :=
  ∀ x u v, parallelogramCirculation A b x u v = 0

/-- Affine offsets and segment self-terms cancel around a parallelogram; only
the antisymmetric bilinear part remains. -/
theorem parallelogramCirculation_eq
    (A : Matrix Index Index ℝ) (b x u v : Index → ℝ) :
    parallelogramCirculation A b x u v =
      (A *ᵥ u) ⬝ᵥ v - (A *ᵥ v) ⬝ᵥ u := by
  simp only [parallelogramCirculation, affineSegmentWork, affineField,
    Matrix.mulVec_add, Matrix.mulVec_neg, add_dotProduct, neg_dotProduct,
    dotProduct_neg]
  ring

/-- Vanishing affine circulation is equivalent to symmetry of the linear
Jacobian.  This derives integrability from segment work rather than defining
it to be symmetry. -/
theorem euclideanIntegrable_iff_isSymm
    [DecidableEq Index]
    (A : Matrix Index Index ℝ) (b : Index → ℝ) :
    EuclideanIntegrable A b ↔ A.IsSymm := by
  constructor
  · intro hintegrable
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    have hloop := hintegrable 0 (Pi.single j 1) (Pi.single i 1)
    rw [parallelogramCirculation_eq] at hloop
    have hij : A i j - A j i = 0 := by
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hloop
    linarith
  · intro hsymm x u v
    rw [parallelogramCirculation_eq]
    have hbilinear : (A *ᵥ u) ⬝ᵥ v = (A *ᵥ v) ⬝ᵥ u := by
      calc
        (A *ᵥ u) ⬝ᵥ v = v ⬝ᵥ (A *ᵥ u) := dotProduct_comm _ _
        _ = u ⬝ᵥ (A.transpose *ᵥ v) :=
          (dotProduct_transpose_mulVec A u v).symm
        _ = u ⬝ᵥ (A *ᵥ v) := by rw [hsymm.eq]
        _ = (A *ᵥ v) ⬝ᵥ u := dotProduct_comm _ _
    exact sub_eq_zero.mpr hbilinear

/-! ## Metric-gradient certificates -/

/-- A linear flow is a metric gradient flow when it factors as `-M Q`, with
positive-definite metric/preconditioner `M` and symmetric positive-semidefinite
quadratic energy matrix `Q`. -/
def IsMetricGradientFlow (A : Matrix Index Index ℝ) : Prop :=
  ∃ M Q : Matrix Index Index ℝ,
    M.PosDef ∧ Q.PosSemidef ∧ A = -(M * Q)

/-- An SPD metric is invertible, so left pullback of a certified metric
gradient flow recovers the symmetric energy matrix exactly. -/
theorem inverse_metric_recovers_energy
    [DecidableEq Index]
    (M Q A : Matrix Index Index ℝ) (hM : M.PosDef)
    (hA : A = -(M * Q)) :
    -(M⁻¹ * A) = Q := by
  letI := hM.isUnit.invertible
  rw [hA]
  simp

/-! ## Monotone linear operators -/

/-- Symmetric part of a real linear operator. -/
def symmetricPart (B : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  (1 / 2 : ℝ) • (B + B.transpose)

/-- Monotonicity of a linear operator, reduced to its quadratic form. -/
def LinearMonotone (B : Matrix Index Index ℝ) : Prop :=
  ∀ x : Index → ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x)

omit [Fintype Index] in
theorem symmetricPart_isHermitian (B : Matrix Index Index ℝ) :
    (symmetricPart B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [symmetricPart]
  ring

/-- The skew part contributes zero to a real quadratic form. -/
theorem dotProduct_symmetricPart_mulVec
    (B : Matrix Index Index ℝ) (x : Index → ℝ) :
    x ⬝ᵥ (symmetricPart B *ᵥ x) = x ⬝ᵥ (B *ᵥ x) := by
  simp only [symmetricPart, Matrix.smul_mulVec, Matrix.add_mulVec,
    dotProduct_smul, dotProduct_add]
  have htranspose : x ⬝ᵥ (B.transpose *ᵥ x) = x ⬝ᵥ (B *ᵥ x) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [htranspose]
  ring

/-- Exact linear criterion: monotonicity is equivalent to positive
semidefiniteness of the symmetric operator part. -/
theorem linearMonotone_iff_symmetricPart_posSemidef
    (B : Matrix Index Index ℝ) :
    LinearMonotone B ↔ (symmetricPart B).PosSemidef := by
  constructor
  · intro hmonotone
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (symmetricPart_isHermitian B)
    intro x
    simpa [dotProduct_symmetricPart_mulVec] using hmonotone x
  · intro hpositive x
    rw [← dotProduct_symmetricPart_mulVec]
    exact hpositive.dotProduct_mulVec_nonneg x

/-! ## Exact two-dimensional boundary fixtures -/

/-- Convex Euclidean-gradient flow `-(diag 1 2)`. -/
def euclideanGradientFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 0; 0, -2]

/-- Positive-definite metric for the nonsymmetric metric-gradient fixture. -/
def metricFixture : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 1]

/-- Positive-definite quadratic energy for the metric-gradient fixture. -/
def metricEnergyFixture : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 2]

/-- Nonsymmetric flow `-M Q`. -/
def metricGradientFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2, -2; -1, -2]

/-- Sign-adjusted KKT operator for `min h²/2` subject to `h = 0`. -/
def primalDualOperator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; -1, 0]

/-- Corresponding descent-ascent field. -/
def primalDualFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, -1; 1, 0]

/-- Pure rotation field. -/
def rotationFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- Sign-adjusted pure rotation operator. -/
def rotationOperator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

/-- Expanding nonsymmetric recurrence with indefinite sign-adjusted symmetric
part. -/
def unconstrainedFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 3; 0, 1]

theorem euclideanGradientFlow_integrable :
    EuclideanIntegrable euclideanGradientFlow 0 := by
  rw [euclideanIntegrable_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [euclideanGradientFlow]

theorem metricFixture_posDef : metricFixture.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [metricFixture]
  · intro x hx
    simp [metricFixture, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hcoordinate : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoordinate with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1)]

theorem metricEnergyFixture_posSemidef : metricEnergyFixture.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [metricEnergyFixture]
  · intro x
    simp [metricEnergyFixture, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem metricGradientFlow_factorization :
    metricGradientFlow = -(metricFixture * metricEnergyFixture) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [metricGradientFlow, metricFixture, metricEnergyFixture,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem metricGradientFlow_certificate :
    IsMetricGradientFlow metricGradientFlow := by
  exact ⟨metricFixture, metricEnergyFixture, metricFixture_posDef,
    metricEnergyFixture_posSemidef, metricGradientFlow_factorization⟩

theorem metricGradientFlow_not_euclideanIntegrable :
    ¬ EuclideanIntegrable metricGradientFlow 0 := by
  rw [euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [metricGradientFlow] at h01

theorem metricGradientFlow_inverse_recovers_energy :
    -(metricFixture⁻¹ * metricGradientFlow) = metricEnergyFixture := by
  exact inverse_metric_recovers_energy metricFixture metricEnergyFixture
    metricGradientFlow metricFixture_posDef metricGradientFlow_factorization

theorem primalDualOperator_monotone : LinearMonotone primalDualOperator := by
  intro x
  simp [primalDualOperator, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0)]

theorem primalDualFlow_not_euclideanIntegrable :
    ¬ EuclideanIntegrable primalDualFlow 0 := by
  rw [euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [primalDualFlow] at h01

theorem rotationOperator_monotone : LinearMonotone rotationOperator := by
  intro x
  simp [rotationOperator, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  ring_nf
  exact le_rfl

/-- Pure rotation preserves squared Euclidean norm for every state. -/
theorem rotationFlow_preserves_squaredNorm (x : Fin 2 → ℝ) :
    (rotationFlow *ᵥ x) ⬝ᵥ (rotationFlow *ᵥ x) = x ⬝ᵥ x := by
  simp [rotationFlow, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Monotonicity does not imply strict norm contraction: the explicit
nonzero state `(3,4)` is rotated from norm squared `25` to norm squared `25`. -/
theorem monotonicity_does_not_imply_contraction_negativeExample :
    LinearMonotone rotationOperator ∧
      let x : Fin 2 → ℝ := ![3, 4]
      x ≠ 0 ∧
        (rotationFlow *ᵥ x) ⬝ᵥ (rotationFlow *ᵥ x) = x ⬝ᵥ x := by
  refine ⟨rotationOperator_monotone, ?_⟩
  dsimp
  constructor
  · intro hx
    have h0 := congrFun hx 0
    norm_num at h0
  · exact rotationFlow_preserves_squaredNorm ![3, 4]

/-- The Euclidean gradient and rotation fields have the same fixed point at
the origin. -/
theorem distinctOperatorClasses_share_fixedPoint :
    affineField euclideanGradientFlow 0 0 = 0 ∧
      affineField rotationFlow 0 0 = 0 := by
  constructor <;> ext i <;> simp [affineField]

/-- Equal fixed points do not determine operator class: one explicit field is
Euclidean-integrable and the other is not. -/
theorem equalFixedPoint_does_not_imply_equalOperatorClass_negativeExample :
    affineField euclideanGradientFlow 0 0 = 0 ∧
      affineField rotationFlow 0 0 = 0 ∧
      EuclideanIntegrable euclideanGradientFlow 0 ∧
      ¬ EuclideanIntegrable rotationFlow 0 := by
  refine ⟨distinctOperatorClasses_share_fixedPoint.1,
    distinctOperatorClasses_share_fixedPoint.2,
    euclideanGradientFlow_integrable, ?_⟩
  rw [euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [rotationFlow] at h01

/-- The unconstrained recurrence fails the monotonicity certificate after
sign adjustment. -/
theorem unconstrainedFlow_not_monotone_negativeExample :
    ¬ LinearMonotone (-unconstrainedFlow) := by
  intro hmonotone
  have h := hmonotone ![1, 1]
  norm_num [unconstrainedFlow, LinearMonotone, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two] at h

theorem unconstrainedFlow_not_euclideanIntegrable :
    ¬ EuclideanIntegrable unconstrainedFlow 0 := by
  rw [euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [unconstrainedFlow] at h01

/-! ## Proof-carrying CAROM classification -/

/-- Independent certificates that may be attached to a real linearization.
The constructors are intentionally non-exclusive: one operator can carry more
than one valid certificate. -/
inductive LinearOperatorCertificate {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (A : Matrix Index Index ℝ) where
  | euclideanGradient
      (certificate : EuclideanIntegrable A 0)
  | metricGradient
      (certificate : IsMetricGradientFlow A)
  | signAdjustedMonotone
      (certificate : LinearMonotone (-A))

/-- A conservative classification result is either a nonempty collection of
proof-carrying certificates or an explicit unresolved result. -/
inductive LinearClassification {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (A : Matrix Index Index ℝ) where
  | resolved
      (certificates : List (LinearOperatorCertificate A))
      (nonempty : certificates ≠ [])
  | unresolved

/-- Convert supplied certificates into a classification without guessing
missing structure. -/
def classifyFromCertificates {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (A : Matrix Index Index ℝ)
    (certificates : List (LinearOperatorCertificate A)) :
    LinearClassification A :=
  match certificates with
  | [] => .unresolved
  | certificate :: remaining =>
      .resolved (certificate :: remaining) (by simp)

/-- Real differentiable linearization of the exact structural CAROM step.
The derivative equality is supplied as a certificate because arbitrary
attention, transforms, and gates need not be differentiable or affine. -/
structure RealCaromLinearization
    (Slot Operator : Type*)
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Operator] [Nonempty Operator] where
  mechanisms : Carom.Mechanisms Slot Operator ℝ
  center : Slot → ℝ
  jacobian : Matrix Slot Slot ℝ
  hasFDerivAt_step :
    HasFDerivAt mechanisms.toGatedOperatorFamily.step
      (matrixContinuousLinearMap jacobian) center

namespace RealCaromLinearization

variable {Slot Operator : Type*}
  [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
  [Fintype Operator] [Nonempty Operator]

/-- Classify a CAROM linearization solely from the certificates actually
established for its Jacobian. -/
def classify (linearization : RealCaromLinearization Slot Operator)
    (certificates : List
      (LinearOperatorCertificate linearization.jacobian)) :
    LinearClassification linearization.jacobian :=
  classifyFromCertificates linearization.jacobian certificates

/-- With no integrability, metric, or monotonicity proof supplied, a CAROM
linearization remains explicitly unresolved. -/
theorem classify_withoutCertificates_unresolved
    (linearization : RealCaromLinearization Slot Operator) :
    linearization.classify [] = LinearClassification.unresolved := by
  rfl

end RealCaromLinearization

/-- The unconstrained fixture demonstrates why `unresolved` is substantive:
two major certificates are actually refuted, while no metric factorization is
asserted either way. -/
theorem unconstrainedFixture_refutes_two_certificates :
    ¬ EuclideanIntegrable unconstrainedFlow 0 ∧
      ¬ LinearMonotone (-unconstrainedFlow) :=
  ⟨unconstrainedFlow_not_euclideanIntegrable,
    unconstrainedFlow_not_monotone_negativeExample⟩

/-! ## Point-local nonlinear classification -/

/-- A nonlinear field has a symmetric Jacobian at one point when an actual
Fréchet derivative is represented there by a symmetric matrix. -/
def SymmetricJacobianAt {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (field : (Index → ℝ) → (Index → ℝ)) (center : Index → ℝ) : Prop :=
  ∃ jacobian : Matrix Index Index ℝ,
    HasFDerivAt field (matrixContinuousLinearMap jacobian) center ∧
      jacobian.IsSymm

/-- Point-local sign-adjusted monotonicity uses the actual derivative matrix;
it is not a global nonlinear monotonicity claim. -/
def MonotoneSignAdjustedJacobianAt {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (field : (Index → ℝ) → (Index → ℝ)) (center : Index → ℝ) : Prop :=
  ∃ jacobian : Matrix Index Index ℝ,
    HasFDerivAt field (matrixContinuousLinearMap jacobian) center ∧
      LinearMonotone (-jacobian)

theorem symmetricJacobianAt_of_matrixDerivative
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (field : (Index → ℝ) → (Index → ℝ)) (center : Index → ℝ)
    (jacobian : Matrix Index Index ℝ)
    (hderivative : HasFDerivAt field
      (matrixContinuousLinearMap jacobian) center)
    (hsymmetric : jacobian.IsSymm) :
    SymmetricJacobianAt field center :=
  ⟨jacobian, hderivative, hsymmetric⟩

theorem monotoneSignAdjustedJacobianAt_of_matrixDerivative
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (field : (Index → ℝ) → (Index → ℝ)) (center : Index → ℝ)
    (jacobian : Matrix Index Index ℝ)
    (hderivative : HasFDerivAt field
      (matrixContinuousLinearMap jacobian) center)
    (hmonotone : LinearMonotone (-jacobian)) :
    MonotoneSignAdjustedJacobianAt field center :=
  ⟨jacobian, hderivative, hmonotone⟩

/-- Nonlinear cross-coordinate shear used to separate point-local from global
classification. -/
def quadraticShear (state : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun coordinate => if coordinate = 0 then 0 else state 0 ^ 2

/-- The shear has the symmetric zero Jacobian at the origin. -/
theorem quadraticShear_hasFDerivAt_zero :
    HasFDerivAt quadraticShear
      (matrixContinuousLinearMap (0 : Matrix (Fin 2) (Fin 2) ℝ)) 0 := by
  have hzero : HasFDerivAt quadraticShear
      (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) 0 := by
    rw [hasFDerivAt_pi']
    intro coordinate
    fin_cases coordinate
    · simpa [quadraticShear] using
        (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : Fin 2 → ℝ))
    · simpa [quadraticShear] using
        ((hasFDerivAt_apply (𝕜 := ℝ) 0 (0 : Fin 2 → ℝ)).pow 2)
  simpa [matrixContinuousLinearMap, Matrix.toLin'_apply'] using hzero

theorem quadraticShear_symmetricJacobianAt_zero :
    SymmetricJacobianAt quadraticShear 0 := by
  refine symmetricJacobianAt_of_matrixDerivative quadraticShear 0 0
    quadraticShear_hasFDerivAt_zero ?_
  exact Matrix.isSymm_zero

/-- The point-local certificate does not determine the nonlinear field away
from its center: the shear is nonzero at a unit displacement despite its zero
Jacobian at the origin. -/
theorem symmetricJacobianAt_does_not_determine_globalField_negativeExample :
    SymmetricJacobianAt quadraticShear 0 ∧
      quadraticShear ![1, 0] ≠ 0 := by
  refine ⟨quadraticShear_symmetricJacobianAt_zero, ?_⟩
  intro hzero
  have h1 := congrFun hzero 1
  norm_num [quadraticShear] at h1

#print axioms euclideanIntegrable_iff_isSymm
#print axioms inverse_metric_recovers_energy
#print axioms linearMonotone_iff_symmetricPart_posSemidef
#print axioms metricGradientFlow_certificate
#print axioms primalDualOperator_monotone
#print axioms monotonicity_does_not_imply_contraction_negativeExample
#print axioms equalFixedPoint_does_not_imply_equalOperatorClass_negativeExample
#print axioms unconstrainedFlow_not_monotone_negativeExample
#print axioms RealCaromLinearization.classify_withoutCertificates_unresolved
#print axioms quadraticShear_symmetricJacobianAt_zero
#print axioms symmetricJacobianAt_does_not_determine_globalField_negativeExample

end

end OperatorClassification

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
