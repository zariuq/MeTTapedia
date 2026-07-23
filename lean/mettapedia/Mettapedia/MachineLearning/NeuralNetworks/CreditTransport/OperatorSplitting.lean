import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorClassification

/-!
# Discrete monotone-operator splitting

This file separates an implicit resolvent update from an explicit forward
step.  A unit resolvent is certified by two matrix identities rather than by
an informal method label.  Monotonicity then gives firm nonexpansiveness, and
the resolvent fixed points are exactly the zeros of the underlying operator.

The two-dimensional fixtures use a genuinely skew monotone operator.  Its
explicit unit forward step expands squared norm, whereas its implicit
resolvent contracts squared norm by one half.  A second nondegenerate fixture
adds a nonzero monotone forward operator and proves the exact
forward--backward fixed-point equation.  Both discrete steps are
nonsymmetric, so neither is an affine Euclidean scalar-potential update.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace OperatorSplitting

open Matrix
open OperatorClassification

noncomputable section

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-! ## Resolvent certificates -/

/-- `J` is the unit-step resolvent of `B` when it is a certified two-sided
inverse of `I + B`.  Both identities are retained so fixed-point reasoning
does not silently assume finite-dimensional invertibility. -/
structure IsUnitResolventOf
    (B J : Matrix Index Index ℝ) : Prop where
  operator_mul_resolvent : (1 + B) * J = 1
  resolvent_mul_operator : J * (1 + B) = 1

/-- Linear firm nonexpansiveness written directly in the Euclidean inner
product.  Applying it to `x - y` gives the usual two-point statement. -/
def LinearFirmlyNonexpansive (J : Matrix Index Index ℝ) : Prop :=
  ∀ displacement : Index → ℝ,
    (J *ᵥ displacement) ⬝ᵥ (J *ᵥ displacement) ≤
      (J *ᵥ displacement) ⬝ᵥ displacement

omit [DecidableEq Index] in
/-- The displacement form is exactly the usual two-point firm
nonexpansiveness inequality for a linear step. -/
theorem LinearFirmlyNonexpansive.twoPoint
    {J : Matrix Index Index ℝ}
    (certificate : LinearFirmlyNonexpansive J)
    (x y : Index → ℝ) :
    (J *ᵥ x - J *ᵥ y) ⬝ᵥ (J *ᵥ x - J *ᵥ y) ≤
      (J *ᵥ x - J *ᵥ y) ⬝ᵥ (x - y) := by
  simpa [Matrix.mulVec_sub] using certificate (x - y)

/-- The defining resolvent equation `(I+B)Jx=x`. -/
theorem IsUnitResolventOf.operator_equation
    {B J : Matrix Index Index ℝ}
    (certificate : IsUnitResolventOf B J) (x : Index → ℝ) :
    J *ᵥ x + B *ᵥ (J *ᵥ x) = x := by
  calc
    J *ᵥ x + B *ᵥ (J *ᵥ x) =
        J *ᵥ x + (B * J) *ᵥ x := by rw [Matrix.mulVec_mulVec]
    _ = (J + B * J) *ᵥ x := by rw [Matrix.add_mulVec]
    _ = ((1 + B) * J) *ᵥ x := by rw [Matrix.add_mul, Matrix.one_mul]
    _ = 1 *ᵥ x := by rw [certificate.operator_mul_resolvent]
    _ = x := Matrix.one_mulVec x

/-- A resolvent preserves exactly the zero set of its underlying operator. -/
theorem IsUnitResolventOf.fixed_iff_operator_zero
    {B J : Matrix Index Index ℝ}
    (certificate : IsUnitResolventOf B J) (x : Index → ℝ) :
    J *ᵥ x = x ↔ B *ᵥ x = 0 := by
  constructor
  · intro hfixed
    have hequation := certificate.operator_equation x
    rw [hfixed] at hequation
    exact add_eq_left.mp hequation
  · intro hzero
    calc
      J *ᵥ x = J *ᵥ ((1 + B) *ᵥ x) := by
        simp [Matrix.add_mulVec, hzero]
      _ = (J * (1 + B)) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ x := by rw [certificate.resolvent_mul_operator]
      _ = x := Matrix.one_mulVec x

/-- The resolvent of a monotone linear operator is firmly nonexpansive. -/
theorem IsUnitResolventOf.firmlyNonexpansive
    {B J : Matrix Index Index ℝ}
    (certificate : IsUnitResolventOf B J)
    (monotone : LinearMonotone B) :
    LinearFirmlyNonexpansive J := by
  intro displacement
  let resolved := J *ᵥ displacement
  have hmonotone : 0 ≤ resolved ⬝ᵥ (B *ᵥ resolved) := monotone resolved
  have hequation : resolved + B *ᵥ resolved = displacement := by
    simpa [resolved] using certificate.operator_equation displacement
  calc
    resolved ⬝ᵥ resolved ≤
        resolved ⬝ᵥ resolved + resolved ⬝ᵥ (B *ᵥ resolved) := by linarith
    _ = resolved ⬝ᵥ displacement := by
      rw [← hequation]
      simp [dotProduct_add]

/-- Proof-carrying discrete certificate for a monotone resolvent method. -/
structure MonotoneResolventCertificate
    (J : Matrix Index Index ℝ) where
  operator : Matrix Index Index ℝ
  monotone : LinearMonotone operator
  resolvent : IsUnitResolventOf operator J

theorem MonotoneResolventCertificate.firmlyNonexpansive
    {J : Matrix Index Index ℝ}
    (certificate : MonotoneResolventCertificate J) :
    LinearFirmlyNonexpansive J :=
  certificate.resolvent.firmlyNonexpansive certificate.monotone

/-! ## Forward--backward splitting -/

/-- Exact forward--backward step: first apply `I-B`, then the resolvent of
`A`. -/
def forwardBackwardStep
    (resolvent forward : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  resolvent * (1 - forward)

/-- A proof-carrying forward--backward split with nonnegative operator
quadratic forms on both sides. -/
structure MonotoneForwardBackwardCertificate
    (step : Matrix Index Index ℝ) where
  implicitOperator : Matrix Index Index ℝ
  forwardOperator : Matrix Index Index ℝ
  resolvent : Matrix Index Index ℝ
  implicitMonotone : LinearMonotone implicitOperator
  forwardMonotone : LinearMonotone forwardOperator
  resolventCertificate : IsUnitResolventOf implicitOperator resolvent
  step_eq : step = forwardBackwardStep resolvent forwardOperator

/-- Fixed points of a certified forward--backward step are exactly zeros of
the sum of its implicit and forward operators. -/
theorem MonotoneForwardBackwardCertificate.fixed_iff_sum_zero
    {step : Matrix Index Index ℝ}
    (certificate : MonotoneForwardBackwardCertificate step)
    (x : Index → ℝ) :
    step *ᵥ x = x ↔
      (certificate.implicitOperator + certificate.forwardOperator) *ᵥ x = 0 := by
  constructor
  · intro hfixed
    have hstep := congrArg (fun matrix : Matrix Index Index ℝ => matrix *ᵥ x)
      certificate.step_eq
    have hfixed' :
        forwardBackwardStep certificate.resolvent certificate.forwardOperator *ᵥ x = x :=
      hstep.symm.trans hfixed
    have hresolved :
        certificate.resolvent *ᵥ
            ((1 - certificate.forwardOperator) *ᵥ x) = x := by
      simpa [forwardBackwardStep, Matrix.mulVec_mulVec] using hfixed'
    have hequation := certificate.resolventCertificate.operator_equation
      ((1 - certificate.forwardOperator) *ᵥ x)
    rw [hresolved] at hequation
    rw [Matrix.add_mulVec]
    funext coordinate
    have hcoordinate := congrFun hequation coordinate
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.add_apply, Pi.zero_apply] at hcoordinate ⊢
    linarith
  · intro hzero
    have hsum :
        certificate.implicitOperator *ᵥ x +
            certificate.forwardOperator *ᵥ x = 0 := by
      simpa [Matrix.add_mulVec] using hzero
    have hbalance :
        (1 - certificate.forwardOperator) *ᵥ x =
          (1 + certificate.implicitOperator) *ᵥ x := by
      funext coordinate
      have hcoordinate := congrFun hsum coordinate
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at hcoordinate ⊢
      linarith
    calc
      step *ᵥ x =
          forwardBackwardStep certificate.resolvent certificate.forwardOperator *ᵥ x :=
            congrArg (fun matrix : Matrix Index Index ℝ => matrix *ᵥ x)
              certificate.step_eq
      _ =
          certificate.resolvent *ᵥ
            ((1 - certificate.forwardOperator) *ᵥ x) := by
              rw [forwardBackwardStep, Matrix.mulVec_mulVec]
      _ = certificate.resolvent *ᵥ
            ((1 + certificate.implicitOperator) *ᵥ x) := by rw [hbalance]
      _ = x := by
        rw [Matrix.mulVec_mulVec,
          certificate.resolventCertificate.resolvent_mul_operator,
          Matrix.one_mulVec]

/-! ## Exact skew and split fixtures -/

/-- Unit resolvent of the monotone skew operator `rotationOperator`. -/
def rotationResolvent : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, -1 / 2; 1 / 2, 1 / 2]

/-- Explicit unit forward step `I - rotationOperator`. -/
def rotationForwardStep : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -1; 1, 1]

theorem rotationResolvent_isUnitResolvent :
    IsUnitResolventOf rotationOperator rotationResolvent := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotationOperator, rotationResolvent, Matrix.mul_apply,
      Fin.sum_univ_two]

def rotationResolvent_monotoneCertificate :
    MonotoneResolventCertificate rotationResolvent :=
  ⟨rotationOperator, rotationOperator_monotone,
    rotationResolvent_isUnitResolvent⟩

theorem rotationResolvent_firmlyNonexpansive :
    LinearFirmlyNonexpansive rotationResolvent :=
  rotationResolvent_monotoneCertificate.firmlyNonexpansive

theorem rotationOperator_mulVec_eq_zero_iff (x : Fin 2 → ℝ) :
    rotationOperator *ᵥ x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    funext coordinate
    fin_cases coordinate
    · have h := congrFun hzero 1
      norm_num [rotationOperator, Matrix.mulVec, Fin.sum_univ_two] at h
      simpa [Matrix.vecHead] using h
    · have h := congrFun hzero 0
      norm_num [rotationOperator, Matrix.mulVec, Fin.sum_univ_two] at h
      simpa [Matrix.vecHead, Matrix.vecTail] using h
  · rintro rfl
    simp

theorem rotationResolvent_fixed_iff_zero (x : Fin 2 → ℝ) :
    rotationResolvent *ᵥ x = x ↔ x = 0 := by
  rw [rotationResolvent_isUnitResolvent.fixed_iff_operator_zero,
    rotationOperator_mulVec_eq_zero_iff]

theorem rotationForwardStep_eq_one_sub_operator :
    rotationForwardStep = 1 - rotationOperator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationForwardStep, rotationOperator]

/-- The implicit skew resolvent contracts squared norm by exactly one half. -/
theorem rotationResolvent_squaredNorm (x : Fin 2 → ℝ) :
    (rotationResolvent *ᵥ x) ⬝ᵥ (rotationResolvent *ᵥ x) =
      (1 / 2 : ℝ) * (x ⬝ᵥ x) := by
  simp [rotationResolvent, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The corresponding explicit unit forward step expands squared norm by
exactly two. -/
theorem rotationForwardStep_squaredNorm (x : Fin 2 → ℝ) :
    (rotationForwardStep *ᵥ x) ⬝ᵥ (rotationForwardStep *ᵥ x) =
      2 * (x ⬝ᵥ x) := by
  simp [rotationForwardStep, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- A monotone skew operator can therefore have an expanding explicit step
and a contracting implicit resolvent at the same unit step size. -/
theorem implicit_resolvent_contracts_while_explicit_step_expands :
    let x : Fin 2 → ℝ := ![3, 4]
    (rotationResolvent *ᵥ x) ⬝ᵥ (rotationResolvent *ᵥ x) = 25 / 2 ∧
      (rotationForwardStep *ᵥ x) ⬝ᵥ (rotationForwardStep *ᵥ x) = 50 := by
  norm_num [rotationResolvent, rotationForwardStep, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]

/-- A nonzero monotone forward operator used in the genuine two-operator
split fixture. -/
def coordinatePenaltyOperator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- Exact forward--backward step for the skew implicit operator and the
coordinate penalty. -/
def rotationPenaltySplitStep : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1 / 2; 0, 1 / 2]

theorem coordinatePenaltyOperator_monotone :
    LinearMonotone coordinatePenaltyOperator := by
  intro x
  simp [coordinatePenaltyOperator, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  simpa [pow_two] using sq_nonneg (x 0)

theorem rotationPenaltySplitStep_eq_forwardBackward :
    rotationPenaltySplitStep =
      forwardBackwardStep rotationResolvent coordinatePenaltyOperator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationPenaltySplitStep, forwardBackwardStep,
      rotationResolvent, coordinatePenaltyOperator, Matrix.mul_apply,
      Fin.sum_univ_two]

def rotationPenaltySplit_certificate :
    MonotoneForwardBackwardCertificate rotationPenaltySplitStep :=
  { implicitOperator := rotationOperator
    forwardOperator := coordinatePenaltyOperator
    resolvent := rotationResolvent
    implicitMonotone := rotationOperator_monotone
    forwardMonotone := coordinatePenaltyOperator_monotone
    resolventCertificate := rotationResolvent_isUnitResolvent
    step_eq := rotationPenaltySplitStep_eq_forwardBackward }

theorem rotationPenaltySplit_fixed_iff_sum_zero (x : Fin 2 → ℝ) :
    rotationPenaltySplitStep *ᵥ x = x ↔
      (rotationOperator + coordinatePenaltyOperator) *ᵥ x = 0 :=
  by
    simpa [rotationPenaltySplit_certificate] using
      rotationPenaltySplit_certificate.fixed_iff_sum_zero x

/-- The nondegenerate split contracts squared norm by at least one half per
step. -/
theorem rotationPenaltySplit_squaredNorm_le (x : Fin 2 → ℝ) :
    (rotationPenaltySplitStep *ᵥ x) ⬝ᵥ
        (rotationPenaltySplitStep *ᵥ x) ≤
      (1 / 2 : ℝ) * (x ⬝ᵥ x) := by
  simp [rotationPenaltySplitStep, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0)]

/-! ## Scalar-potential separation -/

/-- A linear discrete step belongs to the affine Euclidean-potential class
when its displacement field has zero circulation. -/
def IsAffineEuclideanPotentialStep
    (step : Matrix Index Index ℝ) : Prop :=
  EuclideanIntegrable (step - 1) 0

theorem rotationResolvent_not_affineEuclideanPotentialStep :
    ¬ IsAffineEuclideanPotentialStep rotationResolvent := by
  rw [IsAffineEuclideanPotentialStep,
    euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [rotationResolvent] at h01

theorem rotationPenaltySplit_not_affineEuclideanPotentialStep :
    ¬ IsAffineEuclideanPotentialStep rotationPenaltySplitStep := by
  rw [IsAffineEuclideanPotentialStep,
    euclideanIntegrable_iff_isSymm]
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [rotationPenaltySplitStep] at h01

/-- This is the requested category separation: a nondegenerate
forward--backward step can have a monotone certificate and a strict contraction
bound while failing the affine Euclidean scalar-potential criterion. -/
theorem monotone_splitting_not_scalarPotential_crown :
    Nonempty (MonotoneForwardBackwardCertificate rotationPenaltySplitStep) ∧
      (∀ x : Fin 2 → ℝ,
        (rotationPenaltySplitStep *ᵥ x) ⬝ᵥ
            (rotationPenaltySplitStep *ᵥ x) ≤
          (1 / 2 : ℝ) * (x ⬝ᵥ x)) ∧
      ¬ IsAffineEuclideanPotentialStep rotationPenaltySplitStep :=
  ⟨⟨rotationPenaltySplit_certificate⟩,
    rotationPenaltySplit_squaredNorm_le,
    rotationPenaltySplit_not_affineEuclideanPotentialStep⟩

#print axioms IsUnitResolventOf.fixed_iff_operator_zero
#print axioms IsUnitResolventOf.firmlyNonexpansive
#print axioms MonotoneForwardBackwardCertificate.fixed_iff_sum_zero
#print axioms rotationResolvent_isUnitResolvent
#print axioms implicit_resolvent_contracts_while_explicit_step_expands
#print axioms rotationPenaltySplit_fixed_iff_sum_zero
#print axioms monotone_splitting_not_scalarPotential_crown

end

end OperatorSplitting

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
