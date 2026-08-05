import Mathlib

/-!
# Conditional-information novelty

Directional novelty and evidential novelty are different tests.  An observation
may lie entirely in a mechanism direction already represented by memory while
still supply independent information about that mechanism.  Conversely, an
exactly predictable manifestation supplies no new information even though it
may carry a nonzero score.

This file gives finite-dimensional covariance semantics to that distinction.
For a current score covariance `Fcc`, stored-score covariance `Fmm`, and cross
covariance `Fcm`, the conditional-information matrix is the Schur complement

`Fcc - Fcm * Fmm⁻¹ * Fcmᴴ`.

When the stored block is positive definite, positive semidefiniteness of the
joint covariance is equivalent to positive semidefiniteness of this
conditional information.  The predictable part is itself positive
semidefinite, giving the matrix interval

`0 ⪯ conditionalInformation ⪯ Fcc`.

The exact-duplicate and zero-cross-covariance endpoints are proved, together
with fixtures separating zero directional residual from zero evidential
novelty.  The inverse-based construction is deliberately scoped to a positive
definite stored covariance.  Singular stored covariances require a
Moore--Penrose inverse or an explicitly supplied least-squares projector and
are not silently identified with this theorem.

The construction formalizes the local Schur-complement novelty rule in the
*Causal Memory and Credit Protocol*.  It does not infer conditional
independence, causal identity, or covariance matrices from data.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace ConditionalInformationNovelty

noncomputable section

open Matrix
open scoped Matrix

variable {Current Memory : Type*}
variable [Fintype Current] [DecidableEq Current]
variable [Fintype Memory] [DecidableEq Memory]

/-- Information remaining in the current score after the best linear
prediction licensed by an invertible stored covariance. -/
def conditionalInformation
    (currentCovariance : Matrix Current Current ℝ)
    (crossCovariance : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ) :
    Matrix Current Current ℝ :=
  currentCovariance -
    crossCovariance * memoryCovariance⁻¹ * crossCovarianceᴴ

/-- Current score after subtracting the linear prediction supplied by stored
score statistics. -/
def conditionalScoreResidual
    (crossCovariance : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (currentScore : Current → ℝ)
    (memoryScore : Memory → ℝ) :
    Current → ℝ :=
  currentScore -
    (crossCovariance * memoryCovariance⁻¹) *ᵥ memoryScore

/-- Orthogonal directional residual against a declared mechanism projector. -/
def directionalResidual
    (projector : Matrix Current Current ℝ)
    (score : Current → ℝ) :
    Current → ℝ :=
  (1 - projector) *ᵥ score

omit [DecidableEq Current] in
/-- A positive-definite stored covariance turns the Schur-complement law into
an exact equivalence: the joint covariance is positive semidefinite exactly
when the residual information is. -/
theorem jointCovariance_posSemidef_iff_conditionalInformation
    (currentCovariance : Matrix Current Current ℝ)
    (crossCovariance : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (hmemory : memoryCovariance.PosDef) :
    (Matrix.fromBlocks
        currentCovariance crossCovariance
        crossCovarianceᴴ memoryCovariance).PosSemidef ↔
      (conditionalInformation
        currentCovariance crossCovariance memoryCovariance).PosSemidef := by
  letI := hmemory.isUnit.invertible
  exact Matrix.PosDef.fromBlocks₂₂
    currentCovariance crossCovariance hmemory

omit [DecidableEq Current] in
/-- The predictable covariance removed by conditioning is positive
semidefinite. Equivalently, conditional information is no larger than the
unconditioned current covariance in Loewner order. -/
theorem currentCovariance_sub_conditionalInformation_posSemidef
    (currentCovariance : Matrix Current Current ℝ)
    (crossCovariance : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (hmemory : memoryCovariance.PosDef) :
    (currentCovariance -
      conditionalInformation
        currentCovariance crossCovariance memoryCovariance).PosSemidef := by
  simpa [conditionalInformation] using
    hmemory.inv.posSemidef.mul_mul_conjTranspose_same crossCovariance

omit [DecidableEq Current] in
/-- The source's partial-redundancy interval:
`0 ⪯ F(current | memory) ⪯ F(current)`. -/
theorem conditionalInformation_between_zero_and_current
    (currentCovariance : Matrix Current Current ℝ)
    (crossCovariance : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (hmemory : memoryCovariance.PosDef)
    (hjoint :
      (Matrix.fromBlocks
        currentCovariance crossCovariance
        crossCovarianceᴴ memoryCovariance).PosSemidef) :
    (conditionalInformation
        currentCovariance crossCovariance memoryCovariance).PosSemidef ∧
      (currentCovariance -
        conditionalInformation
          currentCovariance crossCovariance memoryCovariance).PosSemidef := by
  exact ⟨
    (jointCovariance_posSemidef_iff_conditionalInformation
      currentCovariance crossCovariance memoryCovariance hmemory).mp hjoint,
    currentCovariance_sub_conditionalInformation_posSemidef
      currentCovariance crossCovariance memoryCovariance hmemory⟩

omit [Fintype Current] [DecidableEq Current] in
/-- Zero score cross-covariance means conditioning removes no information. -/
@[simp]
theorem conditionalInformation_zeroCross
    (currentCovariance : Matrix Current Current ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ) :
    conditionalInformation currentCovariance 0 memoryCovariance =
      currentCovariance := by
  simp [conditionalInformation]

omit [Fintype Current] [DecidableEq Current] in
/-- Zero score cross-covariance leaves the current score unchanged. -/
@[simp]
theorem conditionalScoreResidual_zeroCross
    (memoryCovariance : Matrix Memory Memory ℝ)
    (currentScore : Current → ℝ)
    (memoryScore : Memory → ℝ) :
    conditionalScoreResidual 0 memoryCovariance
      currentScore memoryScore = currentScore := by
  simp [conditionalScoreResidual]

omit [Fintype Current] [DecidableEq Current] in
/-- An exact linear manifestation of stored score statistics has zero
conditional score residual. -/
theorem conditionalScoreResidual_duplicate_eq_zero
    (predictor : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (memoryScore : Memory → ℝ)
    (hmemory : memoryCovariance.PosDef) :
    conditionalScoreResidual
        (predictor * memoryCovariance) memoryCovariance
        (predictor *ᵥ memoryScore) memoryScore =
      0 := by
  have hdet : IsUnit memoryCovariance.det :=
    (Matrix.isUnit_iff_isUnit_det memoryCovariance).mp hmemory.isUnit
  ext current
  simp [conditionalScoreResidual, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv memoryCovariance hdet]

omit [Fintype Current] [DecidableEq Current] in
/-- An exact linear manifestation has zero conditional information. -/
theorem conditionalInformation_duplicate_eq_zero
    (predictor : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (hmemory : memoryCovariance.PosDef) :
    conditionalInformation
        (predictor * memoryCovariance * predictorᴴ)
        (predictor * memoryCovariance)
        memoryCovariance =
      0 := by
  have hdet : IsUnit memoryCovariance.det :=
    (Matrix.isUnit_iff_isUnit_det memoryCovariance).mp hmemory.isUnit
  have htranspose : memoryCovarianceᵀ = memoryCovariance :=
    (Matrix.isHermitian_iff_isSymm.mp hmemory.1).eq
  simp [conditionalInformation, Matrix.mul_assoc,
    htranspose, Matrix.mul_nonsing_inv memoryCovariance hdet]

omit [DecidableEq Current] in
/-- Exact duplicate blocks satisfy the joint covariance premise rather than
obtaining zero novelty from an invalid covariance tuple. -/
theorem duplicate_jointCovariance_posSemidef
    (predictor : Matrix Current Memory ℝ)
    (memoryCovariance : Matrix Memory Memory ℝ)
    (hmemory : memoryCovariance.PosDef) :
    (Matrix.fromBlocks
      (predictor * memoryCovariance * predictorᴴ)
      (predictor * memoryCovariance)
      (predictor * memoryCovariance)ᴴ
      memoryCovariance).PosSemidef := by
  rw [jointCovariance_posSemidef_iff_conditionalInformation
    (predictor * memoryCovariance * predictorᴴ)
    (predictor * memoryCovariance) memoryCovariance hmemory]
  rw [conditionalInformation_duplicate_eq_zero
    predictor memoryCovariance hmemory]
  exact Matrix.PosSemidef.zero

/-- Projecting against the entire represented direction space leaves no
directional residual. -/
@[simp]
theorem directionalResidual_full
    (score : Current → ℝ) :
    directionalResidual (1 : Matrix Current Current ℝ) score = 0 := by
  simp [directionalResidual]

/-! ## One-dimensional boundary fixtures -/

/-- An independent repeated observation may occupy no new direction while
retaining its full unit information. -/
theorem independent_sameDirection_fullInformation :
    directionalResidual (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ => (1 : ℝ)) = 0 ∧
      conditionalInformation
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        0
        (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      1 := by
  simp

/-- An exact duplicate occupies the same represented direction but has zero
conditional information. -/
theorem duplicate_sameDirection_zeroInformation :
    directionalResidual (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ => (1 : ℝ)) = 0 ∧
      conditionalInformation
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      0 := by
  constructor
  · simp
  · simpa using conditionalInformation_duplicate_eq_zero
      (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)

/-- Half-correlated unit scores retain three quarters of the original scalar
information. -/
theorem halfCorrelated_retains_threeQuarters :
    conditionalInformation
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      (3 / 4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext current₁ current₂
  fin_cases current₁
  fin_cases current₂
  norm_num [conditionalInformation, Matrix.mul_apply]

/-- Without the positive-definite stored-covariance premise, the totalized
nonsingular inverse can return an algebraic value that is not a valid
conditional-information certificate. -/
theorem singularMemory_totalizedInverse_boundary :
    conditionalInformation
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) =
      1 := by
  simp [conditionalInformation]

#print axioms jointCovariance_posSemidef_iff_conditionalInformation
#print axioms currentCovariance_sub_conditionalInformation_posSemidef
#print axioms conditionalInformation_between_zero_and_current
#print axioms conditionalScoreResidual_duplicate_eq_zero
#print axioms conditionalInformation_duplicate_eq_zero
#print axioms duplicate_jointCovariance_posSemidef
#print axioms independent_sameDirection_fullInformation
#print axioms duplicate_sameDirection_zeroInformation
#print axioms halfCorrelated_retains_threeQuarters
#print axioms singularMemory_totalizedInverse_boundary

end

end ConditionalInformationNovelty

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
