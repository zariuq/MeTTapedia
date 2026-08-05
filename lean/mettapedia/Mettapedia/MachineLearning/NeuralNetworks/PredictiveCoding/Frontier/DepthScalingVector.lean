import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DepthScalingImplementation
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.MatrixGaussianChain
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalPreconditionedRate
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

/-!
# Vector and nonlinear depth-scaling repairs

This file removes the scalar ceiling from the exact depth-repair mechanisms.
Layer states are finite real vectors; link Jacobians are genuine rectangular
matrices; and covariance matrices are arbitrary positive-definite matrices,
not merely diagonal weights.  Exact finite-increment identities are stated in
full covariance coordinates.  For nonlinear prediction maps, the exact
increment retains the nonlinear Taylor remainder, while a Fréchet-derivative
theorem proves that this remainder has zero derivative at the base point.

The residual timing theorem remains independent of numerical contents and is
therefore instantiated for vector states and arbitrary nonlinear update maps.
No nonlinear optimization-accuracy claim is inferred from these identities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Matrix
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open scoped BigOperators

/-! ## Full-covariance vector energies -/

/-- Precision-weighted energy of one vector residual. -/
noncomputable def vectorPrecisionEnergy {Index : Type*} [Fintype Index]
    (precision : Matrix Index Index ℝ) (error : Index → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (error ⬝ᵥ precision.mulVec error)

/-- Covariance-coordinate energy.  A positive-definite covariance is
invertible, so its nonsingular inverse is the full precision matrix. -/
noncomputable def vectorCovarianceEnergy {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (covariance : Matrix Index Index ℝ) (error : Index → ℝ) : ℝ :=
  vectorPrecisionEnergy covariance⁻¹ error

/-- Symmetric real precision permits swapping the two residual arguments. -/
theorem vectorPrecision_dot_swap {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (precision : Matrix Index Index ℝ) (hprecision : precision.IsHermitian)
    (a b : Index → ℝ) :
    a ⬝ᵥ precision.mulVec b = b ⬝ᵥ precision.mulVec a := by
  have htranspose : precision.transpose = precision := by
    ext i j
    have h := hprecision.apply i j
    simpa using h
  calc
    a ⬝ᵥ precision.mulVec b =
        a ⬝ᵥ precision.transpose.mulVec b := by rw [htranspose]
    _ = b ⬝ᵥ precision.mulVec a :=
      Matrix.dotProduct_transpose_mulVec precision a b

/-- Exact finite increment of a full-matrix quadratic energy. -/
theorem vectorPrecisionEnergy_add_exact {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (precision : Matrix Index Index ℝ) (hprecision : precision.IsHermitian)
    (error perturbation : Index → ℝ) :
    vectorPrecisionEnergy precision (error + perturbation) -
        vectorPrecisionEnergy precision error =
      perturbation ⬝ᵥ precision.mulVec error +
        (1 / 2 : ℝ) *
          (perturbation ⬝ᵥ precision.mulVec perturbation) := by
  unfold vectorPrecisionEnergy
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [vectorPrecision_dot_swap precision hprecision error perturbation]
  ring

/-- Two adjacent full-covariance energies before perturbing their shared
hidden vector. -/
noncomputable def vectorHiddenPairEnergy
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ) : ℝ :=
  vectorCovarianceEnergy incomingCovariance incomingError +
    vectorCovarianceEnergy outgoingCovariance outgoingError

/-- Perturb the incoming residual by `delta` and the outgoing residual by
minus an arbitrary transported displacement. -/
noncomputable def vectorHiddenPairEnergyAfterDisplacements
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
    (delta : Hidden → ℝ) (transported : Outgoing → ℝ) : ℝ :=
  vectorCovarianceEnergy incomingCovariance (incomingError + delta) +
    vectorCovarianceEnergy outgoingCovariance
      (outgoingError - transported)

/-- Exact full-covariance finite increment.  This theorem is valid for an
arbitrary transported displacement and is the algebraic core shared by
linear Jacobians and nonlinear maps with a remainder. -/
theorem vectorHiddenPairEnergy_displacements_exact
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (hincoming : incomingCovariance.PosDef)
    (houtgoing : outgoingCovariance.PosDef)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
    (delta : Hidden → ℝ) (transported : Outgoing → ℝ) :
    vectorHiddenPairEnergyAfterDisplacements incomingCovariance
        outgoingCovariance incomingError outgoingError delta transported -
      vectorHiddenPairEnergy incomingCovariance outgoingCovariance
        incomingError outgoingError =
      delta ⬝ᵥ incomingCovariance⁻¹.mulVec incomingError -
        transported ⬝ᵥ outgoingCovariance⁻¹.mulVec outgoingError +
        (1 / 2 : ℝ) *
          (delta ⬝ᵥ incomingCovariance⁻¹.mulVec delta +
            transported ⬝ᵥ outgoingCovariance⁻¹.mulVec transported) := by
  have hinverse : incomingCovariance⁻¹.IsHermitian :=
    hincoming.inv.isHermitian
  have houtverse : outgoingCovariance⁻¹.IsHermitian :=
    houtgoing.inv.isHermitian
  have hi := vectorPrecisionEnergy_add_exact incomingCovariance⁻¹
    hinverse incomingError delta
  have ho := vectorPrecisionEnergy_add_exact outgoingCovariance⁻¹
    houtverse outgoingError (-transported)
  have ho' :
      vectorPrecisionEnergy outgoingCovariance⁻¹
          (outgoingError - transported) -
        vectorPrecisionEnergy outgoingCovariance⁻¹ outgoingError =
      -(transported ⬝ᵥ outgoingCovariance⁻¹.mulVec outgoingError) +
        (1 / 2 : ℝ) *
          (transported ⬝ᵥ outgoingCovariance⁻¹.mulVec transported) := by
    simpa [sub_eq_add_neg, Matrix.mulVec_neg, neg_dotProduct,
      dotProduct_neg] using ho
  unfold vectorHiddenPairEnergyAfterDisplacements vectorHiddenPairEnergy
  unfold vectorCovarianceEnergy
  calc
    vectorPrecisionEnergy incomingCovariance⁻¹ (incomingError + delta) +
          vectorPrecisionEnergy outgoingCovariance⁻¹
            (outgoingError - transported) -
        (vectorPrecisionEnergy incomingCovariance⁻¹ incomingError +
          vectorPrecisionEnergy outgoingCovariance⁻¹ outgoingError) =
      (vectorPrecisionEnergy incomingCovariance⁻¹ (incomingError + delta) -
          vectorPrecisionEnergy incomingCovariance⁻¹ incomingError) +
        (vectorPrecisionEnergy outgoingCovariance⁻¹
            (outgoingError - transported) -
          vectorPrecisionEnergy outgoingCovariance⁻¹ outgoingError) := by ring
    _ = _ := by rw [hi, ho']; ring

/-! ## Linear Jacobian and sign/index audit -/

/-- Full-covariance hidden-state gradient at a layer.  The outgoing force is
pulled back by the transpose of the rectangular prediction Jacobian. -/
noncomputable def vectorActivityGradient
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ) : Hidden → ℝ :=
  incomingCovariance⁻¹.mulVec incomingError -
    jacobian.transpose.mulVec
      (outgoingCovariance⁻¹.mulVec outgoingError)

/-- The linear coefficient in the exact vector increment is precisely the
dot product against the full-covariance activity gradient. -/
theorem vectorActivityGradient_directional_identity
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
    (delta : Hidden → ℝ) :
    delta ⬝ᵥ vectorActivityGradient incomingCovariance outgoingCovariance
        jacobian incomingError outgoingError =
      delta ⬝ᵥ incomingCovariance⁻¹.mulVec incomingError -
        jacobian.mulVec delta ⬝ᵥ
          outgoingCovariance⁻¹.mulVec outgoingError := by
  unfold vectorActivityGradient
  rw [dotProduct_sub]
  congr 1
  have htransport :
      jacobian.mulVec delta ⬝ᵥ
          outgoingCovariance⁻¹.mulVec outgoingError =
        delta ⬝ᵥ jacobian.transpose.mulVec
          (outgoingCovariance⁻¹.mulVec outgoingError) := by
    symm
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact htransport.symm

/-- Exact finite increment for a vector layer linearized by a genuine
rectangular Jacobian. -/
theorem vectorHiddenPairEnergy_jacobianIncrement_exact
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (hincoming : incomingCovariance.PosDef)
    (houtgoing : outgoingCovariance.PosDef)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
    (delta : Hidden → ℝ) :
    vectorHiddenPairEnergyAfterDisplacements incomingCovariance
        outgoingCovariance incomingError outgoingError delta
        (jacobian.mulVec delta) -
      vectorHiddenPairEnergy incomingCovariance outgoingCovariance
        incomingError outgoingError =
      delta ⬝ᵥ vectorActivityGradient incomingCovariance outgoingCovariance
          jacobian incomingError outgoingError +
        (1 / 2 : ℝ) *
          (delta ⬝ᵥ incomingCovariance⁻¹.mulVec delta +
            jacobian.mulVec delta ⬝ᵥ
              outgoingCovariance⁻¹.mulVec (jacobian.mulVec delta)) := by
  rw [vectorHiddenPairEnergy_displacements_exact incomingCovariance
    outgoingCovariance hincoming houtgoing incomingError outgoingError
    delta (jacobian.mulVec delta)]
  rw [vectorActivityGradient_directional_identity]

/-- Mechanically derived negative-gradient activity step. -/
noncomputable def vectorNegativeGradientActivityStep
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (rate : ℝ)
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ) : Hidden → ℝ :=
  -rate • vectorActivityGradient incomingCovariance outgoingCovariance
    jacobian incomingError outgoingError

/-- Covariance-corrected displayed vector force. -/
noncomputable def vectorCorrectedDisplayedActivityStep
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (rate : ℝ)
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ) : Hidden → ℝ :=
  rate • vectorActivityGradient incomingCovariance outgoingCovariance
    jacobian incomingError outgoingError

theorem vectorNegativeGradientActivityStep_eq_neg_correctedDisplayed
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (rate : ℝ)
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ) :
    vectorNegativeGradientActivityStep rate incomingCovariance
        outgoingCovariance jacobian incomingError outgoingError =
      -vectorCorrectedDisplayedActivityStep rate incomingCovariance
        outgoingCovariance jacobian incomingError outgoingError := by
  simp [vectorNegativeGradientActivityStep,
    vectorCorrectedDisplayedActivityStep]

/-- Precision-coordinate reading of the paper's displayed activity force for
equal-width adjacent layers.  It applies the incoming-link precision to both
the incoming and outgoing residuals, reproducing the paper's index choice. -/
noncomputable def vectorPaperDisplayedActivityForce
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (incomingPrecision _outgoingPrecision : Matrix Index Index ℝ)
    (jacobian : Matrix Index Index ℝ)
    (incomingError outgoingError : Index → ℝ) : Index → ℝ :=
  incomingPrecision.mulVec incomingError -
    jacobian.transpose.mulVec (incomingPrecision.mulVec outgoingError)

/-- The covariance-corrected force uses the outgoing-link precision on the
outgoing residual. -/
noncomputable def vectorCorrectedActivityForce
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (incomingPrecision outgoingPrecision : Matrix Index Index ℝ)
    (jacobian : Matrix Index Index ℝ)
    (incomingError outgoingError : Index → ℝ) : Index → ℝ :=
  incomingPrecision.mulVec incomingError -
    jacobian.transpose.mulVec (outgoingPrecision.mulVec outgoingError)

/-- The displayed and corrected vector forces coincide when adjacent link
precisions coincide. -/
theorem vectorPaperDisplayedActivityForce_eq_corrected_of_precision_eq
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (incomingPrecision outgoingPrecision : Matrix Index Index ℝ)
    (jacobian : Matrix Index Index ℝ)
    (incomingError outgoingError : Index → ℝ)
    (hprecision : incomingPrecision = outgoingPrecision) :
    vectorPaperDisplayedActivityForce incomingPrecision outgoingPrecision
        jacobian incomingError outgoingError =
      vectorCorrectedActivityForce incomingPrecision outgoingPrecision
        jacobian incomingError outgoingError := by
  subst outgoingPrecision
  rfl

/-- The corrected precision force is exactly the full-covariance gradient
when the precisions are the inverses of the two link covariances. -/
theorem vectorCorrectedActivityForce_eq_covarianceGradient
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (incomingCovariance outgoingCovariance : Matrix Index Index ℝ)
    (jacobian : Matrix Index Index ℝ)
    (incomingError outgoingError : Index → ℝ) :
    vectorCorrectedActivityForce incomingCovariance⁻¹ outgoingCovariance⁻¹
        jacobian incomingError outgoingError =
      vectorActivityGradient incomingCovariance outgoingCovariance jacobian
        incomingError outgoingError := by
  rfl

/-- Two-dimensional negative fixture for the covariance-index audit.  The
paper-displayed force uses unit incoming precision on the first coordinate;
the corrected force uses outgoing precision two. -/
theorem vectorDisplayedActivity_precisionIndexMismatch :
    let incomingPrecision : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
    let outgoingPrecision : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]
    let jacobian : Matrix (Fin 2) (Fin 2) ℝ := 1
    let incomingError : Fin 2 → ℝ := ![0, 0]
    let outgoingError : Fin 2 → ℝ := ![1, 0]
    vectorPaperDisplayedActivityForce incomingPrecision outgoingPrecision
        jacobian incomingError outgoingError 0 = -1 ∧
      vectorCorrectedActivityForce incomingPrecision outgoingPrecision
        jacobian incomingError outgoingError 0 = -2 := by
  norm_num [vectorPaperDisplayedActivityForce,
    vectorCorrectedActivityForce, Matrix.mulVec, dotProduct]

/-! ## Matrix-weight finite increments -/

/-- Frobenius pairing of two weight matrices. -/
noncomputable def matrixFrobeniusPairing
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    (first second : Matrix Row Column ℝ) : ℝ :=
  ∑ i, ∑ j, first i j * second i j

/-- Full-covariance gradient of one link energy with respect to its matrix
weight. -/
noncomputable def vectorWeightGradient
    {Source Target : Type*}
    [Fintype Source] [Fintype Target] [DecidableEq Target]
    (covariance : Matrix Target Target ℝ)
    (predictionError : Target → ℝ) (sourceActivity : Source → ℝ) :
    Matrix Target Source ℝ :=
  fun i j => -(covariance⁻¹.mulVec predictionError i * sourceActivity j)

theorem matrixFrobeniusPairing_vectorWeightGradient
    {Source Target : Type*}
    [Fintype Source] [Fintype Target] [DecidableEq Target]
    (covariance : Matrix Target Target ℝ)
    (predictionError : Target → ℝ) (sourceActivity : Source → ℝ)
    (weightPerturbation : Matrix Target Source ℝ) :
    matrixFrobeniusPairing weightPerturbation
        (vectorWeightGradient covariance predictionError sourceActivity) =
      -(weightPerturbation.mulVec sourceActivity ⬝ᵥ
        covariance⁻¹.mulVec predictionError) := by
  let force := covariance⁻¹.mulVec predictionError
  change (∑ i, ∑ j, weightPerturbation i j *
      -(force i * sourceActivity j)) =
    -(weightPerturbation.mulVec sourceActivity ⬝ᵥ force)
  simp only [dotProduct, Matrix.mulVec]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact finite increment under an arbitrary matrix-weight perturbation. -/
theorem vectorWeightEnergy_increment_exact
    {Source Target : Type*}
    [Fintype Source] [Fintype Target] [DecidableEq Target]
    (covariance : Matrix Target Target ℝ) (hcovariance : covariance.PosDef)
    (predictionError : Target → ℝ) (sourceActivity : Source → ℝ)
    (weightPerturbation : Matrix Target Source ℝ) :
    vectorCovarianceEnergy covariance
        (predictionError - weightPerturbation.mulVec sourceActivity) -
      vectorCovarianceEnergy covariance predictionError =
      matrixFrobeniusPairing weightPerturbation
          (vectorWeightGradient covariance predictionError sourceActivity) +
        (1 / 2 : ℝ) *
          (weightPerturbation.mulVec sourceActivity ⬝ᵥ
            covariance⁻¹.mulVec
              (weightPerturbation.mulVec sourceActivity)) := by
  have henergy := vectorPrecisionEnergy_add_exact covariance⁻¹
    hcovariance.inv.isHermitian predictionError
      (-(weightPerturbation.mulVec sourceActivity))
  simp only [sub_eq_add_neg] at henergy ⊢
  simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg] at henergy
  unfold vectorCovarianceEnergy
  rw [matrixFrobeniusPairing_vectorWeightGradient]
  exact henergy

/-- The paper-displayed matrix weight step has the gradient sign; the
mechanical negative-gradient step is its additive inverse. -/
theorem vectorPaperDisplayedWeightStep_eq_neg_negativeGradient
    {Source Target : Type*}
    [Fintype Source] [Fintype Target] [DecidableEq Target]
    (rate : ℝ) (covariance : Matrix Target Target ℝ)
    (predictionError : Target → ℝ) (sourceActivity : Source → ℝ) :
    rate • vectorWeightGradient covariance predictionError sourceActivity =
      -(-rate • vectorWeightGradient covariance predictionError sourceActivity) := by
  simp

/-! ## Nonlinear prediction maps with genuine Jacobians -/

/-- Continuous linear map represented by a finite real matrix. -/
noncomputable def matrixContinuousLinearMap
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (jacobian : Matrix Target Source ℝ) :
    (Source → ℝ) →L[ℝ] (Target → ℝ) :=
  (Matrix.toLin' jacobian).toContinuousLinearMap

/-- Exact nonlinear Taylor remainder around `point`. -/
noncomputable def nonlinearJacobianRemainder
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (prediction : (Source → ℝ) → (Target → ℝ))
    (jacobian : Matrix Target Source ℝ)
    (point perturbation : Source → ℝ) : Target → ℝ :=
  prediction (point + perturbation) - prediction point -
    jacobian.mulVec perturbation

/-- If the matrix is the actual Fréchet derivative of the nonlinear
prediction map, then its exact remainder has zero derivative at zero. -/
theorem nonlinearJacobianRemainder_hasFDerivAt_zero
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (prediction : (Source → ℝ) → (Target → ℝ))
    (jacobian : Matrix Target Source ℝ) (point : Source → ℝ)
    (hjacobian : HasFDerivAt prediction
      (matrixContinuousLinearMap jacobian) point) :
    HasFDerivAt
      (nonlinearJacobianRemainder prediction jacobian point)
      (0 : (Source → ℝ) →L[ℝ] (Target → ℝ)) 0 := by
  let J := matrixContinuousLinearMap jacobian
  have hshift : HasFDerivAt (fun delta : Source → ℝ => point + delta)
      (ContinuousLinearMap.id ℝ (Source → ℝ)) 0 := by
    simpa using
      (hasFDerivAt_const (𝕜 := ℝ) point (0 : Source → ℝ)).add
        (hasFDerivAt_id (𝕜 := ℝ) (0 : Source → ℝ))
  have hcomposed : HasFDerivAt (fun delta : Source → ℝ =>
      prediction (point + delta)) J 0 := by
    have hjacobian' : HasFDerivAt prediction
        (matrixContinuousLinearMap jacobian) (point + 0) := by
      simpa using hjacobian
    simpa [J] using hjacobian'.comp 0 hshift
  have hlinear : HasFDerivAt (fun delta : Source → ℝ =>
      jacobian.mulVec delta) J 0 := by
    simpa [J, matrixContinuousLinearMap, Matrix.toLin'_apply'] using
      J.hasFDerivAt
  simpa [nonlinearJacobianRemainder, J] using
    (hcomposed.sub_const (prediction point)).sub hlinear

/-- Energy of a hidden vector feeding a genuinely nonlinear prediction. -/
noncomputable def nonlinearVectorHiddenPairEnergy
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (incomingError : Hidden → ℝ) (outgoingTarget : Outgoing → ℝ)
    (prediction : (Hidden → ℝ) → (Outgoing → ℝ))
    (hiddenActivity : Hidden → ℝ) : ℝ :=
  vectorCovarianceEnergy incomingCovariance incomingError +
    vectorCovarianceEnergy outgoingCovariance
      (outgoingTarget - prediction hiddenActivity)

/-- Exact nonlinear finite increment.  The transported outgoing displacement
is the Jacobian action plus the exact nonlinear remainder. -/
theorem nonlinearVectorHiddenPairEnergy_increment_exact
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingCovariance : Matrix Hidden Hidden ℝ)
    (outgoingCovariance : Matrix Outgoing Outgoing ℝ)
    (hincoming : incomingCovariance.PosDef)
    (houtgoing : outgoingCovariance.PosDef)
    (incomingError : Hidden → ℝ) (outgoingTarget : Outgoing → ℝ)
    (prediction : (Hidden → ℝ) → (Outgoing → ℝ))
    (jacobian : Matrix Outgoing Hidden ℝ)
    (hiddenActivity delta : Hidden → ℝ) :
    nonlinearVectorHiddenPairEnergy incomingCovariance outgoingCovariance
        (incomingError + delta) outgoingTarget prediction
        (hiddenActivity + delta) -
      nonlinearVectorHiddenPairEnergy incomingCovariance outgoingCovariance
        incomingError outgoingTarget prediction hiddenActivity =
      delta ⬝ᵥ incomingCovariance⁻¹.mulVec incomingError -
        (jacobian.mulVec delta + nonlinearJacobianRemainder prediction
          jacobian hiddenActivity delta) ⬝ᵥ
            outgoingCovariance⁻¹.mulVec
              (outgoingTarget - prediction hiddenActivity) +
        (1 / 2 : ℝ) *
          (delta ⬝ᵥ incomingCovariance⁻¹.mulVec delta +
            (jacobian.mulVec delta + nonlinearJacobianRemainder prediction
              jacobian hiddenActivity delta) ⬝ᵥ
              outgoingCovariance⁻¹.mulVec
                (jacobian.mulVec delta + nonlinearJacobianRemainder prediction
                  jacobian hiddenActivity delta)) := by
  let transported := jacobian.mulVec delta +
    nonlinearJacobianRemainder prediction jacobian hiddenActivity delta
  have houtgoingError :
      outgoingTarget - prediction (hiddenActivity + delta) =
        (outgoingTarget - prediction hiddenActivity) - transported := by
    funext coordinate
    simp [transported, nonlinearJacobianRemainder]
  rw [nonlinearVectorHiddenPairEnergy, nonlinearVectorHiddenPairEnergy,
    houtgoingError]
  exact vectorHiddenPairEnergy_displacements_exact incomingCovariance
    outgoingCovariance hincoming houtgoing incomingError
      (outgoingTarget - prediction hiddenActivity) delta transported

/-! ### Concrete nonlinear Jacobian fixture -/

/-- A genuinely nonlinear two-coordinate prediction map. -/
noncomputable def coordinateSquarePrediction
    (activity : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun coordinate => activity coordinate ^ 2

/-- The zero matrix is the actual Fréchet derivative of the componentwise
square map at the origin. -/
theorem coordinateSquarePrediction_hasFDerivAt_zero :
    HasFDerivAt coordinateSquarePrediction
      (matrixContinuousLinearMap (0 : Matrix (Fin 2) (Fin 2) ℝ)) 0 := by
  have hsquare : HasFDerivAt coordinateSquarePrediction
      (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) 0 := by
    rw [hasFDerivAt_pi']
    intro coordinate
    simpa [coordinateSquarePrediction] using
      ((hasFDerivAt_apply (𝕜 := ℝ) coordinate (0 : Fin 2 → ℝ)).pow 2)
  simpa [matrixContinuousLinearMap, Matrix.toLin'_apply'] using hsquare

/-- The nonlinear remainder is the exact componentwise square, rather than
being silently discarded by a linearized model. -/
theorem coordinateSquarePrediction_remainder_exact (delta : Fin 2 → ℝ) :
    nonlinearJacobianRemainder coordinateSquarePrediction
        (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 delta =
      fun coordinate => delta coordinate ^ 2 := by
  funext coordinate
  simp [nonlinearJacobianRemainder, coordinateSquarePrediction]

/-- Negative fixture for a purely linear treatment: the nonlinear remainder
is nonzero at a unit perturbation. -/
theorem coordinateSquarePrediction_remainder_nonzero :
    nonlinearJacobianRemainder coordinateSquarePrediction
        (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 ![1, 0] ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (0 : Fin 2)
  norm_num [nonlinearJacobianRemainder, coordinateSquarePrediction,
    Matrix.mulVec, dotProduct] at hcoordinate

/-! ## Diagonal and genuinely coupled covariance instances -/

/-- A diagonal covariance is one valid instance of the full theorem. -/
theorem diagonalCovariance_jacobianIncrement_exact
    {Hidden Outgoing : Type*}
    [Fintype Hidden] [DecidableEq Hidden]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incomingVariance : Hidden → ℝ) (outgoingVariance : Outgoing → ℝ)
    (hincoming : (Matrix.diagonal incomingVariance).PosDef)
    (houtgoing : (Matrix.diagonal outgoingVariance).PosDef)
    (jacobian : Matrix Outgoing Hidden ℝ)
    (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
    (delta : Hidden → ℝ) :
    vectorHiddenPairEnergyAfterDisplacements
        (Matrix.diagonal incomingVariance) (Matrix.diagonal outgoingVariance)
        incomingError outgoingError delta (jacobian.mulVec delta) -
      vectorHiddenPairEnergy (Matrix.diagonal incomingVariance)
        (Matrix.diagonal outgoingVariance) incomingError outgoingError =
      delta ⬝ᵥ vectorActivityGradient (Matrix.diagonal incomingVariance)
          (Matrix.diagonal outgoingVariance) jacobian incomingError
          outgoingError +
        (1 / 2 : ℝ) *
          (delta ⬝ᵥ (Matrix.diagonal incomingVariance)⁻¹.mulVec delta +
            jacobian.mulVec delta ⬝ᵥ
              (Matrix.diagonal outgoingVariance)⁻¹.mulVec
                (jacobian.mulVec delta)) :=
  vectorHiddenPairEnergy_jacobianIncrement_exact _ _ hincoming houtgoing
    jacobian incomingError outgoingError delta

/-- A genuinely coupled covariance fixture inherited from the matrix-rate
theory; its off-diagonal entries are nonzero. -/
theorem coupledCovariance_is_full :
    coupledTwoMetric.PosDef ∧ coupledTwoMetric 0 1 ≠ 0 :=
  ⟨coupledTwoMetric_posDef, coupledTwoMetric_has_nonzero_offDiagonal⟩

/-- Positive full-covariance fixture: the exact Jacobian increment theorem
applies to a non-diagonal two-coordinate covariance. -/
theorem coupledCovariance_jacobianIncrement
    (jacobian : Matrix (Fin 2) (Fin 2) ℝ)
    (incomingError outgoingError delta : Fin 2 → ℝ) :
    vectorHiddenPairEnergyAfterDisplacements coupledTwoMetric coupledTwoMetric
        incomingError outgoingError delta (jacobian.mulVec delta) -
      vectorHiddenPairEnergy coupledTwoMetric coupledTwoMetric
        incomingError outgoingError =
      delta ⬝ᵥ vectorActivityGradient coupledTwoMetric coupledTwoMetric
          jacobian incomingError outgoingError +
        (1 / 2 : ℝ) *
          (delta ⬝ᵥ coupledTwoMetric⁻¹.mulVec delta +
            jacobian.mulVec delta ⬝ᵥ coupledTwoMetric⁻¹.mulVec
              (jacobian.mulVec delta)) :=
  vectorHiddenPairEnergy_jacobianIncrement_exact _ _
    coupledTwoMetric_posDef coupledTwoMetric_posDef jacobian
      incomingError outgoingError delta

/-! ## Full-covariance vector spike -/

/-- The executable scalar schedule scales an arbitrary full precision
matrix, preserving every off-diagonal coupling. -/
noncomputable def implementedFullPrecision
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (alpha : ℝ) (time distance : ℕ)
    (covariance : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  implementedSpikingPrecision alpha time distance • covariance⁻¹

theorem implementedFullPrecision_at_wavefront
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (alpha : ℝ) (distance : ℕ)
    (covariance : Matrix Index Index ℝ) :
    implementedFullPrecision alpha distance distance covariance =
      covariance⁻¹ := by
  simp [implementedFullPrecision, implementedSpikingPrecision]

theorem implementedFullPrecision_off_wavefront
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (alpha : ℝ) (time distance : ℕ) (hoff : distance ≠ time)
    (covariance : Matrix Index Index ℝ) :
    implementedFullPrecision alpha time distance covariance =
      alpha • covariance⁻¹ := by
  simp [implementedFullPrecision, implementedSpikingPrecision, hoff]

/-- At first arrival, the vector force is the unattenuated full-covariance
force, for arbitrary residual vectors. -/
theorem implementedFullPrecision_equalizes_vectorForce
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (alpha : ℝ) (distance : ℕ)
    (covariance : Matrix Index Index ℝ) (signal : Index → ℝ) :
    (implementedFullPrecision alpha distance distance covariance).mulVec signal =
      covariance⁻¹.mulVec signal := by
  rw [implementedFullPrecision_at_wavefront]

/-! ## Vector forward-reference errors -/

noncomputable def cumulativeVectorPredictionDrift
    {Index : Type*} [Fintype Index]
    (drift : ℕ → Index → ℝ) (layer : ℕ) : Index → ℝ :=
  ∑ index ∈ Finset.range layer, drift index

noncomputable def vectorStandardSettledPredictionError
    {Index : Type*} [Fintype Index]
    (initialPrediction finalActivity drift : ℕ → Index → ℝ)
    (layer : ℕ) : Index → ℝ :=
  finalActivity layer -
    (initialPrediction layer + cumulativeVectorPredictionDrift drift layer)

noncomputable def vectorForwardReferencePredictionError
    {Index : Type*} [Fintype Index]
    (initialPrediction finalActivity : ℕ → Index → ℝ)
    (layer : ℕ) : Index → ℝ :=
  finalActivity layer - initialPrediction layer

theorem vectorStandardSettledError_eq_forward_sub_cumulativeDrift
    {Index : Type*} [Fintype Index]
    (initialPrediction finalActivity drift : ℕ → Index → ℝ)
    (layer : ℕ) :
    vectorStandardSettledPredictionError initialPrediction finalActivity
        drift layer =
      vectorForwardReferencePredictionError initialPrediction finalActivity
          layer - cumulativeVectorPredictionDrift drift layer := by
  funext coordinate
  simp [vectorStandardSettledPredictionError,
    vectorForwardReferencePredictionError]
  ring

theorem cumulativeVectorPredictionDrift_const
    {Index : Type*} [Fintype Index]
    (drift : Index → ℝ) (layer : ℕ) :
    cumulativeVectorPredictionDrift (fun _ ↦ drift) layer =
      (layer : ℝ) • drift := by
  funext coordinate
  simp [cumulativeVectorPredictionDrift]

/-- Positive vector fixture: a nonzero constant drift accumulates linearly
with depth while the stored forward-reference error remains zero. -/
theorem vectorForwardReference_nonzeroDrift
    {Index : Type*} [Fintype Index]
    (drift : Index → ℝ) (coordinate : Index) (hdrift : drift coordinate ≠ 0)
    (layer : ℕ) (hlayer : 0 < layer) :
    vectorForwardReferencePredictionError (fun _ ↦ 0) (fun _ ↦ 0)
        layer coordinate = 0 ∧
      vectorStandardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ 0)
        (fun _ ↦ drift) layer coordinate ≠ 0 := by
  constructor
  · simp [vectorForwardReferencePredictionError]
  · simp [vectorStandardSettledPredictionError,
      cumulativeVectorPredictionDrift]
    exact ⟨Nat.ne_of_gt hlayer, hdrift⟩

/-- Negative vector fixture: without drift, settled and forward-reference
errors coincide in every coordinate. -/
theorem vectorForwardReference_zeroDrift
    {Index : Type*} [Fintype Index]
    (initialPrediction finalActivity : ℕ → Index → ℝ) (layer : ℕ) :
    vectorStandardSettledPredictionError initialPrediction finalActivity
        (fun _ ↦ 0) layer =
      vectorForwardReferencePredictionError initialPrediction finalActivity
        layer := by
  funext coordinate
  simp [vectorStandardSettledPredictionError,
    vectorForwardReferencePredictionError, cumulativeVectorPredictionDrift]

/-! ## Vector residual timing with arbitrary nonlinear updates -/

/-- The finite-speed residual lower bound already quantifies over arbitrary
state values and arbitrary update functions.  This specialization records
the vector-layer consequence explicitly. -/
theorem vectorResidualMainPath_exactSignal_requires_sweeps
    (width skipped sweeps : ℕ)
    (step : ChainState (Fin width → ℝ) (skipped + 1) →
      ChainState (Fin width → ℝ) (skipped + 1))
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ target₀ target₁ :
      ChainState (Fin width → ℝ) (skipped + 1))
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (htarget : target₀ (chainTerminalNode (skipped + 1)) ≠
      target₁ (chainTerminalNode (skipped + 1)))
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    skipped + 1 ≤ sweeps := by
  exact residualMainPath_exactSignal_requires_sweeps skipped sweeps step
    hbandwidth initial₀ initial₁ target₀ target₁ haway htarget hsettle₀ hsettle₁

structure VectorDepthRepairCertificate : Prop where
  fullCovarianceIncrement :
    ∀ {Hidden Outgoing : Type*}
      [Fintype Hidden] [DecidableEq Hidden]
      [Fintype Outgoing] [DecidableEq Outgoing]
      (incomingCovariance : Matrix Hidden Hidden ℝ)
      (outgoingCovariance : Matrix Outgoing Outgoing ℝ),
      incomingCovariance.PosDef → outgoingCovariance.PosDef →
      ∀ (jacobian : Matrix Outgoing Hidden ℝ)
        (incomingError : Hidden → ℝ) (outgoingError : Outgoing → ℝ)
        (delta : Hidden → ℝ),
        vectorHiddenPairEnergyAfterDisplacements incomingCovariance
            outgoingCovariance incomingError outgoingError delta
            (jacobian.mulVec delta) -
          vectorHiddenPairEnergy incomingCovariance outgoingCovariance
            incomingError outgoingError =
          delta ⬝ᵥ vectorActivityGradient incomingCovariance
              outgoingCovariance jacobian incomingError outgoingError +
            (1 / 2 : ℝ) *
              (delta ⬝ᵥ incomingCovariance⁻¹.mulVec delta +
                jacobian.mulVec delta ⬝ᵥ outgoingCovariance⁻¹.mulVec
                  (jacobian.mulVec delta))
  fullPrecisionSpike :
    ∀ {Index : Type*} [Fintype Index] [DecidableEq Index]
      (alpha : ℝ) (distance : ℕ) (covariance : Matrix Index Index ℝ)
      (signal : Index → ℝ),
      (implementedFullPrecision alpha distance distance covariance).mulVec
          signal = covariance⁻¹.mulVec signal
  vectorForwardPartition :
    ∀ {Index : Type*} [Fintype Index]
      (initialPrediction finalActivity drift : ℕ → Index → ℝ)
      (layer : ℕ),
      vectorStandardSettledPredictionError initialPrediction finalActivity
          drift layer =
        vectorForwardReferencePredictionError initialPrediction finalActivity
            layer - cumulativeVectorPredictionDrift drift layer

theorem vectorDepthRepair_crown : VectorDepthRepairCertificate where
  fullCovarianceIncrement := fun incomingCovariance outgoingCovariance
    hincoming houtgoing jacobian incomingError outgoingError delta ↦
      vectorHiddenPairEnergy_jacobianIncrement_exact incomingCovariance
        outgoingCovariance hincoming houtgoing jacobian incomingError
        outgoingError delta
  fullPrecisionSpike := implementedFullPrecision_equalizes_vectorForce
  vectorForwardPartition :=
    vectorStandardSettledError_eq_forward_sub_cumulativeDrift

#print axioms vectorHiddenPairEnergy_jacobianIncrement_exact
#print axioms vectorWeightEnergy_increment_exact
#print axioms nonlinearJacobianRemainder_hasFDerivAt_zero
#print axioms nonlinearVectorHiddenPairEnergy_increment_exact
#print axioms coordinateSquarePrediction_hasFDerivAt_zero
#print axioms vectorResidualMainPath_exactSignal_requires_sweeps
#print axioms vectorDepthRepair_crown

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
