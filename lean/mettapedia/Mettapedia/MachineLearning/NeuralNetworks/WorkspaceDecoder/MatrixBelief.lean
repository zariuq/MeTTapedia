import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator

/-!
# Matrix-valued Gaussian beliefs in natural coordinates

The primal state is the Gaussian information pair `(η, Λ)`, with natural
parameter `η = Λ μ` and precision matrix `Λ`.  Independent evidence fuses by
componentwise addition.  Mean, covariance, and matrix gain are derived charts
of this additive state, exactly as strength and confidence are derived charts
of binary evidence counts.

The operator adapter transports the existing predictive-coding
`LinearGaussianOperatorModel`; no posterior or equilibrium theory is
re-derived here.  All statements are finite-dimensional linear-Gaussian and
make no claim about nonlinear learned belief updates.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

universe uIndex

/-! ## Additive Gaussian information evidence -/

/-- Multivariate Gaussian evidence in natural coordinates `(η, Λ)`.  This raw
carrier includes zero evidence and is therefore closed under a commutative
additive monoid.  Properness is a separate positive-definiteness predicate. -/
structure GaussianInformation (Index : Type uIndex) where
  naturalParameter : Index → ℝ
  precision : Matrix Index Index ℝ

namespace GaussianInformation

variable {Index : Type uIndex}

@[ext] theorem ext'
    {first second : GaussianInformation Index}
    (hnatural : first.naturalParameter = second.naturalParameter)
    (hprecision : first.precision = second.precision) : first = second := by
  cases first
  cases second
  simp_all

instance : Zero (GaussianInformation Index) where
  zero := ⟨0, 0⟩

instance : Add (GaussianInformation Index) where
  add first second :=
    ⟨first.naturalParameter + second.naturalParameter,
      first.precision + second.precision⟩

@[simp] theorem zero_naturalParameter :
    (0 : GaussianInformation Index).naturalParameter = 0 :=
  rfl

@[simp] theorem zero_precision :
    (0 : GaussianInformation Index).precision = 0 :=
  rfl

@[simp] theorem add_naturalParameter
    (first second : GaussianInformation Index) :
    (first + second).naturalParameter =
      first.naturalParameter + second.naturalParameter :=
  rfl

@[simp] theorem add_precision
    (first second : GaussianInformation Index) :
    (first + second).precision = first.precision + second.precision :=
  rfl

instance : AddCommMonoid (GaussianInformation Index) where
  add_assoc first second third := by
    apply GaussianInformation.ext'
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
  zero_add information := by
    apply GaussianInformation.ext' <;> exact zero_add _
  add_zero information := by
    apply GaussianInformation.ext' <;> exact add_zero _
  add_comm first second := by
    apply GaussianInformation.ext' <;> exact add_comm _ _
  nsmul := nsmulRec

/-- Proper Gaussian information has a positive-definite precision matrix. -/
def Proper [Fintype Index] (information : GaussianInformation Index) : Prop :=
  information.precision.PosDef

/-- Independent proper information packets remain proper after fusion. -/
theorem Proper.add [Fintype Index]
    {first second : GaussianInformation Index}
    (hfirst : first.Proper) (hsecond : second.Proper) :
    (first + second).Proper := by
  exact Matrix.PosDef.add hfirst hsecond

/-- Natural-coordinate packet induced by a moment mean and precision. -/
noncomputable def ofMeanPrecision [Fintype Index]
    (mean : Index → ℝ) (precision : Matrix Index Index ℝ) :
    GaussianInformation Index where
  naturalParameter := precision.mulVec mean
  precision := precision

/-- Moment-coordinate mean derived from a proper information state.  The
formula is defined on the raw carrier; properness licenses its Bayesian use. -/
noncomputable def mean [Fintype Index] [DecidableEq Index]
    (information : GaussianInformation Index) : Index → ℝ :=
  information.precision⁻¹.mulVec information.naturalParameter

/-- Covariance chart derived from information precision. -/
noncomputable def covariance [Fintype Index] [DecidableEq Index]
    (information : GaussianInformation Index) : Matrix Index Index ℝ :=
  information.precision⁻¹

/-- Direct adapter from the sealed linear-Gaussian operator posterior. -/
noncomputable def ofOperatorModel
    {Residual : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Index Residual) :
    GaussianInformation Index where
  naturalParameter := model.naturalParameter
  precision := model.posteriorPrecision

/-- The operator adapter is proper by the sealed posterior-precision theorem. -/
theorem ofOperatorModel_proper
    {Residual : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Index Residual) :
    (ofOperatorModel model).Proper :=
  model.posteriorPrecision_posDef

/-- PC transport: the derived information-form mean is exactly the coordinate
function of the sealed operator posterior mean. -/
theorem ofOperatorModel_mean_eq_posteriorMean
    {Residual : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Index Residual) :
    (ofOperatorModel model).mean = fun index => model.posteriorMean index := by
  rfl

/-- PC equilibrium transported into natural coordinates. -/
theorem operator_equilibrium_iff_eq_informationMean
    {Residual : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Index Residual)
    (state : LinearGaussianOperatorSpace Index) :
    model.Equilibrium state ↔
      (fun index => state index) = (ofOperatorModel model).mean := by
  rw [model.equilibrium_iff_eq_posteriorMean]
  constructor
  · rintro rfl
    exact (ofOperatorModel_mean_eq_posteriorMean model).symm
  · intro h
    apply PiLp.ext
    intro index
    have hindex := congrFun h index
    simpa [ofOperatorModel_mean_eq_posteriorMean model] using hindex

end GaussianInformation

/-! ## Matrix gain and moment chart of information addition -/

variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- Matrix gain obtained by viewing additive precision fusion in moment
coordinates. -/
noncomputable def matrixPrecisionGain
    (priorPrecision observationPrecision : Matrix Index Index ℝ) :
    Matrix Index Index ℝ :=
  (priorPrecision + observationPrecision)⁻¹ * observationPrecision

/-- Moment-coordinate shadow of adding an observation information packet. -/
noncomputable def matrixPrecisionInterpolate
    (oldMean proposedMean : Index → ℝ)
    (priorPrecision observationPrecision : Matrix Index Index ℝ) :
    Index → ℝ :=
  oldMean + (matrixPrecisionGain priorPrecision observationPrecision).mulVec
    (proposedMean - oldMean)

/-- Matrix information crown: adding `(Λ₁ μ₁, Λ₁)` and `(Λ₂ μ₂, Λ₂)`
then taking the mean is exactly gain-scheduled interpolation in moment
coordinates. -/
theorem matrixPrecisionInterpolate_eq_fusedInformationMean
    (oldMean proposedMean : Index → ℝ)
    (priorPrecision observationPrecision : Matrix Index Index ℝ)
    (hprior : priorPrecision.PosDef)
    (hobservation : observationPrecision.PosDef) :
    matrixPrecisionInterpolate oldMean proposedMean
        priorPrecision observationPrecision =
      (GaussianInformation.ofMeanPrecision oldMean priorPrecision +
        GaussianInformation.ofMeanPrecision proposedMean observationPrecision).mean := by
  let totalPrecision := priorPrecision + observationPrecision
  have htotal : totalPrecision.PosDef := hprior.add hobservation
  have hdet : IsUnit totalPrecision.det :=
    (Matrix.isUnit_iff_isUnit_det totalPrecision).mp htotal.isUnit
  have hrecover : totalPrecision⁻¹.mulVec (totalPrecision.mulVec oldMean) = oldMean := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul totalPrecision hdet,
      Matrix.one_mulVec]
  unfold matrixPrecisionInterpolate matrixPrecisionGain
  change oldMean + (totalPrecision⁻¹ * observationPrecision).mulVec
      (proposedMean - oldMean) =
    totalPrecision⁻¹.mulVec
      (priorPrecision.mulVec oldMean +
        observationPrecision.mulVec proposedMean)
  calc
    oldMean + (totalPrecision⁻¹ * observationPrecision).mulVec
        (proposedMean - oldMean) =
        totalPrecision⁻¹.mulVec (totalPrecision.mulVec oldMean) +
          totalPrecision⁻¹.mulVec
            (observationPrecision.mulVec (proposedMean - oldMean)) := by
      rw [hrecover, ← Matrix.mulVec_mulVec]
    _ = totalPrecision⁻¹.mulVec
          (totalPrecision.mulVec oldMean +
            observationPrecision.mulVec (proposedMean - oldMean)) := by
      rw [Matrix.mulVec_add]
    _ = totalPrecision⁻¹.mulVec
          (priorPrecision.mulVec oldMean +
            observationPrecision.mulVec proposedMean) := by
      congr 1
      funext index
      simp only [totalPrecision, Matrix.add_mulVec, Matrix.mulVec_sub,
        Pi.add_apply, Pi.sub_apply]
      ring

/-! ## Covariance/Riccati chart -/

/-- Identity-observation multivariate Riccati measurement update, expressed
in the additive information chart. -/
noncomputable def matrixRiccatiStep
    (priorCovariance observationCovariance : Matrix Index Index ℝ) :
    Matrix Index Index ℝ :=
  (priorCovariance⁻¹ + observationCovariance⁻¹)⁻¹

/-- Positive-definite covariances remain positive definite after the matrix
Riccati measurement step. -/
theorem matrixRiccatiStep_posDef
    (priorCovariance observationCovariance : Matrix Index Index ℝ)
    (hprior : priorCovariance.PosDef)
    (hobservation : observationCovariance.PosDef) :
    (matrixRiccatiStep priorCovariance observationCovariance).PosDef := by
  exact (hprior.inv.add hobservation.inv).inv

/-- Covariance-coordinate matrix Kalman gain, defined by transport through
the information chart. -/
noncomputable def matrixKalmanGain
    (priorCovariance observationCovariance : Matrix Index Index ℝ) :
    Matrix Index Index ℝ :=
  matrixPrecisionGain priorCovariance⁻¹ observationCovariance⁻¹

/-- Fusing two moment/precision packets produces exactly the matrix Riccati
covariance in the covariance chart. -/
theorem fusedInformation_covariance_eq_matrixRiccatiStep
    (priorMean observationMean : Index → ℝ)
    (priorCovariance observationCovariance : Matrix Index Index ℝ) :
    (GaussianInformation.ofMeanPrecision priorMean priorCovariance⁻¹ +
      GaussianInformation.ofMeanPrecision observationMean
        observationCovariance⁻¹).covariance =
      matrixRiccatiStep priorCovariance observationCovariance := by
  rfl

/-! ## Positive and negative fixtures -/

/-- Natural parameters and precisions add componentwise on a concrete
one-dimensional information packet. -/
theorem gaussianInformation_add_positiveExample :
    ((⟨fun _ : Unit => 2, fun _ _ => 3⟩ : GaussianInformation Unit) +
      ⟨fun _ : Unit => 5, fun _ _ => 7⟩) =
        ⟨fun _ : Unit => 7, fun _ _ => 10⟩ := by
  apply GaussianInformation.ext' <;> funext <;> norm_num

/-- Zero information is the additive identity but is not a proper Gaussian
belief on a nonempty coordinate space. -/
theorem zeroGaussianInformation_not_proper :
    ¬GaussianInformation.Proper (0 : GaussianInformation Unit) := by
  intro hproper
  have hpositive := hproper.diag_pos (i := ())
  norm_num [GaussianInformation.Proper] at hpositive

#print axioms GaussianInformation.Proper.add
#print axioms GaussianInformation.ofOperatorModel_mean_eq_posteriorMean
#print axioms GaussianInformation.operator_equilibrium_iff_eq_informationMean
#print axioms matrixPrecisionInterpolate_eq_fusedInformationMean
#print axioms matrixRiccatiStep_posDef
#print axioms fusedInformation_covariance_eq_matrixRiccatiStep
#print axioms gaussianInformation_add_positiveExample
#print axioms zeroGaussianInformation_not_proper

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
