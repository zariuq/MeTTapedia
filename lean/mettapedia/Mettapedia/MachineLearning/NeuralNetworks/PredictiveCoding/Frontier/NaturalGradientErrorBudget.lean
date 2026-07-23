import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FiniteSettlingGradientGap
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherGeometry

/-!
# PC-to-natural-gradient error budgets

An observed optimizer displacement is not the same object as a settled local
PC gradient.  A settled local gradient is not automatically a covariance-aware
natural direction, and a damped approximate direction is not the undamped
natural direction.  This file keeps those errors separate and composes them by
the norm triangle inequality.  The finite-settling term is discharged by the
existing Hilbert-space PC theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace

section AbstractBudget

variable {Parameter : Type*} [NormedAddCommGroup Parameter]

/-- Four-stage approximation certificate for an observed PC optimizer step.
All vectors must already use the same rate/units; that normalization is not
silently inserted by the certificate. -/
structure PCNaturalErrorCertificate
    (observed settled equilibrium approximate natural : Parameter)
    (optimizerError settlingError covarianceError dampingError : ℝ) : Prop where
  optimizer : ‖observed - settled‖ ≤ optimizerError
  settling : ‖settled - equilibrium‖ ≤ settlingError
  covariance : ‖equilibrium - approximate‖ ≤ covarianceError
  damping : ‖approximate - natural‖ ≤ dampingError

/-- Complete PC-to-natural error budget. -/
theorem PCNaturalErrorCertificate.total
    (observed settled equilibrium approximate natural : Parameter)
    (optimizerError settlingError covarianceError dampingError : ℝ)
    (certificate : PCNaturalErrorCertificate observed settled equilibrium
      approximate natural optimizerError settlingError covarianceError
      dampingError) :
    ‖observed - natural‖ ≤
      optimizerError + settlingError + covarianceError + dampingError := by
  calc
    ‖observed - natural‖ ≤
        ‖observed - settled‖ + ‖settled - natural‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (observed - settled) (settled - natural)
    _ ≤ optimizerError + ‖settled - natural‖ :=
      add_le_add certificate.optimizer (le_refl _)
    _ ≤ optimizerError +
        (‖settled - equilibrium‖ + ‖equilibrium - natural‖) := by
      gcongr
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (settled - equilibrium) (equilibrium - natural)
    _ ≤ optimizerError +
        (settlingError + ‖equilibrium - natural‖) := by
      gcongr
      exact certificate.settling
    _ ≤ optimizerError +
        (settlingError +
          (‖equilibrium - approximate‖ + ‖approximate - natural‖)) := by
      gcongr
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (equilibrium - approximate) (approximate - natural)
    _ ≤ optimizerError + settlingError + covarianceError + dampingError := by
      nlinarith [certificate.covariance, certificate.damping]

end AbstractBudget

section FiniteSettlingComposition

variable {Latent Parameter : Type*}
  [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
  [NormedAddCommGroup Parameter]

/-- The Hilbert finite-settling theorem supplies the settling rung of the
four-stage natural-gradient budget.  Equilibrium PC/BP mismatch remains an
explicit addend. -/
theorem hilbertObservedPC_to_natural_le
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (gradientReadout : Latent → Parameter) (equilibriumGradient : Parameter)
    (hK : 0 ≤ K)
    (hreadout : HilbertGradientReadoutLipschitzAt gradientReadout target K)
    (sweeps : ℕ)
    (observed approximateNatural natural : Parameter)
    (optimizerError covarianceError dampingError : ℝ)
    (hoptimizer : ‖observed - gradientReadout
      ((hilbertSettlingStep model rate)^[sweeps] initial)‖ ≤ optimizerError)
    (hcovariance : ‖equilibriumGradient - approximateNatural‖ ≤ covarianceError)
    (hdamping : ‖approximateNatural - natural‖ ≤ dampingError) :
    ‖observed - natural‖ ≤
      optimizerError +
        (hilbertFiniteSettlingRemainder mu L rate K initial target sweeps +
          hilbertEquilibriumGradientMismatch gradientReadout target
            equilibriumGradient) + covarianceError + dampingError := by
  let settled := gradientReadout
    ((hilbertSettlingStep model rate)^[sweeps] initial)
  have hsettling := hilbertFiniteSettlingGradientGap_le model hL hrate
    hcoefficient target initial htarget gradientReadout equilibriumGradient
    hK hreadout sweeps
  have certificate : PCNaturalErrorCertificate observed settled
      equilibriumGradient approximateNatural natural optimizerError
      (hilbertFiniteSettlingRemainder mu L rate K initial target sweeps +
        hilbertEquilibriumGradientMismatch gradientReadout target
          equilibriumGradient)
      covarianceError dampingError := by
    refine ⟨?_, ?_, hcovariance, hdamping⟩
    · exact hoptimizer
    · simpa [settled, hilbertFiniteSettlingRemainder] using hsettling
  exact certificate.total observed settled equilibriumGradient
    approximateNatural natural optimizerError
    (hilbertFiniteSettlingRemainder mu L rate K initial target sweeps +
      hilbertEquilibriumGradientMismatch gradientReadout target
        equilibriumGradient)
    covarianceError dampingError

end FiniteSettlingComposition

/-! ## Positive and negative scalar fixtures -/

theorem zeroPCNaturalErrorCertificate_fixture :
    PCNaturalErrorCertificate (0 : ℝ) 0 0 0 0 0 0 0 0 := by
  constructor <;> norm_num

/-- A scalar implementation may incur all four errors simultaneously.  This
fixture prevents any rung, including the Adam/outer-optimizer rung, from being
dropped merely because the update is labelled predictive coding. -/
theorem scalarPrecisionAdam_nonzeroBudgetFixture :
    PCNaturalErrorCertificate (4 : ℝ) 3 2 1 0 1 1 1 1 ∧
      |(4 : ℝ) - 0| = 4 := by
  constructor
  · constructor <;> norm_num [Real.norm_eq_abs]
  · norm_num

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
