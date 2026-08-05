import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActiveFrontierSettling
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DeepErrorCoordinateAcceleration

/-!
# Contraction from captured active-frontier mass

An active-frontier solver improves only the selected coordinates while leaving
the discarded tail unchanged.  This file quantifies the resulting full-space
contraction.  If the frontier contains at least a fraction `f` of the current
squared error mass and its inner solver contracts by `q`, then the whole
squared error contracts by

`1 - f * (1 - q^2)`.

The theorem separates two executable obligations: an exact mass-capture report
for the selected frontier and a contraction certificate for the active solver.
It then instantiates the active certificate with the existing two-rate
error-coordinate block.  No convergence claim is inferred from a sparse mask
or from a one-point curvature observation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ActiveFrontierContraction

open ActiveFrontierSettling
open DeepErrorCoordinateAcceleration
open SpectralPolynomialAcceleration

noncomputable section

variable {Active Tail : Type*}
  [NormedAddCommGroup Active] [NormedAddCommGroup Tail]

/-- Replace the selected component while preserving the discarded tail. -/
def replaceActive
    (activeNext : Active) (direction : SplitDirection Active Tail) :
    SplitDirection Active Tail :=
  WithLp.toLp 2 (activeNext, direction.snd)

@[simp] theorem replaceActive_fst
    (activeNext : Active) (direction : SplitDirection Active Tail) :
    (replaceActive activeNext direction).fst = activeNext :=
  rfl

@[simp] theorem replaceActive_snd
    (activeNext : Active) (direction : SplitDirection Active Tail) :
    (replaceActive activeNext direction).snd = direction.snd :=
  rfl

/-- Full-space squared contraction factor induced by captured mass `fraction`
and active-space contraction factor `q`. -/
def capturedContractionFactor (fraction q : ℝ) : ℝ :=
  1 - fraction * (1 - q ^ 2)

theorem capturedContractionFactor_nonneg
    {direction : SplitDirection Active Tail} {fraction q : ℝ}
    (capture : SquaredMassCapture direction fraction)
    (hqnonneg : 0 ≤ q) (hqle : q ≤ 1) :
    0 ≤ capturedContractionFactor fraction q := by
  unfold capturedContractionFactor
  have hqSqNonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hqSqLe : q ^ 2 ≤ 1 := by nlinarith
  nlinarith [capture.fraction_nonneg, capture.fraction_le_one]

theorem capturedContractionFactor_lt_one
    {fraction q : ℝ} (hfraction : 0 < fraction)
    (hqnonneg : 0 ≤ q) (hqlt : q < 1) :
    capturedContractionFactor fraction q < 1 := by
  have hqgap : 0 < 1 - q ^ 2 := by
    have hproduct : 0 < (1 - q) * (1 + q) :=
      mul_pos (sub_pos.mpr hqlt) (by linarith)
    nlinarith
  have hloss : 0 < fraction * (1 - q ^ 2) :=
    mul_pos hfraction hqgap
  unfold capturedContractionFactor
  linarith

/-- A contraction of the selected component plus an unchanged tail yields the
exact captured-mass contraction factor on the full squared norm. -/
theorem replaceActive_norm_sq_le
    {direction : SplitDirection Active Tail}
    {activeNext : Active} {fraction q : ℝ}
    (capture : SquaredMassCapture direction fraction)
    (hqnonneg : 0 ≤ q) (hqle : q ≤ 1)
    (hactive : ‖activeNext‖ ≤ q * ‖direction.fst‖) :
    ‖replaceActive activeNext direction‖ ^ 2 ≤
      capturedContractionFactor fraction q * ‖direction‖ ^ 2 := by
  have hactiveSq :
      ‖activeNext‖ ^ 2 ≤ (q * ‖direction.fst‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hqnonneg (norm_nonneg _))).2 hactive
  have hcurrent :
      ‖direction‖ ^ 2 =
        ‖direction.fst‖ ^ 2 + ‖direction.snd‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 direction
  have hnext :
      ‖replaceActive activeNext direction‖ ^ 2 =
        ‖activeNext‖ ^ 2 + ‖direction.snd‖ ^ 2 := by
    simpa [replaceActive] using
      WithLp.prod_norm_sq_eq_of_L2
        (replaceActive activeNext direction)
  have hcaptured :
      fraction * ‖direction‖ ^ 2 ≤ ‖direction.fst‖ ^ 2 := by
    simpa using capture.captured
  have hqSqLe : q ^ 2 ≤ 1 := by nlinarith
  rw [hnext, capturedContractionFactor]
  nlinarith [sq_nonneg ‖direction.fst‖, sq_nonneg ‖direction.snd‖]

/-! ## Binding to the active two-rate error-coordinate block -/

variable {ActiveCoord Mode TailCoord : Type*}
  [Fintype ActiveCoord] [Fintype Mode]
  [NormedAddCommGroup TailCoord]

abbrev FrontierError :=
  SplitDirection (ThreeSiteActiveError ActiveCoord) TailCoord

/-- Apply the two-rate error-coordinate solver on the selected active
coordinates while preserving the tail exactly. -/
def activeTwoRateFrontierStep
    (precision rho smooth : ℝ)
    (taskGradient :
      ThreeSiteActiveError ActiveCoord →
        ThreeSiteActiveError ActiveCoord)
    (state : FrontierError (ActiveCoord := ActiveCoord)
      (TailCoord := TailCoord)) :
    FrontierError (ActiveCoord := ActiveCoord) (TailCoord := TailCoord) :=
  WithLp.toLp 2
    (activeTwoRateBlock precision rho smooth taskGradient state.fst,
      state.snd)

/-- The source-bound active two-rate certificate and an exact frontier-mass
certificate compose into a full stored-error contraction. -/
theorem ModalTaskGradientCertificate.activeFrontier_distance_sq_le
    {taskGradient :
      ThreeSiteActiveError ActiveCoord →
        ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (hrho : 0 ≤ rho) (hsmooth : 0 ≤ smooth)
    (hdominates : rho < precision)
    (left right :
      FrontierError (ActiveCoord := ActiveCoord) (TailCoord := TailCoord))
    (capture : SquaredMassCapture (left - right) fraction) :
    ‖activeTwoRateFrontierStep precision rho smooth taskGradient left -
        activeTwoRateFrontierStep precision rho smooth taskGradient right‖ ^ 2 ≤
      capturedContractionFactor fraction
          (twoRateBound (precision - rho) (precision + smooth)) *
        ‖left - right‖ ^ 2 := by
  let q := twoRateBound (precision - rho) (precision + smooth)
  have hlower : 0 < precision - rho := sub_pos.mpr hdominates
  have hupper : precision - rho ≤ precision + smooth := by linarith
  have hqnonneg : 0 ≤ q :=
    twoRateBound_nonneg hlower hupper
  have hqle : q ≤ 1 :=
    (twoRateBound_lt_one hlower hupper).le
  have hactive :
      ‖activeTwoRateBlock precision rho smooth taskGradient left.fst -
          activeTwoRateBlock precision rho smooth taskGradient right.fst‖ ≤
        q * ‖(left - right).fst‖ := by
    simpa [q] using
      certificate.twoRateBlock_distance_le
        hrho hsmooth hdominates left.fst right.fst
  have hfull := replaceActive_norm_sq_le
    capture hqnonneg hqle hactive
  have hstepDifference :
      activeTwoRateFrontierStep precision rho smooth taskGradient left -
          activeTwoRateFrontierStep precision rho smooth taskGradient right =
        replaceActive
          (activeTwoRateBlock precision rho smooth taskGradient left.fst -
            activeTwoRateBlock precision rho smooth taskGradient right.fst)
          (left - right) := by
    apply WithLp.ofLp_injective 2
    simp [activeTwoRateFrontierStep, replaceActive]
  rw [hstepDifference]
  exact hfull

/-! ## Exact positive and negative fixtures -/

def halfActive (value : ℝ) : ℝ :=
  value / 2

theorem halfActive_contracts (value : ℝ) :
    ‖halfActive value‖ ≤ (1 / 2 : ℝ) * ‖value‖ := by
  rw [halfActive, norm_div, Real.norm_eq_abs]
  norm_num
  ring_nf
  exact le_rfl

/-- Contracting the active coordinate by one half while it carries `9/25` of
the mass gives the exact full squared factor `73/100`. -/
theorem threeFour_halfActive_exact :
    ‖replaceActive (halfActive threeFourDirection.fst)
        threeFourDirection‖ ^ 2 =
      (73 / 100 : ℝ) * ‖threeFourDirection‖ ^ 2 := by
  rw [threeFourDirection_norm]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  norm_num [replaceActive, halfActive, threeFourDirection, Real.norm_eq_abs]

/-- If the selected frontier captures no mass, even an exact active solve can
leave the full error unchanged. -/
theorem missedDirection_exactActiveSolve_does_not_contract :
    replaceActive 0 missedDirection = missedDirection := by
  rfl

#print axioms replaceActive_norm_sq_le
#print axioms ModalTaskGradientCertificate.activeFrontier_distance_sq_le
#print axioms threeFour_halfActive_exact
#print axioms missedDirection_exactActiveSolve_does_not_contract

end

end ActiveFrontierContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
