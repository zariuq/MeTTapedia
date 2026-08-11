import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedCreditReadout
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.BlockSettlingStability

/-!
# Finite-budget solver substitution and warm-start credit

Sharing a stationary set licenses an infinite-settling comparison, not the
finite inference depth used by a predictive-coding trainer.  This file states
the missing finite-work contract.

Two contractive solvers that share a fixed point may use different
initializers and different step budgets.  Their credit readouts differ by at
most the sum of their two geometric endpoint-error budgets.  For one solver,
a pairwise Lipschitz readout gives the sharper warm-versus-cold bound directly
from the initializer displacement.  The same budget yields an observable
positive-alignment gate for substituting one finite credit direction for the
other.

For the block-diagonal quadratic model, exact iterate formulas make the
comparison computable coordinate by coordinate.  A negative fixture proves
that identical stationary sets alone do not imply identical finite
trajectories or credit.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FiniteSolverSubstitution

open AmortizedInitialization
open AmortizedCreditReadout
open LocalAmortizedInitialization
open WorkNormalizedTruncation
open BlockSettlingStability
open scoped InnerProductSpace

noncomputable section

variable {State Credit : Type*}
  [NormedAddCommGroup State] [NormedAddCommGroup Credit]

/-! ## Warm-start dependence for one characterized solver -/

/-- A pairwise Lipschitz credit readout.  This stronger, global form is used
when comparing two finite trajectories rather than one trajectory with a
fixed endpoint. -/
def CreditReadoutPairwiseLipschitz
    (readout : State → Credit) (constant : ℝ) : Prop :=
  ∀ left right,
    ‖readout left - readout right‖ ≤ constant * ‖left - right‖

/-- Pairwise Lipschitz continuity specializes to the existing fixed-point
readout condition at every chosen target. -/
theorem pairwiseLipschitz_to_lipschitzAt
    (readout : State → Credit) (constant : ℝ)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (target : State) :
    CreditReadoutLipschitzAt readout target constant := by
  intro state
  exact hreadout state target

/-- After a fixed number of corrective steps, the observable effect of
changing only the initializer contracts geometrically.  This is the direct
warm-start parity certificate. -/
theorem warmStart_credit_difference_le
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State) (steps : ℕ) :
    ‖readout (solver^[steps] warm) - readout (solver^[steps] cold)‖ ≤
      constant *
        (certificate.factor ^ steps * ‖warm - cold‖) := by
  calc
    ‖readout (solver^[steps] warm) - readout (solver^[steps] cold)‖ ≤
        constant * ‖solver^[steps] warm - solver^[steps] cold‖ :=
      hreadout _ _
    _ ≤ constant *
        (certificate.factor ^ steps * ‖warm - cold‖) :=
      mul_le_mul_of_nonneg_left
        (iterate_initializer_distance_le certificate warm cold steps)
        hconstant

/-- If the warm initializer is already `factor^savedSteps` times closer to the
fixed point, then its `warmSteps` geometric error budget is no larger than the
cold initializer's budget after `warmSteps + savedSteps` steps.  This is the
work-saving inequality behind a registered reduction in inference depth. -/
theorem warmInitializer_savesSteps_geometricBudget
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target warm cold : State) (warmSteps savedSteps : ℕ)
    (hcloser :
      ‖warm - target‖ ≤
        certificate.factor ^ savedSteps * ‖cold - target‖) :
    certificate.factor ^ warmSteps * ‖warm - target‖ ≤
      certificate.factor ^ (warmSteps + savedSteps) *
        ‖cold - target‖ := by
  calc
    certificate.factor ^ warmSteps * ‖warm - target‖ ≤
        certificate.factor ^ warmSteps *
          (certificate.factor ^ savedSteps * ‖cold - target‖) :=
      mul_le_mul_of_nonneg_left hcloser
        (pow_nonneg certificate.factor_nonneg warmSteps)
    _ = certificate.factor ^ (warmSteps + savedSteps) *
        ‖cold - target‖ := by rw [pow_add]; ring

/-- The work-saving initializer condition composes with a Lipschitz credit
readout: fewer warm-started sweeps meet the credit-error budget certified for
the longer cold solve. -/
theorem warmInitializer_savesSteps_creditBudget
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target warm cold : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (warmSteps savedSteps : ℕ)
    (hcloser :
      ‖warm - target‖ ≤
        certificate.factor ^ savedSteps * ‖cold - target‖) :
    ‖readout (solver^[warmSteps] warm) - readout target‖ ≤
      constant *
        (certificate.factor ^ (warmSteps + savedSteps) *
          ‖cold - target‖) := by
  calc
    ‖readout (solver^[warmSteps] warm) - readout target‖ ≤
        constant *
          (certificate.factor ^ warmSteps * ‖warm - target‖) :=
      iterate_creditReadout_to_fixedPoint_le certificate target warm htarget
        readout constant hconstant hreadout warmSteps
    _ ≤ constant *
        (certificate.factor ^ (warmSteps + savedSteps) *
          ‖cold - target‖) :=
      mul_le_mul_of_nonneg_left
        (warmInitializer_savesSteps_geometricBudget certificate target warm
          cold warmSteps savedSteps hcloser)
        hconstant

/-! ## Local same-basin acceleration -/

/-- In a nonlinear solver's certified invariant neighborhood, warm-versus-cold
credit parity holds only after both initializers are shown to belong to that
same neighborhood. -/
theorem localWarmStart_credit_difference_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (steps : ℕ) :
    ‖readout (solver^[steps] warm) - readout (solver^[steps] cold)‖ ≤
      constant *
        (certificate.factor ^ steps * ‖warm - cold‖) := by
  calc
    ‖readout (solver^[steps] warm) - readout (solver^[steps] cold)‖ ≤
        constant * ‖solver^[steps] warm - solver^[steps] cold‖ :=
      hreadout _ _
    _ ≤ constant *
        (certificate.factor ^ steps * ‖warm - cold‖) :=
      mul_le_mul_of_nonneg_left
        (LocalAmortizedInitialization.iterate_initializer_distance_le
          certificate warm cold hwarm hcold steps)
        hconstant

/-- Finite substitution for two nonlinear solvers is licensed inside their
explicit invariant neighborhoods.  Both solvers must certify the same target,
and each initializer must remain in the corresponding basin certificate. -/
theorem localFiniteSolver_credit_difference_le
    {referenceSolver candidateSolver : State → State}
    {referenceCenter candidateCenter : State}
    {referenceRadius candidateRadius : ℝ}
    (referenceCertificate :
      LocalContractionCertificate referenceSolver referenceCenter referenceRadius)
    (candidateCertificate :
      LocalContractionCertificate candidateSolver candidateCenter candidateRadius)
    (target referenceInitial candidateInitial : State)
    (referenceTargetMem :
      InClosedBall referenceCenter referenceRadius target)
    (candidateTargetMem :
      InClosedBall candidateCenter candidateRadius target)
    (referenceInitialMem :
      InClosedBall referenceCenter referenceRadius referenceInitial)
    (candidateInitialMem :
      InClosedBall candidateCenter candidateRadius candidateInitial)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ) :
    ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
        readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
      constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) := by
  have hcandidate :=
    LocalAmortizedInitialization.iterate_initializer_to_fixedPoint_le
      candidateCertificate target candidateInitial candidateTargetMem
      candidateInitialMem candidateFixed candidateSteps
  have hreference :=
    LocalAmortizedInitialization.iterate_initializer_to_fixedPoint_le
      referenceCertificate target referenceInitial referenceTargetMem
      referenceInitialMem referenceFixed referenceSteps
  calc
    ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
        readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
        ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target‖ +
          ‖readout target -
            readout (referenceSolver^[referenceSteps] referenceInitial)‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target)
          (readout target -
            readout (referenceSolver^[referenceSteps] referenceInitial))
    _ = ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target‖ +
          ‖readout (referenceSolver^[referenceSteps] referenceInitial) -
            readout target‖ := by
      rw [show readout target -
          readout (referenceSolver^[referenceSteps] referenceInitial) =
          -(readout (referenceSolver^[referenceSteps] referenceInitial) -
            readout target) by abel, norm_neg]
    _ ≤ constant *
          ‖candidateSolver^[candidateSteps] candidateInitial - target‖ +
        constant *
          ‖referenceSolver^[referenceSteps] referenceInitial - target‖ :=
      add_le_add (hreadout _) (hreadout _)
    _ ≤ constant *
          (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖) +
        constant *
          (referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcandidate hconstant)
        (mul_le_mul_of_nonneg_left hreference hconstant)
    _ = constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) := by ring

/-! ## Two-solver finite-work substitution -/

/-- Two possibly different contractive solvers, initializers, and work
budgets share a finite-credit comparison whenever they share a fixed point.
The theorem deliberately compares finite iterates; equality of stationary
sets alone is not used as a surrogate. -/
theorem finiteSolver_credit_difference_le
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ) :
    ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
        readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
      constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) := by
  have hcandidate := iterate_initializer_to_fixedPoint_le
    candidateCertificate target candidateInitial candidateFixed candidateSteps
  have hreference := iterate_initializer_to_fixedPoint_le
    referenceCertificate target referenceInitial referenceFixed referenceSteps
  calc
    ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
        readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
        ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target‖ +
          ‖readout target -
            readout (referenceSolver^[referenceSteps] referenceInitial)‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target)
          (readout target -
            readout (referenceSolver^[referenceSteps] referenceInitial))
    _ = ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
            readout target‖ +
          ‖readout (referenceSolver^[referenceSteps] referenceInitial) -
            readout target‖ := by
      rw [show readout target -
          readout (referenceSolver^[referenceSteps] referenceInitial) =
          -(readout (referenceSolver^[referenceSteps] referenceInitial) -
            readout target) by abel, norm_neg]
    _ ≤ constant *
          ‖candidateSolver^[candidateSteps] candidateInitial - target‖ +
        constant *
          ‖referenceSolver^[referenceSteps] referenceInitial - target‖ :=
      add_le_add (hreadout _) (hreadout _)
    _ ≤ constant *
          (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖) +
        constant *
          (referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcandidate hconstant)
        (mul_le_mul_of_nonneg_left hreference hconstant)
    _ = constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖) := by ring

/-- A registered tolerance admits finite solver substitution whenever the
complete two-solver credit budget fits inside it. -/
theorem finiteSolver_credit_difference_le_tolerance
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ) (tolerance : ℝ)
    (hbudget :
      constant *
          (candidateCertificate.factor ^ candidateSteps *
              ‖candidateInitial - target‖ +
            referenceCertificate.factor ^ referenceSteps *
              ‖referenceInitial - target‖) ≤ tolerance) :
    ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
        readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
      tolerance := by
  exact (finiteSolver_credit_difference_le referenceCertificate
    candidateCertificate target referenceInitial candidateInitial
    referenceFixed candidateFixed readout constant hconstant hreadout
    referenceSteps candidateSteps).trans hbudget

section Alignment

variable [InnerProductSpace ℝ Credit]

/-- If the finite substitution budget is smaller than the observed candidate
credit norm, the candidate remains positively aligned with the reference
finite credit.  This is an observable admission gate, not a claim that the two
finite directions are equal. -/
theorem finiteSolver_positiveAlignment
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ)
    (hrelative :
      constant *
          (candidateCertificate.factor ^ candidateSteps *
              ‖candidateInitial - target‖ +
            referenceCertificate.factor ^ referenceSteps *
              ‖referenceInitial - target‖) <
        ‖readout (candidateSolver^[candidateSteps] candidateInitial)‖) :
    0 < ⟪readout (referenceSolver^[referenceSteps] referenceInitial),
      readout (candidateSolver^[candidateSteps] candidateInitial)⟫_ℝ := by
  let referenceCredit :=
    readout (referenceSolver^[referenceSteps] referenceInitial)
  let candidateCredit :=
    readout (candidateSolver^[candidateSteps] candidateInitial)
  let error := constant *
    (candidateCertificate.factor ^ candidateSteps *
        ‖candidateInitial - target‖ +
      referenceCertificate.factor ^ referenceSteps *
        ‖referenceInitial - target‖)
  have herror : ‖candidateCredit - referenceCredit‖ ≤ error := by
    simpa [candidateCredit, referenceCredit, error] using
      finiteSolver_credit_difference_le referenceCertificate
        candidateCertificate target referenceInitial candidateInitial
        referenceFixed candidateFixed readout constant hconstant hreadout
        referenceSteps candidateSteps
  exact finiteCredit_positiveAlignment referenceCredit candidateCredit error
    herror (by simpa [candidateCredit, error] using hrelative)

end Alignment

/-! ## Exact block-quadratic finite-depth formulas -/

variable {n : ℕ}

/-- Iterate closed form for blockwise rates. -/
theorem blockStep_iterate_error
    (curvature target rates state : Fin n → ℝ) {i : Fin n}
    (hcurv : curvature i ≠ 0) (steps : ℕ) :
    (blockStep curvature target rates)^[steps] state i -
        equilibrium curvature target i =
      (1 - rates i * curvature i) ^ steps *
        (state i - equilibrium curvature target i) := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply',
        blockStep_error curvature target rates _ hcurv,
        inductionHypothesis, pow_succ]
      ring

/-- Iterate closed form for the damped block step. -/
theorem dampedStep_iterate_error
    (curvature target : Fin n → ℝ) (damping : ℝ)
    (state : Fin n → ℝ) {i : Fin n}
    (hcurv : curvature i ≠ 0) (hdenom : curvature i + damping ≠ 0)
    (steps : ℕ) :
    (dampedStep curvature target damping)^[steps] state i -
        equilibrium curvature target i =
      (damping / (curvature i + damping)) ^ steps *
        (state i - equilibrium curvature target i) := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply',
        dampedStep_error curvature target damping _ hcurv hdenom,
        inductionHypothesis, pow_succ]
      ring

/-- Exact finite-depth state difference between a global-rate solve and a
damped solve from the same initializer. -/
theorem global_damped_iterate_difference
    (curvature target : Fin n → ℝ) (rate damping : ℝ)
    (state : Fin n → ℝ) {i : Fin n}
    (hcurv : curvature i ≠ 0) (hdenom : curvature i + damping ≠ 0)
    (steps : ℕ) :
    (globalStep curvature target rate)^[steps] state i -
        (dampedStep curvature target damping)^[steps] state i =
      ((1 - rate * curvature i) ^ steps -
          (damping / (curvature i + damping)) ^ steps) *
        (state i - equilibrium curvature target i) := by
  calc
    (globalStep curvature target rate)^[steps] state i -
        (dampedStep curvature target damping)^[steps] state i =
      ((globalStep curvature target rate)^[steps] state i -
          equilibrium curvature target i) -
        ((dampedStep curvature target damping)^[steps] state i -
          equilibrium curvature target i) := by ring
    _ = (1 - rate * curvature i) ^ steps *
          (state i - equilibrium curvature target i) -
        (damping / (curvature i + damping)) ^ steps *
          (state i - equilibrium curvature target i) := by
      rw [globalStep_iterate_error curvature target rate state hcurv,
        dampedStep_iterate_error curvature target damping state hcurv hdenom]
    _ = ((1 - rate * curvature i) ^ steps -
          (damping / (curvature i + damping)) ^ steps) *
        (state i - equilibrium curvature target i) := by ring

/-- Exact warm-versus-cold dependence of the damped block solver. -/
theorem damped_warmStart_iterate_difference
    (curvature target : Fin n → ℝ) (damping : ℝ)
    (warm cold : Fin n → ℝ) {i : Fin n}
    (hcurv : curvature i ≠ 0) (hdenom : curvature i + damping ≠ 0)
    (steps : ℕ) :
    (dampedStep curvature target damping)^[steps] warm i -
        (dampedStep curvature target damping)^[steps] cold i =
      (damping / (curvature i + damping)) ^ steps *
        (warm i - cold i) := by
  have hwarm := dampedStep_iterate_error curvature target damping warm
    hcurv hdenom steps
  have hcold := dampedStep_iterate_error curvature target damping cold
    hcurv hdenom steps
  linarith

/-- A coordinatewise linear credit readout. -/
def coordinateCredit {n : ℕ}
    (weight state : Fin n → ℝ) (i : Fin n) : ℝ :=
  weight i * state i

/-- Exact finite-depth credit difference for global versus damped settling.
The credit weight and initializer displacement remain explicit. -/
theorem coordinateCredit_global_damped_difference
    (curvature target weight : Fin n → ℝ) (rate damping : ℝ)
    (state : Fin n → ℝ) {i : Fin n}
    (hcurv : curvature i ≠ 0) (hdenom : curvature i + damping ≠ 0)
    (steps : ℕ) :
    coordinateCredit weight
          ((globalStep curvature target rate)^[steps] state) i -
        coordinateCredit weight
          ((dampedStep curvature target damping)^[steps] state) i =
      weight i *
        (((1 - rate * curvature i) ^ steps -
            (damping / (curvature i + damping)) ^ steps) *
          (state i - equilibrium curvature target i)) := by
  simp only [coordinateCredit]
  rw [← mul_sub]
  rw [global_damped_iterate_difference curvature target rate damping state
    hcurv hdenom steps]

/-! ## Positive and negative executable boundaries -/

def identityCreditReadout (state : ℝ) : ℝ := state

theorem identityCreditReadout_pairwiseLipschitz :
    CreditReadoutPairwiseLipschitz identityCreditReadout 1 := by
  intro left right
  simp [identityCreditReadout]

/-- The generic warm-start theorem specializes to the half-contraction with
no slack in the declared geometric factor. -/
theorem halfSolver_warmStart_credit_difference_le
    (warm cold : ℝ) (steps : ℕ) :
    |identityCreditReadout (halfSolver^[steps] warm) -
        identityCreditReadout (halfSolver^[steps] cold)| ≤
      (1 / 2 : ℝ) ^ steps * |warm - cold| := by
  simpa [Real.norm_eq_abs, halfSolverCertificate, identityCreditReadout] using
    warmStart_credit_difference_le halfSolverCertificate
      identityCreditReadout 1 (by norm_num)
      identityCreditReadout_pairwiseLipschitz warm cold steps

/-- Starting at distance one instead of two saves one half-solver sweep in
the certified identity-credit budget, at every retained depth. -/
theorem halfSolver_one_step_warmStart_saving (steps : ℕ) :
    |identityCreditReadout (halfSolver^[steps] (1 : ℝ)) -
        identityCreditReadout 0| ≤
      (1 : ℝ) *
        ((1 / 2 : ℝ) ^ (steps + 1) * |(2 : ℝ) - 0|) := by
  have hcloser : |(1 : ℝ) - 0| ≤
      (1 / 2 : ℝ) ^ 1 * |(2 : ℝ) - 0| := by norm_num
  simpa [Real.norm_eq_abs, halfSolverCertificate, identityCreditReadout] using
    warmInitializer_savesSteps_creditBudget halfSolverCertificate
      0 (1 : ℝ) (2 : ℝ) halfSolver_zero_fixed identityCreditReadout
      1 (by norm_num)
      (pairwiseLipschitz_to_lipschitzAt identityCreditReadout 1
        identityCreditReadout_pairwiseLipschitz 0)
      steps 1 hcloser

def quarterSolver (state : ℝ) : ℝ := state / 4

/-- Half and quarter contraction have exactly the same stationary set. -/
theorem halfSolver_fixed_iff_quarterSolver_fixed (state : ℝ) :
    halfSolver state = state ↔ quarterSolver state = state := by
  simp [halfSolver, quarterSolver]
  constructor <;> intro h <;> linarith

/-- Nevertheless their one-step finite credits differ. -/
theorem shared_stationary_set_not_finiteStep_license :
    (∀ state : ℝ,
        halfSolver state = state ↔ quarterSolver state = state) ∧
      identityCreditReadout (halfSolver 1) ≠
        identityCreditReadout (quarterSolver 1) := by
  constructor
  · exact halfSolver_fixed_iff_quarterSolver_fixed
  · norm_num [identityCreditReadout, halfSolver, quarterSolver]

#print axioms pairwiseLipschitz_to_lipschitzAt
#print axioms warmStart_credit_difference_le
#print axioms warmInitializer_savesSteps_geometricBudget
#print axioms warmInitializer_savesSteps_creditBudget
#print axioms localWarmStart_credit_difference_le
#print axioms localFiniteSolver_credit_difference_le
#print axioms finiteSolver_credit_difference_le
#print axioms finiteSolver_credit_difference_le_tolerance
#print axioms finiteSolver_positiveAlignment
#print axioms blockStep_iterate_error
#print axioms dampedStep_iterate_error
#print axioms global_damped_iterate_difference
#print axioms damped_warmStart_iterate_difference
#print axioms coordinateCredit_global_damped_difference
#print axioms halfSolver_warmStart_credit_difference_le
#print axioms halfSolver_one_step_warmStart_saving
#print axioms shared_stationary_set_not_finiteStep_license

end

end FiniteSolverSubstitution

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
