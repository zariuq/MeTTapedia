import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteSolverSubstitution

/-!
# Fixed-point-free finite-trajectory acceleration

Predictive-coding training consumes a finite solver trajectory, not an exact
equilibrium.  A warm run stopped before the registered cold depth therefore
needs a comparison with that *finite cold endpoint*.  Introducing an unknown
fixed point into this comparison is unnecessary.

This file derives a posteriori bounds from pairwise contraction alone.  The
short warm trajectory is compared with the longer cold trajectory by splitting
the discrepancy into initializer transport and the cold trajectory's omitted
tail.  The tail is controlled by a finite geometric sum times the observable
first cold residual.  Local versions require both initializers to lie in one
explicit invariant neighborhood, making the same-basin obligation visible.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FiniteTrajectoryAcceleration

open AmortizedInitialization
open LocalAmortizedInitialization
open FiniteSolverSubstitution

noncomputable section

variable {State Credit : Type*}
  [NormedAddCommGroup State] [NormedAddCommGroup Credit]

/-- Finite geometric prefix used to charge an omitted solver tail. -/
def geometricPrefix (factor : ℝ) (steps : ℕ) : ℝ :=
  ∑ index ∈ Finset.range steps, factor ^ index

/-- Under pairwise contraction, displacement after finitely many steps is
bounded by the first observable residual times a finite geometric prefix.
No fixed point is mentioned. -/
theorem iterate_displacement_le_geometricPrefix
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (initial : State) (steps : ℕ) :
    ‖initial - solver^[steps] initial‖ ≤
      geometricPrefix certificate.factor steps * ‖initial - solver initial‖ := by
  induction steps with
  | zero => simp [geometricPrefix]
  | succ steps inductionHypothesis =>
      have hstep :
          ‖solver^[steps] initial - solver^[steps.succ] initial‖ ≤
            certificate.factor ^ steps * ‖initial - solver initial‖ := by
        simpa only [Function.iterate_succ_apply] using
          iterate_initializer_distance_le certificate initial (solver initial) steps
      calc
        ‖initial - solver^[steps.succ] initial‖ ≤
            ‖initial - solver^[steps] initial‖ +
              ‖solver^[steps] initial - solver^[steps.succ] initial‖ := by
          simpa only [sub_add_sub_cancel] using
            norm_add_le
              (initial - solver^[steps] initial)
              (solver^[steps] initial - solver^[steps.succ] initial)
        _ ≤ geometricPrefix certificate.factor steps *
              ‖initial - solver initial‖ +
            certificate.factor ^ steps * ‖initial - solver initial‖ :=
          add_le_add inductionHypothesis hstep
        _ = geometricPrefix certificate.factor steps.succ *
              ‖initial - solver initial‖ := by
          rw [geometricPrefix, geometricPrefix, Finset.sum_range_succ]
          ring

/-- The omitted tail after `prefixSteps` contracts the cold initial residual
by `factor^prefixSteps`; its remaining length is charged by a finite geometric
prefix. -/
theorem iterate_tail_le_firstResidual
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (initial : State) (prefixSteps omittedSteps : ℕ) :
    ‖solver^[prefixSteps] initial -
        solver^[prefixSteps + omittedSteps] initial‖ ≤
      certificate.factor ^ prefixSteps *
        (geometricPrefix certificate.factor omittedSteps *
          ‖initial - solver initial‖) := by
  have htransport := iterate_initializer_distance_le certificate
    initial (solver^[omittedSteps] initial) prefixSteps
  have hdisplacement := iterate_displacement_le_geometricPrefix
    certificate initial omittedSteps
  calc
    ‖solver^[prefixSteps] initial -
        solver^[prefixSteps + omittedSteps] initial‖ =
        ‖solver^[prefixSteps] initial -
          solver^[prefixSteps] (solver^[omittedSteps] initial)‖ := by
      rw [Function.iterate_add_apply]
    _ ≤ certificate.factor ^ prefixSteps *
          ‖initial - solver^[omittedSteps] initial‖ := htransport
    _ ≤ certificate.factor ^ prefixSteps *
          (geometricPrefix certificate.factor omittedSteps *
            ‖initial - solver initial‖) :=
      mul_le_mul_of_nonneg_left hdisplacement
        (pow_nonneg certificate.factor_nonneg prefixSteps)

/-- State-level certificate for replacing a longer cold solve by a shorter
warm solve.  The budget separates warm/cold initializer displacement from the
omitted cold tail. -/
theorem warmShort_state_difference_to_coldLong_le
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (warm cold : State) (warmSteps omittedSteps : ℕ) :
    ‖solver^[warmSteps] warm -
        solver^[warmSteps + omittedSteps] cold‖ ≤
      certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖) := by
  have hinitial := iterate_initializer_distance_le certificate
    warm cold warmSteps
  have htail := iterate_tail_le_firstResidual certificate
    cold warmSteps omittedSteps
  calc
    ‖solver^[warmSteps] warm -
        solver^[warmSteps + omittedSteps] cold‖ ≤
        ‖solver^[warmSteps] warm - solver^[warmSteps] cold‖ +
          ‖solver^[warmSteps] cold -
            solver^[warmSteps + omittedSteps] cold‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (solver^[warmSteps] warm - solver^[warmSteps] cold)
          (solver^[warmSteps] cold -
            solver^[warmSteps + omittedSteps] cold)
    _ ≤ certificate.factor ^ warmSteps * ‖warm - cold‖ +
          certificate.factor ^ warmSteps *
            (geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖) := add_le_add hinitial htail
    _ = certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖) := by ring

/-- Credit-level finite-depth license.  This compares directly with the
registered finite cold credit and requires neither an exact equilibrium nor a
stationarity claim. -/
theorem warmShort_credit_difference_to_coldLong_le
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State) (warmSteps omittedSteps : ℕ) :
    ‖readout (solver^[warmSteps] warm) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
      constant *
        (certificate.factor ^ warmSteps *
          (‖warm - cold‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) := by
  calc
    ‖readout (solver^[warmSteps] warm) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
        constant *
          ‖solver^[warmSteps] warm -
            solver^[warmSteps + omittedSteps] cold‖ := hreadout _ _
    _ ≤ constant *
        (certificate.factor ^ warmSteps *
          (‖warm - cold‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) :=
      mul_le_mul_of_nonneg_left
        (warmShort_state_difference_to_coldLong_le certificate
          warm cold warmSteps omittedSteps)
        hconstant

/-! ## Same-basin nonlinear versions -/

/-- Local displacement bound.  Invariance supplies every intermediate basin
membership needed by pairwise contraction. -/
theorem local_iterate_displacement_le_geometricPrefix
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (initial : State) (hinitial : InClosedBall center radius initial)
    (steps : ℕ) :
    ‖initial - solver^[steps] initial‖ ≤
      geometricPrefix certificate.factor steps * ‖initial - solver initial‖ := by
  induction steps with
  | zero => simp [geometricPrefix]
  | succ steps inductionHypothesis =>
      have hstep :
          ‖solver^[steps] initial - solver^[steps.succ] initial‖ ≤
            certificate.factor ^ steps * ‖initial - solver initial‖ := by
        simpa only [Function.iterate_succ_apply] using
          LocalAmortizedInitialization.iterate_initializer_distance_le
            certificate initial (solver initial) hinitial
            (certificate.maps_ball initial hinitial) steps
      calc
        ‖initial - solver^[steps.succ] initial‖ ≤
            ‖initial - solver^[steps] initial‖ +
              ‖solver^[steps] initial - solver^[steps.succ] initial‖ := by
          simpa only [sub_add_sub_cancel] using
            norm_add_le
              (initial - solver^[steps] initial)
              (solver^[steps] initial - solver^[steps.succ] initial)
        _ ≤ geometricPrefix certificate.factor steps *
              ‖initial - solver initial‖ +
            certificate.factor ^ steps * ‖initial - solver initial‖ :=
          add_le_add inductionHypothesis hstep
        _ = geometricPrefix certificate.factor steps.succ *
              ‖initial - solver initial‖ := by
          rw [geometricPrefix, geometricPrefix, Finset.sum_range_succ]
          ring

/-- Same-basin nonlinear state certificate for a short warm trajectory versus
the registered longer cold trajectory. -/
theorem local_warmShort_state_difference_to_coldLong_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ) :
    ‖solver^[warmSteps] warm -
        solver^[warmSteps + omittedSteps] cold‖ ≤
      certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖) := by
  have hinitial :=
    LocalAmortizedInitialization.iterate_initializer_distance_le
      certificate warm cold hwarm hcold warmSteps
  have hdisplacement := local_iterate_displacement_le_geometricPrefix
    certificate cold hcold omittedSteps
  have hcoldAdvanced :
      InClosedBall center radius (solver^[omittedSteps] cold) :=
    iterate_mem_closedBall certificate cold hcold omittedSteps
  have htailTransport :=
    LocalAmortizedInitialization.iterate_initializer_distance_le
      certificate cold (solver^[omittedSteps] cold) hcold hcoldAdvanced warmSteps
  have htail :
      ‖solver^[warmSteps] cold -
          solver^[warmSteps + omittedSteps] cold‖ ≤
        certificate.factor ^ warmSteps *
          (geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖) := by
    calc
      ‖solver^[warmSteps] cold -
          solver^[warmSteps + omittedSteps] cold‖ =
          ‖solver^[warmSteps] cold -
            solver^[warmSteps] (solver^[omittedSteps] cold)‖ := by
        rw [Function.iterate_add_apply]
      _ ≤ certificate.factor ^ warmSteps *
            ‖cold - solver^[omittedSteps] cold‖ := htailTransport
      _ ≤ certificate.factor ^ warmSteps *
            (geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖) :=
        mul_le_mul_of_nonneg_left hdisplacement
          (pow_nonneg certificate.factor_nonneg warmSteps)
  calc
    ‖solver^[warmSteps] warm -
        solver^[warmSteps + omittedSteps] cold‖ ≤
        ‖solver^[warmSteps] warm - solver^[warmSteps] cold‖ +
          ‖solver^[warmSteps] cold -
            solver^[warmSteps + omittedSteps] cold‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (solver^[warmSteps] warm - solver^[warmSteps] cold)
          (solver^[warmSteps] cold -
            solver^[warmSteps + omittedSteps] cold)
    _ ≤ certificate.factor ^ warmSteps * ‖warm - cold‖ +
          certificate.factor ^ warmSteps *
            (geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖) := add_le_add hinitial htail
    _ = certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖) := by ring

/-- Local credit certificate.  This is the theorem consumed by a nonlinear
Unified-PC warm-start admission gate: same invariant basin, certified `q`,
pairwise readout sensitivity `K`, finite depths, and observable initializer
and first-residual norms. -/
theorem local_warmShort_credit_difference_to_coldLong_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ) :
    ‖readout (solver^[warmSteps] warm) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
      constant *
        (certificate.factor ^ warmSteps *
          (‖warm - cold‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) := by
  calc
    ‖readout (solver^[warmSteps] warm) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
        constant *
          ‖solver^[warmSteps] warm -
            solver^[warmSteps + omittedSteps] cold‖ := hreadout _ _
    _ ≤ constant *
        (certificate.factor ^ warmSteps *
          (‖warm - cold‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) :=
      mul_le_mul_of_nonneg_left
        (local_warmShort_state_difference_to_coldLong_le certificate
          warm cold hwarm hcold warmSteps omittedSteps)
        hconstant

/-! ## Realized finite-precision credit -/

/-- Triangle composition for a mathematically bounded ideal-credit
difference and two independently checked implementation errors.  The two
finite-precision budgets remain separate so that a replay checker can bind
each realized endpoint to its exact-real counterpart. -/
theorem realized_credit_difference_le
    (candidateIdeal referenceIdeal candidateRealized referenceRealized : Credit)
    (trajectoryError candidatePrecisionError referencePrecisionError : ℝ)
    (htrajectory :
      ‖candidateIdeal - referenceIdeal‖ ≤ trajectoryError)
    (hcandidate :
      ‖candidateRealized - candidateIdeal‖ ≤ candidatePrecisionError)
    (hreference :
      ‖referenceRealized - referenceIdeal‖ ≤ referencePrecisionError) :
    ‖candidateRealized - referenceRealized‖ ≤
      candidatePrecisionError + trajectoryError + referencePrecisionError := by
  have hreference' :
      ‖referenceIdeal - referenceRealized‖ ≤ referencePrecisionError := by
    rw [show referenceIdeal - referenceRealized =
      -(referenceRealized - referenceIdeal) by abel, norm_neg]
    exact hreference
  calc
    ‖candidateRealized - referenceRealized‖ ≤
        ‖candidateRealized - candidateIdeal‖ +
          ‖candidateIdeal - referenceRealized‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (candidateRealized - candidateIdeal)
          (candidateIdeal - referenceRealized)
    _ ≤ ‖candidateRealized - candidateIdeal‖ +
          (‖candidateIdeal - referenceIdeal‖ +
            ‖referenceIdeal - referenceRealized‖) := by
      gcongr
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (candidateIdeal - referenceIdeal)
          (referenceIdeal - referenceRealized)
    _ ≤ candidatePrecisionError +
          (trajectoryError + referencePrecisionError) :=
      add_le_add hcandidate (add_le_add htrajectory hreference')
    _ = candidatePrecisionError + trajectoryError +
          referencePrecisionError := by ring

/-- One-sided replay composition used when the exact-real cold endpoint is a
mathematical reference but is deliberately not executed on an admitted warm
path. -/
theorem realized_candidate_to_ideal_reference_le
    (candidateIdeal referenceIdeal candidateRealized : Credit)
    (trajectoryError candidatePrecisionError : ℝ)
    (htrajectory :
      ‖candidateIdeal - referenceIdeal‖ ≤ trajectoryError)
    (hcandidate :
      ‖candidateRealized - candidateIdeal‖ ≤ candidatePrecisionError) :
    ‖candidateRealized - referenceIdeal‖ ≤
      candidatePrecisionError + trajectoryError := by
  calc
    ‖candidateRealized - referenceIdeal‖ ≤
        ‖candidateRealized - candidateIdeal‖ +
          ‖candidateIdeal - referenceIdeal‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          (candidateRealized - candidateIdeal)
          (candidateIdeal - referenceIdeal)
    _ ≤ candidatePrecisionError + trajectoryError :=
      add_le_add hcandidate htrajectory

/-- Complete nonlinear realized-credit budget for a short warm solve versus
the registered longer cold solve.  Mathematical trajectory error and both
finite-precision replay errors are charged explicitly. -/
theorem local_realized_warmShort_credit_difference_to_coldLong_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (hcandidate :
      ‖candidateRealized - readout (solver^[warmSteps] warm)‖ ≤
        candidatePrecisionError)
    (hreference :
      ‖referenceRealized -
          readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
        referencePrecisionError) :
    ‖candidateRealized - referenceRealized‖ ≤
      candidatePrecisionError +
        constant *
          (certificate.factor ^ warmSteps *
            (‖warm - cold‖ +
              geometricPrefix certificate.factor omittedSteps *
                ‖cold - solver cold‖)) +
        referencePrecisionError := by
  apply realized_credit_difference_le
    (readout (solver^[warmSteps] warm))
    (readout (solver^[warmSteps + omittedSteps] cold))
    candidateRealized referenceRealized
    (constant *
      (certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖)))
    candidatePrecisionError referencePrecisionError
  · exact local_warmShort_credit_difference_to_coldLong_le certificate
      readout constant hconstant hreadout warm cold hwarm hcold
      warmSteps omittedSteps
  · exact hcandidate
  · exact hreference

/-- Admitted-path budget against the unexecuted exact-real cold endpoint.
Only the warm endpoint replay error is charged; a rejected path may execute
and validate cold separately. -/
theorem local_realized_warmShort_credit_to_idealColdLong_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Credit) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized : Credit) (candidatePrecisionError : ℝ)
    (hcandidate :
      ‖candidateRealized - readout (solver^[warmSteps] warm)‖ ≤
        candidatePrecisionError) :
    ‖candidateRealized -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
      candidatePrecisionError +
        constant *
          (certificate.factor ^ warmSteps *
            (‖warm - cold‖ +
              geometricPrefix certificate.factor omittedSteps *
                ‖cold - solver cold‖)) := by
  apply realized_candidate_to_ideal_reference_le
    (readout (solver^[warmSteps] warm))
    (readout (solver^[warmSteps + omittedSteps] cold))
    candidateRealized
    (constant *
      (certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖)))
    candidatePrecisionError
  · exact local_warmShort_credit_difference_to_coldLong_le certificate
      readout constant hconstant hreadout warm cold hwarm hcold
      warmSteps omittedSteps
  · exact hcandidate

/-! ## Positive and negative executable boundaries -/

/-- A half-solver warm initializer obtained from one cold step exactly saves
that step: two subsequent warm steps equal three cold steps. -/
theorem halfSolver_warm_twoSteps_eq_cold_threeSteps :
    identityCreditReadout (halfSolver^[2] (1 / 2 : ℝ)) =
      identityCreditReadout (halfSolver^[3] (1 : ℝ)) := by
  norm_num [identityCreditReadout, halfSolver, Function.iterate_succ_apply]

/-- The fixed-point-free finite-trajectory bound specializes to the same
half-solver comparison. -/
theorem halfSolver_warmShort_credit_bound :
    |identityCreditReadout (halfSolver^[2] (1 / 2 : ℝ)) -
        identityCreditReadout (halfSolver^[3] (1 : ℝ))| ≤
      (1 : ℝ) *
        ((1 / 2 : ℝ) ^ 2 *
          (|(1 / 2 : ℝ) - 1| +
            geometricPrefix (1 / 2 : ℝ) 1 * |(1 : ℝ) - halfSolver 1|)) := by
  simpa [Real.norm_eq_abs, halfSolverCertificate] using
    warmShort_credit_difference_to_coldLong_le halfSolverCertificate
      identityCreditReadout 1 (by norm_num)
      identityCreditReadout_pairwiseLipschitz (1 / 2 : ℝ) 1 2 1

def unitDriftSolver (state : ℝ) : ℝ := state + 1

/-- The contraction premise is substantive.  Unit drift preserves pairwise
distance, so no factor strictly below one can certify it. -/
theorem unitDriftSolver_no_contractionCertificate :
    ¬ Nonempty (ContractionCertificate unitDriftSolver) := by
  intro ⟨certificate⟩
  have bound := certificate.contracts (0 : ℝ) 1
  norm_num [unitDriftSolver, Real.norm_eq_abs] at bound
  exact (not_lt_of_ge bound) certificate.factor_lt_one

end

end FiniteTrajectoryAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.iterate_displacement_le_geometricPrefix
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.warmShort_credit_difference_to_coldLong_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.local_warmShort_credit_difference_to_coldLong_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.local_realized_warmShort_credit_difference_to_coldLong_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.local_realized_warmShort_credit_to_idealColdLong_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.halfSolver_warmShort_credit_bound
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration.unitDriftSolver_no_contractionCertificate
