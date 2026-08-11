import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage

/-!
# Guarded finite-solver advantage and net-work accounting

A finite warm solve is scientifically admissible only if it preserves the
advantage already certified for the authenticated cold finite credit.  It is
an acceleration only if the admitted path remains cheaper after charging
initializer construction, certificate extraction, finite-precision checking,
and audit work.  Rejected warm proposals are safe because they return the cold
credit, but they are not free: they pay both the proposal and cold-reference
costs.

This file composes the finite-solver credit bound with the existing robust
conditional-advantage theory and gives exact accepted, rejected, and batched
work inequalities.  Positive and negative fixtures separate saved sweeps from
saved total work.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace GuardedFiniteAcceleration

open scoped InnerProductSpace
open AmortizedInitialization
open AmortizedCreditReadout
open LocalAmortizedInitialization
open ConditionalCreditAdvantage
open FiniteSolverSubstitution
open FiniteTrajectoryAcceleration
open MinimumInterferenceCredit
open WorkNormalizedTruncation

noncomputable section

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-! ## Preserve the cold finite credit's advantage -/

/-- A candidate inside an explicit norm ball around an authenticated reference
retains the reference's retention-weighted score advantage whenever the error
charge fits strictly inside that advantage margin.  The reference may be a
finite cold solve; it need not be an ideal analytic direction. -/
theorem candidate_score_gt_baseline_of_reference_gap
    (current replay reference candidate baseline : Parameter)
    (retentionWeight error : ℝ)
    (errorBound : ‖candidate - reference‖ ≤ error)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight reference -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight candidate := by
  have lower := retentionWeightedScore_realized_lower current replay
    reference candidate retentionWeight error errorBound
  linarith

/-- A certified lower bound on the reference advantage is sufficient; the
reference score itself need not be recomputed by the admission path. -/
theorem candidate_score_gt_baseline_of_reference_margin
    (current replay reference candidate baseline : Parameter)
    (retentionWeight error margin : ℝ)
    (errorBound : ‖candidate - reference‖ ≤ error)
    (referenceMargin :
      margin ≤
        retentionWeightedScore current replay retentionWeight reference -
          retentionWeightedScore current replay retentionWeight baseline)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error < margin) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight candidate := by
  apply candidate_score_gt_baseline_of_reference_gap current replay reference
    candidate baseline retentionWeight error errorBound
  exact gate.trans_le referenceMargin

/-- The corresponding finite-step guarantee charges both credit displacement
and any change in the directional curvature bound. -/
theorem candidate_decreaseLower_gt_baseline_of_reference_gap
    (current replay reference candidate baseline : Parameter)
    (retentionWeight error step candidateCurvature baselineCurvature : ℝ)
    (errorBound : ‖candidate - reference‖ ≤ error)
    (stepPositive : 0 < step)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error +
          step * (candidateCurvature - baselineCurvature) / 2 <
        retentionWeightedScore current replay retentionWeight reference -
          retentionWeightedScore current replay retentionWeight baseline) :
    directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight baseline)
          baselineCurvature <
      directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight candidate)
          candidateCurvature := by
  have lower := retentionWeightedScore_realized_lower current replay
    reference candidate retentionWeight error errorBound
  unfold directionalDecreaseLower
  have scaled := mul_lt_mul_of_pos_left gate stepPositive
  nlinarith

variable {State : Type*} [NormedAddCommGroup State]

/-- Complete finite-solver composition: the two-solver geometric credit budget
is used directly as the error charge against the authenticated reference
credit's conditional-advantage margin. -/
theorem finiteSolver_preserves_retentionAdvantage
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Parameter) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ)
    (current replay baseline : Parameter) (retentionWeight : ℝ)
    (gate :
      let error := constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖)
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight
            (readout (referenceSolver^[referenceSteps] referenceInitial)) -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (readout (candidateSolver^[candidateSteps] candidateInitial)) := by
  let error := constant *
    (candidateCertificate.factor ^ candidateSteps *
        ‖candidateInitial - target‖ +
      referenceCertificate.factor ^ referenceSteps *
        ‖referenceInitial - target‖)
  have errorBound :
      ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
          readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
        error := by
    simpa [error] using
      finiteSolver_credit_difference_le referenceCertificate
        candidateCertificate target referenceInitial candidateInitial
        referenceFixed candidateFixed readout constant hconstant hreadout
        referenceSteps candidateSteps
  apply candidate_score_gt_baseline_of_reference_gap current replay
    (readout (referenceSolver^[referenceSteps] referenceInitial))
    (readout (candidateSolver^[candidateSteps] candidateInitial)) baseline
    retentionWeight error errorBound
  simpa [error] using gate

/-- The finite-solver displacement budget also preserves the cold reference's
finite-step advantage after charging a possibly different candidate curvature
bound. -/
theorem finiteSolver_preserves_decreaseLowerAdvantage
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Parameter) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ)
    (current replay baseline : Parameter)
    (retentionWeight step candidateCurvature baselineCurvature : ℝ)
    (stepPositive : 0 < step)
    (gate :
      let error := constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖)
      ‖combinedGradient current replay retentionWeight‖ * error +
          step * (candidateCurvature - baselineCurvature) / 2 <
        retentionWeightedScore current replay retentionWeight
            (readout (referenceSolver^[referenceSteps] referenceInitial)) -
          retentionWeightedScore current replay retentionWeight baseline) :
    directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight baseline)
          baselineCurvature <
      directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight
            (readout (candidateSolver^[candidateSteps] candidateInitial)))
          candidateCurvature := by
  let error := constant *
    (candidateCertificate.factor ^ candidateSteps *
        ‖candidateInitial - target‖ +
      referenceCertificate.factor ^ referenceSteps *
        ‖referenceInitial - target‖)
  have errorBound :
      ‖readout (candidateSolver^[candidateSteps] candidateInitial) -
          readout (referenceSolver^[referenceSteps] referenceInitial)‖ ≤
        error := by
    simpa [error] using
      finiteSolver_credit_difference_le referenceCertificate
        candidateCertificate target referenceInitial candidateInitial
        referenceFixed candidateFixed readout constant hconstant hreadout
        referenceSteps candidateSteps
  apply candidate_decreaseLower_gt_baseline_of_reference_gap current replay
    (readout (referenceSolver^[referenceSteps] referenceInitial))
    (readout (candidateSolver^[candidateSteps] candidateInitial)) baseline
    retentionWeight error step candidateCurvature baselineCurvature errorBound
    stepPositive
  simpa [error] using gate

/-! ## Fail-closed credit selection -/

/-- Select the candidate only after its certificate is admitted; rejection
returns the authenticated cold reference exactly. -/
def guardedCredit (admitted : Bool)
    (reference candidate : Parameter) : Parameter :=
  if admitted then candidate else reference

omit [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] in
@[simp] theorem guardedCredit_true (reference candidate : Parameter) :
    guardedCredit true reference candidate = candidate := rfl

omit [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] in
@[simp] theorem guardedCredit_false (reference candidate : Parameter) :
    guardedCredit false reference candidate = reference := rfl

/-- Fail-closed selection preserves an established reference advantage.  On
the admitted branch the candidate must carry its own proof; on rejection the
reference proof is reused without approximation. -/
theorem guardedCredit_retains_referenceAdvantage
    (admitted : Bool)
    (current replay reference candidate baseline : Parameter)
    (retentionWeight : ℝ)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight reference)
    (candidateAdvantage : admitted = true →
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight candidate) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted reference candidate) := by
  cases admitted
  · simpa using referenceAdvantage
  · simpa using candidateAdvantage rfl

/-- A norm-error gate supplies the admitted-branch proof while rejection still
returns the exact reference. -/
theorem guardedCredit_retains_referenceAdvantage_of_errorGate
    (admitted : Bool)
    (current replay reference candidate baseline : Parameter)
    (retentionWeight error : ℝ)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight reference)
    (candidateError : admitted = true →
      ‖candidate - reference‖ ≤ error)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight reference -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted reference candidate) := by
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    reference candidate baseline retentionWeight referenceAdvantage
  intro hadmitted
  exact candidate_score_gt_baseline_of_reference_gap current replay reference
    candidate baseline retentionWeight error (candidateError hadmitted) gate

/-- End-to-end fail-closed finite-solver crown.  Candidate advantage is only
required on the admitted branch; rejection returns the authenticated reference
and uses its already established advantage. -/
theorem guardedFiniteSolver_preserves_retentionAdvantage
    {referenceSolver candidateSolver : State → State}
    (referenceCertificate : ContractionCertificate referenceSolver)
    (candidateCertificate : ContractionCertificate candidateSolver)
    (target referenceInitial candidateInitial : State)
    (referenceFixed : IsFixedPoint referenceSolver target)
    (candidateFixed : IsFixedPoint candidateSolver target)
    (readout : State → Parameter) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutLipschitzAt readout target constant)
    (referenceSteps candidateSteps : ℕ)
    (current replay baseline : Parameter) (retentionWeight : ℝ)
    (admitted : Bool)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight
          (readout (referenceSolver^[referenceSteps] referenceInitial)))
    (gate : admitted = true →
      let error := constant *
        (candidateCertificate.factor ^ candidateSteps *
            ‖candidateInitial - target‖ +
          referenceCertificate.factor ^ referenceSteps *
            ‖referenceInitial - target‖)
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight
            (readout (referenceSolver^[referenceSteps] referenceInitial)) -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted
          (readout (referenceSolver^[referenceSteps] referenceInitial))
          (readout (candidateSolver^[candidateSteps] candidateInitial))) := by
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    (readout (referenceSolver^[referenceSteps] referenceInitial))
    (readout (candidateSolver^[candidateSteps] candidateInitial)) baseline
    retentionWeight referenceAdvantage
  intro hadmitted
  exact finiteSolver_preserves_retentionAdvantage referenceCertificate
    candidateCertificate target referenceInitial candidateInitial
    referenceFixed candidateFixed readout constant hconstant hreadout
    referenceSteps candidateSteps current replay baseline retentionWeight
    (gate hadmitted)

/-- Runtime-facing finite-trajectory crown.  An admitted realized warm credit
retains the authenticated realized cold credit's advantage after charging the
same-basin finite-depth bound and both replay precision budgets.  Rejection
returns the realized cold credit exactly. -/
theorem guardedLocalWarmShort_preserves_retentionAdvantage
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Parameter) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Parameter)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout (solver^[warmSteps] warm)‖ ≤
        candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized -
          readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
        referencePrecisionError)
    (current replay baseline : Parameter) (retentionWeight : ℝ)
    (admitted : Bool)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate : admitted = true →
      let error := candidatePrecisionError +
        constant *
          (certificate.factor ^ warmSteps *
            (‖warm - cold‖ +
              geometricPrefix certificate.factor omittedSteps *
                ‖cold - solver cold‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted referenceRealized candidateRealized) := by
  let error := candidatePrecisionError +
    constant *
      (certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖)) +
    referencePrecisionError
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    referenceRealized candidateRealized baseline retentionWeight
    referenceAdvantage
  intro hadmitted
  apply candidate_score_gt_baseline_of_reference_gap current replay
    referenceRealized candidateRealized baseline retentionWeight error
  · simpa [error] using
      local_realized_warmShort_credit_difference_to_coldLong_le certificate
        readout constant hconstant hreadout warm cold hwarm hcold
        warmSteps omittedSteps candidateRealized referenceRealized
        candidatePrecisionError referencePrecisionError candidateReplayBound
        referenceReplayBound
  · simpa [error] using gate hadmitted

/-- Work-preserving admitted-path crown.  The warm candidate is compared with
the exact-real finite cold endpoint through a certified reference-advantage
margin, so admission does not execute that cold endpoint.  Rejection remains
fail-closed and uses a separately authenticated cold fallback. -/
theorem guardedLocalWarmShort_withoutAdmittedColdReplay
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (readout : State → Parameter) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hreadout : CreditReadoutPairwiseLipschitz readout constant)
    (warm cold : State)
    (hwarm : InClosedBall center radius warm)
    (hcold : InClosedBall center radius cold)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized coldFallback : Parameter)
    (candidatePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout (solver^[warmSteps] warm)‖ ≤
        candidatePrecisionError)
    (current replay baseline : Parameter) (retentionWeight margin : ℝ)
    (admitted : Bool)
    (fallbackAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight coldFallback)
    (idealColdMargin :
      margin ≤
        retentionWeightedScore current replay retentionWeight
            (readout (solver^[warmSteps + omittedSteps] cold)) -
          retentionWeightedScore current replay retentionWeight baseline)
    (gate : admitted = true →
      let error := candidatePrecisionError +
        constant *
          (certificate.factor ^ warmSteps *
            (‖warm - cold‖ +
              geometricPrefix certificate.factor omittedSteps *
                ‖cold - solver cold‖))
      ‖combinedGradient current replay retentionWeight‖ * error < margin) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted coldFallback candidateRealized) := by
  let error := candidatePrecisionError +
    constant *
      (certificate.factor ^ warmSteps *
        (‖warm - cold‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖))
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    coldFallback candidateRealized baseline retentionWeight fallbackAdvantage
  intro hadmitted
  apply candidate_score_gt_baseline_of_reference_margin current replay
    (readout (solver^[warmSteps + omittedSteps] cold)) candidateRealized
    baseline retentionWeight error margin
  · simpa [error] using
      local_realized_warmShort_credit_to_idealColdLong_le certificate
        readout constant hconstant hreadout warm cold hwarm hcold
        warmSteps omittedSteps candidateRealized candidatePrecisionError
        candidateReplayBound
  · exact idealColdMargin
  · simpa [error] using gate hadmitted

/-! ## Total-work accounting -/

/-- Every incremental cost charged to a guarded warm-start attempt.  Common
training work that is identical in both arms may be added outside this record;
it cancels in the comparison. -/
structure GuardedWorkProfile where
  initializerWork : ℕ
  certificateWork : ℕ
  finitePrecisionWork : ℕ
  auditWork : ℕ
  sweepWork : ℕ
  warmDepth : ℕ
  coldFixedWork : ℕ
  coldDepth : ℕ

/-- Lookup, certification, finite-precision, and audit overhead paid whether
the candidate is eventually admitted or rejected. -/
def GuardedWorkProfile.overhead (profile : GuardedWorkProfile) : ℕ :=
  profile.initializerWork + profile.certificateWork +
    profile.finitePrecisionWork + profile.auditWork

/-- Cost of constructing and settling one warm proposal. -/
def GuardedWorkProfile.proposalWork (profile : GuardedWorkProfile) : ℕ :=
  profile.overhead + profile.sweepWork * profile.warmDepth

/-- Cost of the cold reference path by itself. -/
def GuardedWorkProfile.coldWork (profile : GuardedWorkProfile) : ℕ :=
  profile.coldFixedWork + profile.sweepWork * profile.coldDepth

/-- Exact incremental cost of the fail-closed path.  A rejected proposal pays
for both the proposal and the cold reference that replaces it. -/
def GuardedWorkProfile.guardedWork
    (profile : GuardedWorkProfile) (admitted : Bool) : ℕ :=
  profile.proposalWork + if admitted then 0 else profile.coldWork

/-- On acceptance, net acceleration is exactly total proposal work being less
than cold work; saved sweeps alone are insufficient. -/
theorem admitted_guardedWork_lt_coldWork_iff
    (profile : GuardedWorkProfile) :
    profile.guardedWork true < profile.coldWork ↔
      profile.overhead + profile.sweepWork * profile.warmDepth <
        profile.coldFixedWork + profile.sweepWork * profile.coldDepth := by
  rfl

/-- A rejected warm proposal is fail-closed scientifically but cannot be a
per-attempt acceleration: it contains the complete cold work plus proposal
work. -/
theorem rejected_guardedWork_not_lt_coldWork
    (profile : GuardedWorkProfile) :
    ¬ profile.guardedWork false < profile.coldWork := by
  simp only [GuardedWorkProfile.guardedWork, Bool.false_eq_true, ↓reduceIte]
  omega

/-- Exact incremental work for a batch with declared admitted and rejected
proposal counts. -/
def GuardedWorkProfile.batchGuardedWork
    (profile : GuardedWorkProfile) (admitted rejected : ℕ) : ℕ :=
  (admitted + rejected) * profile.proposalWork +
    rejected * profile.coldWork

/-- Cold-only work for the same number of updates. -/
def GuardedWorkProfile.batchColdWork
    (profile : GuardedWorkProfile) (admitted rejected : ℕ) : ℕ :=
  (admitted + rejected) * profile.coldWork

/-- Batch acceleration has a sharp acceptance/work threshold: all proposals
are charged, while only admitted proposals can replace cold work. -/
theorem batchGuardedWork_lt_coldWork_iff
    (profile : GuardedWorkProfile) (admitted rejected : ℕ) :
    profile.batchGuardedWork admitted rejected <
        profile.batchColdWork admitted rejected ↔
      (admitted + rejected) * profile.proposalWork <
        admitted * profile.coldWork := by
  unfold GuardedWorkProfile.batchGuardedWork
    GuardedWorkProfile.batchColdWork
  rw [add_mul, add_mul]
  omega

/-! ## Positive and negative executable work boundaries -/

def economicalProfile : GuardedWorkProfile where
  initializerWork := 1
  certificateWork := 1
  finitePrecisionWork := 0
  auditWork := 0
  sweepWork := 1
  warmDepth := 4
  coldFixedWork := 0
  coldDepth := 8

def expensiveCertificateProfile : GuardedWorkProfile where
  initializerWork := 2
  certificateWork := 2
  finitePrecisionWork := 1
  auditWork := 0
  sweepWork := 1
  warmDepth := 4
  coldFixedWork := 0
  coldDepth := 8

/-- Four saved sweeps remain a genuine total-work saving when all overhead is
only two work units. -/
theorem economicalProfile_admitted_saves_totalWork :
    economicalProfile.guardedWork true < economicalProfile.coldWork := by
  norm_num [GuardedWorkProfile.guardedWork, GuardedWorkProfile.proposalWork,
    GuardedWorkProfile.overhead, GuardedWorkProfile.coldWork,
    economicalProfile]

/-- The same four saved sweeps are not an acceleration when certification and
checking cost five work units. -/
theorem expensiveCertificate_erases_sweep_saving :
    expensiveCertificateProfile.coldWork <
      expensiveCertificateProfile.guardedWork true := by
  norm_num [GuardedWorkProfile.guardedWork, GuardedWorkProfile.proposalWork,
    GuardedWorkProfile.overhead, GuardedWorkProfile.coldWork,
    expensiveCertificateProfile]

/-- With the economical profile, four admissions and one rejection still
beat five cold solves.  Three admissions and one rejection would only break
even, so the inequality is strict at the exact acceptance threshold. -/
theorem fourAdmissions_oneRejection_save_batchWork :
    economicalProfile.batchGuardedWork 4 1 <
      economicalProfile.batchColdWork 4 1 := by
  norm_num [GuardedWorkProfile.batchGuardedWork,
    GuardedWorkProfile.batchColdWork, GuardedWorkProfile.proposalWork,
    GuardedWorkProfile.overhead, GuardedWorkProfile.coldWork,
    economicalProfile]

/-- Three admissions and one rejection are the exact break-even point for the
economical fixture. -/
theorem threeAdmissions_oneRejection_break_even :
    economicalProfile.batchGuardedWork 3 1 =
      economicalProfile.batchColdWork 3 1 := by
  norm_num [GuardedWorkProfile.batchGuardedWork,
    GuardedWorkProfile.batchColdWork, GuardedWorkProfile.proposalWork,
    GuardedWorkProfile.overhead, GuardedWorkProfile.coldWork,
    economicalProfile]

/-- At the same proposal cost, two admissions and two rejections cost more
than four cold solves. -/
theorem twoAdmissions_twoRejections_erase_batchSaving :
    economicalProfile.batchColdWork 2 2 <
      economicalProfile.batchGuardedWork 2 2 := by
  norm_num [GuardedWorkProfile.batchGuardedWork,
    GuardedWorkProfile.batchColdWork, GuardedWorkProfile.proposalWork,
    GuardedWorkProfile.overhead, GuardedWorkProfile.coldWork,
    economicalProfile]

#print axioms candidate_score_gt_baseline_of_reference_gap
#print axioms candidate_score_gt_baseline_of_reference_margin
#print axioms candidate_decreaseLower_gt_baseline_of_reference_gap
#print axioms finiteSolver_preserves_retentionAdvantage
#print axioms finiteSolver_preserves_decreaseLowerAdvantage
#print axioms guardedCredit_retains_referenceAdvantage
#print axioms guardedCredit_retains_referenceAdvantage_of_errorGate
#print axioms guardedFiniteSolver_preserves_retentionAdvantage
#print axioms guardedLocalWarmShort_preserves_retentionAdvantage
#print axioms guardedLocalWarmShort_withoutAdmittedColdReplay
#print axioms admitted_guardedWork_lt_coldWork_iff
#print axioms rejected_guardedWork_not_lt_coldWork
#print axioms batchGuardedWork_lt_coldWork_iff
#print axioms economicalProfile_admitted_saves_totalWork
#print axioms expensiveCertificate_erases_sweep_saving
#print axioms fourAdmissions_oneRejection_save_batchWork
#print axioms threeAdmissions_oneRejection_break_even
#print axioms twoAdmissions_twoRejections_erase_batchSaving

end

end GuardedFiniteAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
