import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfinite

/-!
# Canaries for finite evidence of infinitary behaviour

The positive fixture is a three-state proof-stream controller.  It emits an
accepted checkpoint, performs two locally legal reasoning steps, and returns
to the checkpoint.  A finite rank assignment proves that every controlled
execution returns to the accepting state beyond every finite prefix.

The negative fixtures separate the two checker layers:

* a controller with a real transition graph but a constant rank passes local
  replay and fails global progress;
* a controller selecting a nonexistent edge fails local replay regardless of
  its ranks;
* an otherwise valid certificate naming the wrong semantic authority is
  rejected before its payload is considered.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.UltrainfiniteCanary

open Mettapedia.GSLT.LanguageDef.CertificateGSLT

inductive DemoState where
  | checkpoint
  | search
  | prove
deriving Repr, DecidableEq

instance : Fintype DemoState :=
  Fintype.ofList [.checkpoint, .search, .prove] (by
    intro state
    cases state <;> simp)

inductive DemoAction where
  | advance
  | progress
deriving Repr, DecidableEq

/-- The only accepting state is the emitted checkpoint. -/
def demoSystem : LabeledSystem DemoState DemoAction where
  step source action target :=
    match source, action, target with
    | .checkpoint, .advance, .search => true
    | .search, .progress, .prove => true
    | .prove, .progress, .checkpoint => true
    | _, _, _ => false
  accepting state :=
    match state with
    | .checkpoint => true
    | _ => false

/-- The controller follows the three-state proof-production loop. -/
def goodController : MemorylessController DemoState DemoAction where
  active _ := true
  action state :=
    match state with
    | .checkpoint => .advance
    | .search => .progress
    | .prove => .progress
  next state :=
    match state with
    | .checkpoint => .search
    | .search => .prove
    | .prove => .checkpoint

/-- The distance to the next emitted checkpoint. -/
def goodMeasure : ProgressMeasure DemoState where
  rank state :=
    match state with
    | .checkpoint => 0
    | .search => 2
    | .prove => 1

theorem good_local_check :
    goodController.checkLocal demoSystem .checkpoint = true := by
  decide

theorem good_global_check :
    goodMeasure.checkGlobal demoSystem goodController = true := by
  decide

theorem good_certificate_check :
    goodMeasure.check demoSystem goodController .checkpoint = true := by
  decide

/-- The finite controller and its three ranks license the infinite recurrence
claim for every execution following the controller. -/
theorem good_controller_buchi :
    goodController.BuchiWinning demoSystem .checkpoint := by
  apply ProgressMeasure.buchi_sound (measure := goodMeasure)
  exact (ProgressMeasure.check_eq_true_iff demoSystem goodController
    goodMeasure .checkpoint).mp good_certificate_check

def goodExecution : ControlledExecution goodController .checkpoint :=
  goodController.canonicalExecution .checkpoint

theorem good_execution_returns_at_three :
    demoSystem.accepting (goodExecution.state 3) = true := by
  rfl

theorem good_execution_is_recurrent :
    InfinitelyOftenAccepting demoSystem goodExecution.state :=
  good_controller_buchi goodExecution

/-! ## Local replay without global progress is insufficient -/

/-- A constant rank cannot justify the nonaccepting `search -> prove` step. -/
def constantMeasure : ProgressMeasure DemoState where
  rank _ := 0

theorem constant_rank_still_locally_valid :
    goodController.checkLocal demoSystem .checkpoint = true :=
  good_local_check

theorem constant_rank_fails_global_check :
    constantMeasure.checkGlobal demoSystem goodController = false := by
  decide

theorem constant_rank_certificate_rejected :
    constantMeasure.check demoSystem goodController .checkpoint = false := by
  decide

/-- The same locally valid controller is accepted with one global measure and
rejected with another.  Local replay therefore cannot determine the global
licence. -/
theorem local_and_global_are_independent :
    goodController.checkLocal demoSystem .checkpoint = true ∧
      goodMeasure.checkGlobal demoSystem goodController = true ∧
      constantMeasure.checkGlobal demoSystem goodController = false := by
  exact ⟨good_local_check, good_global_check,
    constant_rank_fails_global_check⟩

/-! ## A global-looking measure cannot repair an illegal local edge -/

/-- This controller asks for `advance` at `search`, where only `progress` is
an authored transition. -/
def badEdgeController : MemorylessController DemoState DemoAction where
  active _ := true
  action state :=
    match state with
    | .checkpoint => .advance
    | .search => .advance
    | .prove => .progress
  next state :=
    match state with
    | .checkpoint => .search
    | .search => .prove
    | .prove => .checkpoint

theorem bad_edge_fails_local_check :
    badEdgeController.checkLocal demoSystem .checkpoint = false := by
  decide

theorem bad_edge_certificate_rejected :
    goodMeasure.check demoSystem badEdgeController .checkpoint = false := by
  decide

/-! ## Authority identity and Prime status -/

def demoAuthority :
    SemanticAuthority String (BuchiControllerClaim DemoState DemoAction) :=
  buchiControllerAuthority "demo-buchi-v1" demoSystem

def goodClaim : BuchiControllerClaim DemoState DemoAction :=
  { root := .checkpoint, controller := goodController }

def goodEnvelope : EvidenceEnvelope String demoAuthority.Certificate :=
  { authority := "demo-buchi-v1", certificate := goodMeasure }

theorem good_envelope_accepted :
    demoAuthority.checkEnvelope goodClaim goodEnvelope = true := by
  apply (demoAuthority.checkEnvelope_eq_true_iff goodClaim goodEnvelope).2
  constructor
  · rfl
  · exact good_certificate_check

theorem good_envelope_sound : demoAuthority.Meaning goodClaim :=
  demoAuthority.envelope_sound good_envelope_accepted

def wrongEnvelope : EvidenceEnvelope String demoAuthority.Certificate :=
  { authority := "different-semantics-v2", certificate := goodMeasure }

theorem wrong_envelope_rejected :
    demoAuthority.checkEnvelope goodClaim wrongEnvelope = false := by
  exact demoAuthority.wrong_authority_rejected goodClaim goodMeasure (by
    decide)

/-- Prime may move an attempt from running to exhausted and change its score;
neither action changes the evidential verdict. -/
def attempt (status : OperationalStatus) (score : Nat) :
    EvidenceAttempt demoAuthority Nat :=
  { claim := goodClaim
    evidence := some goodEnvelope
    operational := status
    score := score }

theorem operational_and_score_changes_are_non_authoritative :
    (attempt .running 100).accepted =
      (attempt .resourceExhausted 0).accepted := by
  rfl

theorem exhausted_without_evidence_is_not_acceptance :
    (EvidenceAttempt.accepted
      (authority := demoAuthority)
      { claim := goodClaim
        evidence := none
        operational := .resourceExhausted
        score := 0 }) = false := by
  rfl

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.UltrainfiniteCanary
