import Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine

/-!
# Complete bounded certificate-replay control for M0GC

This module exposes the complete decoded-certificate checker as a deterministic
small-step control machine:

1. validate the profile/source identities and materialize terms;
2. replay proof records chronologically through an explicitly bounded store;
3. pin the last proof result to the declared goal and observe the submitted
   claim.

The terminal result is proved exactly equal to the connected source-level
certificate checker, and therefore inherits its source-calculus soundness.

Maturity boundary: this is a fully connected intermediate proof of concept.
The control flow, capacity check, and logical observations are genuine, but
term materialization and proof storage still use persistent Lean arrays.
Preparation and final observation are atomic transitions.  This is not yet an
optimized ABI, mutable target-addressed store, generated C/Pancake/Clight
program, verified object code, OS, or hardware model.  Later backends must
refine this machine without weakening its observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

abbrev ReplayConfiguration :=
  Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.ReplayConfiguration

abbrev ProofStore :=
  Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.ProofStore

abbrev boundedReplayRecord? :=
  Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayRecord?

abbrev boundedReplayLoop :=
  Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayLoop

/-! ## Complete checker machine -/

/-- Parameters fixed throughout one complete decoded-certificate check. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  certificate : Certificate
  replayFuel : Nat
  submitted : Pattern

/-- The record-replay configuration after term materialization. -/
def replayConfiguration (configuration : Configuration)
    (terms : TermState) : ReplayConfiguration :=
  { profile := configuration.profile
    tables := configuration.tables
    certificate := configuration.certificate
    terms
    replayFuel := configuration.replayFuel }

/-- Allocate exactly one proof-record slot for every encoded proof record. -/
def initialStore (configuration : Configuration) : ProofStore :=
  { capacity := configuration.certificate.proofs.length
    admitted := {} }

/-- Interpret an optional admitted prefix as the final Boolean observation. -/
def observeReplayResult (configuration : Configuration) (terms : TermState) :
    Option CProofPrefixState → Bool
  | none => false
  | some proofs =>
      cCoreObserveFinal configuration.submitted configuration.certificate
        terms proofs

/-- A complete checker state makes preparation, replay, and finalization
explicit.  Rejection and acceptance are both terminal Boolean observations. -/
inductive ControlState where
  | prepare
  | replay (terms : TermState) (remaining : List ProofNode)
      (store : ProofStore)
  | finalize (terms : TermState) (store : ProofStore)
  | halt (accepted : Bool)
deriving Repr

/-- Terminal observations are unavailable before the machine halts. -/
def observe : ControlState → Option Bool
  | .halt accepted => some accepted
  | _ => none

/-- One complete-checker transition.  Every replay transition checks at most
one record and performs at most one admitted-prefix append. -/
def step (configuration : Configuration) : ControlState → ControlState
  | .prepare =>
      match cCorePrepare? configuration.profile configuration.certificate with
      | none => .halt false
      | some terms =>
          .replay terms configuration.certificate.proofs
            (initialStore configuration)
  | .replay terms [] store => .finalize terms store
  | .replay terms (proof :: proofs) store =>
      match boundedReplayRecord?
          (replayConfiguration configuration terms) store proof with
      | none => .halt false
      | some next => .replay terms proofs next
  | .finalize terms store =>
      .halt
        (cCoreObserveFinal configuration.submitted configuration.certificate
          terms store.admitted)
  | .halt accepted => .halt accepted

/-- Relational presentation used by later backend simulations. -/
def Transition (configuration : Configuration)
    (before after : ControlState) : Prop :=
  step configuration before = after

theorem transition_deterministic
    (configuration : Configuration)
    {before afterLeft afterRight : ControlState}
    (left : Transition configuration before afterLeft)
    (right : Transition configuration before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (configuration : Configuration)
    (accepted : Bool) :
    step configuration (.halt accepted) = .halt accepted := rfl

/-- Execute a fixed number of complete-checker transitions. -/
def runSteps (configuration : Configuration) :
    Nat → ControlState → ControlState
  | 0, state => state
  | fuel + 1, state =>
      runSteps configuration fuel (step configuration state)

@[simp] theorem runSteps_halt (configuration : Configuration)
    (fuel : Nat) (accepted : Bool) :
    runSteps configuration fuel (.halt accepted) = .halt accepted := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [runSteps, inductionHypothesis]

/-! ## Exact terminal behavior -/

/-- The recursive bounded replay viewed through the complete checker's final
observation. -/
def referenceCheck (configuration : Configuration) : Bool :=
  match cCorePrepare? configuration.profile configuration.certificate with
  | none => false
  | some terms =>
      observeReplayResult configuration terms
        (Option.map
          Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.ProofStore.admitted
          (boundedReplayLoop (replayConfiguration configuration terms)
            configuration.certificate.proofs (initialStore configuration)))

/-- The exact-size initial store has sufficient capacity for the complete
encoded proof list. -/
theorem initialStore_has_capacity (configuration : Configuration) :
    (initialStore configuration).admitted.processed.size +
        configuration.certificate.proofs.length ≤
      (initialStore configuration).capacity := by
  simp [initialStore]

/-- Starting at replay, one transition per record plus the empty-list and
finalization transitions reaches exactly the recursive bounded observation. -/
theorem runSteps_replay_sufficient (configuration : Configuration)
    (terms : TermState) (proofs : List ProofNode)
    (store : ProofStore) :
    runSteps configuration (proofs.length + 2)
        (.replay terms proofs store) =
      .halt
        (observeReplayResult configuration terms
          (Option.map
            Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.ProofStore.admitted
            (boundedReplayLoop (replayConfiguration configuration terms)
              proofs store))) := by
  induction proofs generalizing store with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      cases recordResult :
          boundedReplayRecord?
            (replayConfiguration configuration terms) store proof with
      | none =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          simp [boundedReplayLoop,
            Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayLoop,
            recordResult, observeReplayResult]
      | some next =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          rw [inductionHypothesis next]
          simp [boundedReplayLoop,
            Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayLoop,
            recordResult]

/-- Preparation plus the statically sufficient replay budget reaches the
recursive complete-check result. -/
theorem runSteps_sufficient (configuration : Configuration) :
    runSteps configuration
        (configuration.certificate.proofs.length + 3) .prepare =
      .halt (referenceCheck configuration) := by
  unfold referenceCheck
  cases prepared :
      cCorePrepare? configuration.profile configuration.certificate with
  | none =>
      rw [show configuration.certificate.proofs.length + 3 =
        (configuration.certificate.proofs.length + 2) + 1 by omega]
      rw [runSteps, step, prepared]
      simp
  | some terms =>
      rw [show configuration.certificate.proofs.length + 3 =
        (configuration.certificate.proofs.length + 2) + 1 by omega]
      rw [runSteps, step, prepared]
      exact runSteps_replay_sufficient configuration terms
        configuration.certificate.proofs (initialStore configuration)

/-- Execute the statically sufficient complete-checker budget. -/
def execute (configuration : Configuration) : Bool :=
  match runSteps configuration
      (configuration.certificate.proofs.length + 3) .prepare with
  | .halt accepted => accepted
  | _ => false

theorem execute_eq_referenceCheck (configuration : Configuration) :
    execute configuration = referenceCheck configuration := by
  unfold execute
  rw [runSteps_sufficient]

/-- The bounded complete machine has exactly the same Boolean behavior as the
unbounded connected proof-prefix checker. -/
theorem referenceCheck_eq_cCoreCheckCertificate
    (configuration : Configuration) :
    referenceCheck configuration =
      cCoreCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificate := by
  rw [cCoreCheckCertificate_eq_pipeline]
  unfold referenceCheck
  cases cCorePrepare? configuration.profile configuration.certificate with
  | none => rfl
  | some terms =>
      change
        observeReplayResult configuration terms
            (Option.map
              Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.ProofStore.admitted
              (Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayLoop
                (replayConfiguration configuration terms)
                configuration.certificate.proofs
                (initialStore configuration))) =
          observeReplayResult configuration terms
            (cCoreReplayLoop configuration.profile configuration.tables
              configuration.certificate terms configuration.replayFuel
              configuration.certificate.proofs {})
      rw [Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine.replayLoop_refines_of_capacity
        (replayConfiguration configuration terms)
        configuration.certificate.proofs (initialStore configuration)
        (initialStore_has_capacity configuration)]
      rfl

/-- Main exactness theorem for the complete bounded replay machine. -/
theorem execute_eq_cCoreCheckCertificate (configuration : Configuration) :
    execute configuration =
      cCoreCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificate := by
  rw [execute_eq_referenceCheck, referenceCheck_eq_cCoreCheckCertificate]

/-- A connected generated profile makes acceptance by the complete bounded
machine sound for the independently validated source calculus. -/
theorem execute_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {certificate : Certificate}
    (accepted :
      execute
        { profile := candidate.physical.profile
          tables := candidate.physical.tables
          certificate
          replayFuel := candidate.decodeFuel
          submitted } = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  exact cCoreCheckCertificate_sound connected
    ((execute_eq_cCoreCheckCertificate
      ({ profile := candidate.physical.profile
         tables := candidate.physical.tables
         certificate
         replayFuel := candidate.decodeFuel
         submitted } : Configuration)).symm.trans accepted)

/-! ## Positive and negative discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def pairConfiguration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    certificate
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel
    submitted := M0GCLogicalReplayCanary.pair }

/-- Positive discriminator: the complete bounded machine accepts the
nontrivial pair-constructor certificate. -/
theorem pair_certificate_accepts :
    execute pairConfiguration = true := by
  rw [execute_eq_cCoreCheckCertificate]
  exact M0GCCoreLoopCorrespondence.Canary.pair_core_checker_accepts

/-- Negative observation discriminator: the same valid certificate does not
prove a different submitted claim. -/
theorem wrong_submitted_claim_rejected :
    execute
        { pairConfiguration with
          submitted := M0GCLogicalReplayCanary.left } = false := by
  rw [execute_eq_cCoreCheckCertificate]
  change
    cCoreCheckCertificate profile M0GCCoreLoopCorrespondence.Canary.tables
      M0GCCoreLoopCorrespondence.Canary.canaryFuel
      M0GCLogicalReplayCanary.left certificate = false
  unfold cCoreCheckCertificate
  rw [M0GCCoreLoopCorrespondence.Canary.pair_core_replay_accepts]
  rfl

def futureReferenceConfiguration : Configuration :=
  { pairConfiguration with
    profile := futurePremiseProfile
    certificate := futurePremiseCertificate }

/-- Negative chronology discriminator: even the complete machine rejects a
record that cites its own not-yet-admitted result. -/
theorem current_proof_reference_rejected :
    execute futureReferenceConfiguration = false := by
  rw [execute_eq_cCoreCheckCertificate]
  change
    cCoreCheckCertificate futurePremiseProfile
      M0GCCoreLoopCorrespondence.Canary.tables
      M0GCCoreLoopCorrespondence.Canary.canaryFuel
      M0GCLogicalReplayCanary.pair futurePremiseCertificate = false
  rw [cCoreCheckCertificate_eq_pipeline]
  unfold cCorePrepare?
  rw [if_pos (by simp [futurePremiseProfile, profile, profileDigest,
    digestWidth])]
  rw [if_pos (by simp [futurePremiseProfile, profile, sourceDigest,
    digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  have futureTerms :
      materializeTerms? futurePremiseProfile futurePremiseCertificate =
        some termState := by
    change materializeTermsLoop futurePremiseProfile [0, 1]
      [leftNode, rightNode, pairNode] {} = some termState
    rw [materializeTermsLoop_congr_symbols
      (left := futurePremiseProfile) (right := profile) (by rfl)]
    simpa [materializeTerms?, certificate] using terms_materialize
  rw [futureTerms]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show termState.patterns[futurePremiseCertificate.goalTerm.toNat]? =
      some M0GCLogicalReplayCanary.pair by rfl]
  dsimp
  rw [M0GCCoreLoopCorrespondence.Canary.current_proof_reference_rejected]

end Canary

#print axioms transition_deterministic
#print axioms initialStore_has_capacity
#print axioms runSteps_replay_sufficient
#print axioms runSteps_sufficient
#print axioms execute_eq_cCoreCheckCertificate
#print axioms execute_sound
#print axioms Canary.pair_certificate_accepts
#print axioms Canary.wrong_submitted_claim_rejected
#print axioms Canary.current_proof_reference_rejected

end Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine
