import Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine
import Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

/-!
# Complete addressed certificate checking for M0GC

This module reconnects administrative preparation, fixed-capacity addressed
proof replay, final-result pinning, and submitted-claim observation.  The
complete decoded-certificate machine is proved exactly equal to the qualified
allocation-free native checker whenever its requested result region can be
allocated without unsigned-address wraparound.

Maturity boundary: this is a fully connected intermediate proof of concept.
The result region has checked 64-bit cell addresses and fixed capacity, but
its backing store is still a functional Lean array of typed 32-bit cells.
Preparation and final observation remain atomic.  This is not a byte-packed
ABI, pointer-provenance model, Pancake or Clight program, generated production
C, compiler theorem, object code, OS, or hardware model.  The current table
layout and identifier matcher are not claimed to be endgame optimized.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement.ResultStore
open Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine

/-! ## Complete-checker observations -/

/-- Parameters fixed throughout one complete addressed check.  `resultBase`
selects the requested result-region base independently of the immutable input
certificate representation. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  certificate : Certificate
  replayFuel : Nat
  submitted : Pattern
  resultBase : UInt64

/-- Allocate exactly one fixed result cell per encoded proof record. -/
def initialStore? (configuration : Configuration) : Option ResultStore :=
  ResultStore.allocate? configuration.resultBase
    configuration.certificate.proofs.length

/-- Final observation over the allocation-free source replay state. -/
def nativeObserveFinal (configuration : Configuration) (terms : TermState)
    (state : NativeProofState) : Bool :=
  match state.resultIds[state.resultIds.size - 1]? with
  | none => false
  | some finalResultId =>
      if finalResultId = configuration.certificate.goalTerm then
        match terms.patterns[configuration.certificate.goalTerm.toNat]? with
        | none => false
        | some goal => decide (goal = configuration.submitted)
      else
        false

/-- Final observation through a checked physical read of the last initialized
result cell. -/
def addressedObserveFinal (configuration : Configuration) (terms : TermState)
    (store : ResultStore) : Bool :=
  match store.readAdmitted? (store.used - 1) with
  | none => false
  | some finalResultId =>
      if finalResultId = configuration.certificate.goalTerm then
        match terms.patterns[configuration.certificate.goalTerm.toNat]? with
        | none => false
        | some goal => decide (goal = configuration.submitted)
      else
        false

/-- A well-formed addressed final read is exactly the source-level final
observation. -/
theorem addressedObserveFinal_eq_native (configuration : Configuration)
    (terms : TermState) (store : ResultStore)
    (wellFormed : store.WellFormed) :
    addressedObserveFinal configuration terms store =
      nativeObserveFinal configuration terms store.toNative := by
  unfold addressedObserveFinal nativeObserveFinal
  rw [store.readAdmitted?_eq_snapshot (store.used - 1) wellFormed]
  simp only [ResultStore.toNative]
  rw [store.snapshot_size wellFormed]

/-- Source-level native checking factored through the same preparation,
chronological replay, and final observation used by the addressed machine. -/
def nativePipelineCheck (configuration : Configuration) : Bool :=
  match cCorePrepare? configuration.profile configuration.certificate with
  | none => false
  | some terms =>
      match nativeReplayLoop configuration.profile configuration.tables
          configuration.certificate terms configuration.replayFuel
          configuration.certificate.proofs {} with
      | none => false
      | some state => nativeObserveFinal configuration terms state

theorem nativeCheckCertificate_eq_pipeline (configuration : Configuration) :
    nativeCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificate =
      nativePipelineCheck configuration := by
  unfold nativeCheckCertificate nativeReplay? nativePipelineCheck
    cCorePrepare? nativeObserveFinal
  by_cases profileWidth :
      configuration.profile.profileDigest.length = digestWidth
  · rw [if_pos profileWidth, if_pos profileWidth]
    by_cases sourceWidth :
        configuration.profile.sourceDigest.length = digestWidth
    · rw [if_pos sourceWidth, if_pos sourceWidth]
      by_cases profileMatches :
          configuration.certificate.profileDigest =
            configuration.profile.profileDigest
      · rw [if_pos profileMatches, if_pos profileMatches]
        by_cases sourceMatches :
            configuration.certificate.sourceDigest =
              configuration.profile.sourceDigest
        · rw [if_pos sourceMatches, if_pos sourceMatches]
          cases termsEq :
              materializeTerms? configuration.profile
                configuration.certificate with
          | none => rfl
          | some terms =>
              simp only [Option.bind_eq_bind, Option.bind_some]
              cases goalEq :
                  terms.patterns[
                    configuration.certificate.goalTerm.toNat]? with
              | none => rfl
              | some goal =>
                  simp only [Option.bind_some]
                  cases replayEq :
                      nativeReplayLoop configuration.profile
                        configuration.tables configuration.certificate terms
                        configuration.replayFuel
                        configuration.certificate.proofs {} with
                  | none => rfl
                  | some state =>
                      simp only [Option.bind_some]
                      cases finalEq :
                          state.resultIds[state.resultIds.size - 1]? with
                      | none => rfl
                      | some finalResultId =>
                          simp only [Option.bind_some]
                          by_cases finalMatches :
                              finalResultId =
                                configuration.certificate.goalTerm
                          · rw [if_pos finalMatches, if_pos finalMatches]
                            rfl
                          · rw [if_neg finalMatches, if_neg finalMatches]
        · rw [if_neg sourceMatches, if_neg sourceMatches]
      · rw [if_neg profileMatches, if_neg profileMatches]
    · rw [if_neg sourceWidth, if_neg sourceWidth]
  · rw [if_neg profileWidth, if_neg profileWidth]

/-- Big-step addressed reference.  Allocation failure is an explicit safe
rejection rather than implicit modular wraparound. -/
def referenceCheck (configuration : Configuration) : Bool :=
  match cCorePrepare? configuration.profile configuration.certificate with
  | none => false
  | some terms =>
      match initialStore? configuration with
      | none => false
      | some initial =>
          match M0GCAddressedReplayControlMachine.replayLoop
              configuration.profile configuration.tables
              configuration.certificate terms configuration.replayFuel
              configuration.certificate.proofs initial with
          | none => false
          | some final => addressedObserveFinal configuration terms final

/-- Whenever the requested region is addressable, the complete addressed
reference has exactly the qualified native checker's Boolean behavior. -/
theorem referenceCheck_eq_native_of_allocation
    (configuration : Configuration) (initial : ResultStore)
    (allocated : initialStore? configuration = some initial) :
    referenceCheck configuration =
      nativeCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificate := by
  rw [nativeCheckCertificate_eq_pipeline]
  unfold referenceCheck nativePipelineCheck
  cases prepared :
      cCorePrepare? configuration.profile configuration.certificate with
  | none => rfl
  | some terms =>
      rw [allocated]
      change
        (match M0GCAddressedReplayControlMachine.replayLoop
            configuration.profile configuration.tables
            configuration.certificate terms configuration.replayFuel
            configuration.certificate.proofs initial with
          | none => false
          | some final => addressedObserveFinal configuration terms final) =
        match nativeReplayLoop configuration.profile configuration.tables
            configuration.certificate terms configuration.replayFuel
            configuration.certificate.proofs {} with
        | none => false
        | some state => nativeObserveFinal configuration terms state
      have rawAllocated :
          ResultStore.allocate? configuration.resultBase
              configuration.certificate.proofs.length = some initial := by
        simpa [initialStore?] using allocated
      have wellFormed := ResultStore.allocate?_wellFormed rawAllocated
      have shape := ResultStore.allocate?_shape rawAllocated
      have enough :
          initial.used + configuration.certificate.proofs.length ≤
            initial.cells.size := by
        rcases shape with ⟨_, capacity, used⟩
        rw [used, capacity]
        omega
      have replayEq :=
        M0GCAddressedReplayControlMachine.replayLoop_refines_native_of_capacity
          configuration.profile configuration.tables configuration.certificate
          terms configuration.replayFuel configuration.certificate.proofs
          initial wellFormed enough
      cases addressed :
          M0GCAddressedReplayControlMachine.replayLoop
            configuration.profile configuration.tables
            configuration.certificate terms configuration.replayFuel
            configuration.certificate.proofs initial with
      | none =>
          have mappedRejected :
              (none : Option NativeProofState) =
                nativeReplayLoop configuration.profile configuration.tables
                  configuration.certificate terms configuration.replayFuel
                  configuration.certificate.proofs initial.toNative := by
            simpa [addressed] using replayEq
          have nativeRejected :
              nativeReplayLoop configuration.profile configuration.tables
                configuration.certificate terms configuration.replayFuel
                configuration.certificate.proofs initial.toNative = none := by
            exact mappedRejected.symm
          have initialNativeEmpty : initial.toNative = {} := by
            change ({ resultIds := initial.snapshot } : NativeProofState) = {}
            rw [ResultStore.allocate?_snapshot_empty rawAllocated]
          rw [← initialNativeEmpty, nativeRejected]
      | some final =>
          have mappedAccepted :
              some final.toNative =
                nativeReplayLoop configuration.profile configuration.tables
                  configuration.certificate terms configuration.replayFuel
                  configuration.certificate.proofs initial.toNative := by
            simpa [addressed] using replayEq
          have nativeAccepted :
              nativeReplayLoop configuration.profile configuration.tables
                  configuration.certificate terms configuration.replayFuel
                  configuration.certificate.proofs initial.toNative =
                some final.toNative := by
            exact mappedAccepted.symm
          have finalWellFormed :=
            M0GCAddressedReplayControlMachine.replayLoop_wellFormed
              wellFormed addressed
          have initialNativeEmpty : initial.toNative = {} := by
            change ({ resultIds := initial.snapshot } : NativeProofState) = {}
            rw [ResultStore.allocate?_snapshot_empty rawAllocated]
          rw [← initialNativeEmpty, nativeAccepted]
          exact addressedObserveFinal_eq_native configuration terms final
            finalWellFormed

/-! ## Explicit complete-checker control machine -/

/-- A complete addressed checker state.  Allocation is a visible control
phase because address-range failure is an operational rejection, not a
logical proof failure. -/
inductive ControlState where
  | prepare
  | allocate (terms : TermState)
  | replay (terms : TermState) (remaining : List ProofNode)
      (store : ResultStore)
  | finalize (terms : TermState) (store : ResultStore)
  | halt (accepted : Bool)
deriving Repr

/-- Terminal observations are unavailable before the checker halts. -/
def observe : ControlState → Option Bool
  | .halt accepted => some accepted
  | _ => none

/-- One complete-checker transition.  A replay transition validates at most
one proof record and writes at most one preallocated result cell. -/
def step (configuration : Configuration) : ControlState → ControlState
  | .prepare =>
      match cCorePrepare? configuration.profile configuration.certificate with
      | none => .halt false
      | some terms => .allocate terms
  | .allocate terms =>
      match initialStore? configuration with
      | none => .halt false
      | some store =>
          .replay terms configuration.certificate.proofs store
  | .replay terms [] store => .finalize terms store
  | .replay terms (proof :: proofs) store =>
      match M0GCAddressedReplayControlMachine.replayRecord?
          configuration.profile configuration.tables
          configuration.certificate terms configuration.replayFuel
          store proof with
      | none => .halt false
      | some next => .replay terms proofs next
  | .finalize terms store =>
      .halt (addressedObserveFinal configuration terms store)
  | .halt accepted => .halt accepted

/-- Relational presentation for later byte-memory and imperative-language
simulations. -/
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

/-- Execute a fixed number of explicit checker transitions. -/
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

/-- Starting from replay, one transition per remaining record plus the
empty-list and finalization transitions reaches exactly the recursive
addressed observation. -/
theorem runSteps_replay_sufficient (configuration : Configuration)
    (terms : TermState) (proofs : List ProofNode) (store : ResultStore) :
    runSteps configuration (proofs.length + 2)
        (.replay terms proofs store) =
      .halt
        (match M0GCAddressedReplayControlMachine.replayLoop
            configuration.profile configuration.tables
            configuration.certificate terms configuration.replayFuel
            proofs store with
          | none => false
          | some final => addressedObserveFinal configuration terms final) := by
  induction proofs generalizing store with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      cases recordResult :
          M0GCAddressedReplayControlMachine.replayRecord?
            configuration.profile configuration.tables
            configuration.certificate terms configuration.replayFuel
            store proof with
      | none =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          simp [M0GCAddressedReplayControlMachine.replayLoop, recordResult]
      | some next =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          rw [inductionHypothesis next]
          simp [M0GCAddressedReplayControlMachine.replayLoop, recordResult]

/-- Preparation, checked allocation, chronological replay, and finalization
fit in a static budget of one transition per proof record plus four phases. -/
theorem runSteps_sufficient (configuration : Configuration) :
    runSteps configuration
        (configuration.certificate.proofs.length + 4) .prepare =
      .halt (referenceCheck configuration) := by
  unfold referenceCheck
  cases prepared :
      cCorePrepare? configuration.profile configuration.certificate with
  | none =>
      rw [show configuration.certificate.proofs.length + 4 =
        (configuration.certificate.proofs.length + 3) + 1 by omega]
      rw [runSteps, step, prepared]
      simp
  | some terms =>
      cases allocated : initialStore? configuration with
      | none =>
          rw [show configuration.certificate.proofs.length + 4 =
            (configuration.certificate.proofs.length + 3) + 1 by omega]
          rw [runSteps, step, prepared]
          rw [show configuration.certificate.proofs.length + 3 =
            (configuration.certificate.proofs.length + 2) + 1 by omega]
          rw [runSteps, step, allocated]
          simp
      | some initial =>
          rw [show configuration.certificate.proofs.length + 4 =
            (configuration.certificate.proofs.length + 3) + 1 by omega]
          rw [runSteps, step, prepared]
          rw [show configuration.certificate.proofs.length + 3 =
            (configuration.certificate.proofs.length + 2) + 1 by omega]
          rw [runSteps, step, allocated]
          exact runSteps_replay_sufficient configuration terms
            configuration.certificate.proofs initial

/-- Execute the statically sufficient complete-checker budget. -/
def execute (configuration : Configuration) : Bool :=
  match runSteps configuration
      (configuration.certificate.proofs.length + 4) .prepare with
  | .halt accepted => accepted
  | _ => false

theorem execute_eq_referenceCheck (configuration : Configuration) :
    execute configuration = referenceCheck configuration := by
  unfold execute
  rw [runSteps_sufficient]

/-- Machine acceptance entails acceptance by the independently qualified
allocation-free native checker.  Allocation failure is eliminated by the
accepted result rather than assumed by the caller. -/
theorem execute_acceptance_implies_native (configuration : Configuration)
    (accepted : execute configuration = true) :
    nativeCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificate = true := by
  cases allocated : initialStore? configuration with
  | none =>
      rw [execute_eq_referenceCheck] at accepted
      unfold referenceCheck at accepted
      cases prepared :
          cCorePrepare? configuration.profile configuration.certificate <;>
        simp [prepared, allocated] at accepted
  | some initial =>
      rw [execute_eq_referenceCheck,
        referenceCheck_eq_native_of_allocation configuration initial allocated]
        at accepted
      exact accepted

/-- A connected generated profile makes acceptance by the complete addressed
machine sound for the independently validated source calculus. -/
theorem execute_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {certificate : Certificate} {resultBase : UInt64}
    (accepted :
      execute
        { profile := candidate.physical.profile
          tables := candidate.physical.tables
          certificate
          replayFuel := candidate.decodeFuel
          submitted
          resultBase } = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  apply nativeCheckCertificate_sound connected
  exact execute_acceptance_implies_native _ accepted

/-! ## Positive and adversarial discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def pairConfiguration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    certificate
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel
    submitted := M0GCLogicalReplayCanary.pair
    resultBase := 100 }

theorem pair_allocation :
    initialStore? pairConfiguration =
      some M0GCAddressedReplayControlMachine.Canary.emptyOneSlot := by
  decide

/-- Positive discriminator: the explicit five-phase addressed machine accepts
the nontrivial pair-constructor certificate. -/
theorem pair_certificate_accepts : execute pairConfiguration = true := by
  rw [execute_eq_referenceCheck,
    referenceCheck_eq_native_of_allocation pairConfiguration
      M0GCAddressedReplayControlMachine.Canary.emptyOneSlot pair_allocation]
  exact M0GCNativeReplayAdequacy.Canary.pair_native_checker_accepts

def futureReferenceConfiguration : Configuration :=
  { pairConfiguration with
    profile := futurePremiseProfile
    certificate := futurePremiseCertificate }

theorem future_reference_allocation :
    initialStore? futureReferenceConfiguration =
      some M0GCAddressedReplayControlMachine.Canary.emptyOneSlot := by
  decide

/-- Negative chronology discriminator: an encoded proof cannot cite its own
not-yet-admitted result cell. -/
theorem current_proof_reference_rejected :
    execute futureReferenceConfiguration = false := by
  decide

def emptyProofCertificate : Certificate :=
  { certificate with proofs := [] }

def emptyProofConfiguration : Configuration :=
  { pairConfiguration with certificate := emptyProofCertificate }

/-- Negative terminal-shape discriminator: a prepared certificate with no
proof result cannot manufacture the declared goal at finalization. -/
theorem missing_final_result_rejected :
    execute emptyProofConfiguration = false := by
  decide

def overflowingConfiguration : Configuration :=
  { pairConfiguration with resultBase := UInt64.ofNat (UInt64.size - 1) }

/-- Negative resource discriminator: an otherwise valid certificate is safely
rejected when its requested result region would wrap the address space. -/
theorem overflowing_result_region_rejected :
    execute overflowingConfiguration = false := by
  decide

end Canary

#print axioms transition_deterministic
#print axioms runSteps_replay_sufficient
#print axioms runSteps_sufficient
#print axioms execute_eq_referenceCheck
#print axioms execute_acceptance_implies_native
#print axioms execute_sound
#print axioms Canary.pair_certificate_accepts
#print axioms Canary.current_proof_reference_rejected
#print axioms Canary.missing_final_result_rejected
#print axioms Canary.overflowing_result_region_rejected

end Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine
