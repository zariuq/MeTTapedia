import Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryReplayControlMachine
import Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine

/-!
# Complete M0GC certificate checking in unified byte memory

This module starts from the submitted M0GC wire bytes, decodes the certificate,
prepares its tables, allocates one contiguous physical image, replays every
proof record, and observes the final submitted claim.  The original wire bytes
form the immutable prefix of that allocation; aligned little-endian result
cells form its mutable suffix.

The big-step checker and the explicit six-phase control machine are proved
equal.  Whenever unified allocation succeeds, their Boolean observation is
exactly the independently qualified native byte checker.  Therefore machine
acceptance for a connected generated profile produces a source-calculus
derivation.

Maturity boundary: this is a fully connected intermediate proof of concept,
not the endgame implementation.  Decoding, preparation, and final observation
remain atomic Lean functions; the backing array is functional; the current
rule-table lookup and recursive matcher are not claimed to be optimized.
There is not yet pointer provenance, generated C, a verified compiler, object
code, an OS, or hardware.  Those targets must refine this machine rather than
being treated as independent agreement oracles.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryCompleteCheckerControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory.CheckerMemory
open Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryReplayControlMachine
open Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement.PackedReplay

namespace Addressed

abbrev Configuration :=
  Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.Configuration

abbrev initialStore? :=
  Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.initialStore?

abbrev addressedObserveFinal :=
  Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.addressedObserveFinal

abbrev referenceCheck :=
  Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.referenceCheck

end Addressed

/-! ## Wire-input configuration and big-step checker -/

/-- Parameters fixed throughout one physical byte-input check. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  certificateBytes : List UInt8
  replayFuel : Nat
  submitted : Pattern
  memoryBase : UInt64

/-- The typed addressed checker corresponding to a decoded certificate and
the actual aligned result base selected by unified allocation. -/
def toAddressed (configuration : Configuration) (certificate : Certificate)
    (resultBase : UInt64) : Addressed.Configuration :=
  { profile := configuration.profile
    tables := configuration.tables
    certificate
    replayFuel := configuration.replayFuel
    submitted := configuration.submitted
    resultBase }

/-- Allocate the submitted wire bytes plus exactly one result cell per proof
record. -/
def initialMemory? (configuration : Configuration)
    (certificate : Certificate) : Option CheckerMemory :=
  CheckerMemory.allocate? configuration.memoryBase
    configuration.certificateBytes.toArray certificate.proofs.length

/-- Final observation through a checked read from unified byte memory. -/
def unifiedObserveFinal (configuration : Configuration)
    (certificate : Certificate) (terms : TermState)
    (memory : CheckerMemory) : Bool :=
  match memory.readResult? (memory.resultUsed - 1) with
  | none => false
  | some finalResultId =>
      if finalResultId = certificate.goalTerm then
        match terms.patterns[certificate.goalTerm.toNat]? with
        | none => false
        | some goal => decide (goal = configuration.submitted)
      else
        false

/-- Related unified and typed final states have the same observation. -/
theorem unifiedObserveFinal_eq_addressed
    (configuration : Configuration) (certificate : Certificate)
    (terms : TermState) (memory : CheckerMemory) (typed : ResultStore)
    (refines : RefinesResultStore memory typed) :
    unifiedObserveFinal configuration certificate terms memory =
      Addressed.addressedObserveFinal
        (toAddressed configuration certificate memory.resultBase) terms typed := by
  unfold unifiedObserveFinal Addressed.addressedObserveFinal
    Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.addressedObserveFinal
  rw [← refines.used_eq]
  rw [RefinesResultStore.read_eq_all refines]
  rfl

/-- Complete big-step physical checker from submitted wire bytes. -/
def referenceCheck (configuration : Configuration) : Bool :=
  match decodeCertificate? configuration.certificateBytes with
  | none => false
  | some certificate =>
      match cCorePrepare? configuration.profile certificate with
      | none => false
      | some terms =>
          match initialMemory? configuration certificate with
          | none => false
          | some initial =>
              match M0GCUnifiedMemoryReplayControlMachine.replayLoop
                  configuration.profile configuration.tables certificate terms
                  configuration.replayFuel certificate.proofs initial with
              | none => false
              | some final =>
                  unifiedObserveFinal configuration certificate terms final

/-- Successful unified allocation produces a synchronized typed addressed
allocation at the selected result base. -/
theorem coupled_allocation_exists
    (configuration : Configuration) (certificate : Certificate)
    (initial : CheckerMemory)
    (allocated : initialMemory? configuration certificate = some initial) :
    ∃ typed,
      Addressed.initialStore?
          (toAddressed configuration certificate initial.resultBase) =
            some typed ∧
        RefinesResultStore initial typed := by
  have rawAllocated :
      CheckerMemory.allocate? configuration.memoryBase
          configuration.certificateBytes.toArray certificate.proofs.length =
        some initial := by
    simpa [initialMemory?] using allocated
  have memoryWellFormed := CheckerMemory.allocate?_wellFormed rawAllocated
  have capacityEq : initial.resultCapacity = certificate.proofs.length :=
    (CheckerMemory.allocate?_shape rawAllocated).2.2.2.2.1
  obtain ⟨typed, typedAllocated⟩ :=
    RefinesResultStore.typed_allocation_exists initial memoryWellFormed
  rw [capacityEq] at typedAllocated
  have refines := RefinesResultStore.of_allocations rawAllocated typedAllocated
  refine ⟨typed, ?_, refines⟩
  simpa [Addressed.initialStore?,
    Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.initialStore?,
    toAddressed] using typedAllocated

/-- Given successful physical allocation, the unified big-step checker equals
the typed addressed reference for the corresponding result base. -/
theorem referenceCheck_eq_addressed_of_allocation
    (configuration : Configuration) (certificate : Certificate)
    (initial : CheckerMemory)
    (decoded :
      decodeCertificate? configuration.certificateBytes = some certificate)
    (allocated : initialMemory? configuration certificate = some initial) :
    referenceCheck configuration =
      Addressed.referenceCheck
        (toAddressed configuration certificate initial.resultBase) := by
  obtain ⟨typed, typedAllocated, initialRefines⟩ :=
    coupled_allocation_exists configuration certificate initial allocated
  unfold referenceCheck Addressed.referenceCheck
    Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.referenceCheck
  simp only [decoded, toAddressed]
  cases prepared : cCorePrepare? configuration.profile certificate with
  | none => rfl
  | some terms =>
      have typedAllocatedRaw :
          Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.initialStore?
              { profile := configuration.profile
                tables := configuration.tables
                certificate := certificate
                replayFuel := configuration.replayFuel
                submitted := configuration.submitted
                resultBase := initial.resultBase } = some typed := by
        simpa [Addressed.initialStore?, toAddressed] using typedAllocated
      simp only [allocated, typedAllocatedRaw]
      have enough :
          initial.resultUsed + certificate.proofs.length ≤
            initial.resultCapacity := by
        obtain ⟨_base, _certificate, _offset, _resultBase, capacity, used⟩ :=
          CheckerMemory.allocate?_shape
            (by simpa [initialMemory?] using allocated)
        rw [used, capacity]
        omega
      have replayRefines :=
        M0GCUnifiedMemoryReplayControlMachine.replayLoop_refines_typed_of_capacity
          configuration.profile configuration.tables certificate terms
          configuration.replayFuel certificate.proofs initial typed
          initialRefines enough
      cases memoryReplay :
          M0GCUnifiedMemoryReplayControlMachine.replayLoop
            configuration.profile configuration.tables certificate terms
            configuration.replayFuel certificate.proofs initial with
      | none =>
          cases typedReplay :
              M0GCAddressedReplayControlMachine.replayLoop
                configuration.profile configuration.tables certificate terms
                configuration.replayFuel certificate.proofs typed with
          | none => rfl
          | some typedFinal =>
              simp [memoryReplay, typedReplay, OptionRefines] at replayRefines
      | some memoryFinal =>
          cases typedReplay :
              M0GCAddressedReplayControlMachine.replayLoop
                configuration.profile configuration.tables certificate terms
                configuration.replayFuel certificate.proofs typed with
          | none =>
              simp [memoryReplay, typedReplay, OptionRefines] at replayRefines
          | some typedFinal =>
              have finalRefines :
                  RefinesResultStore memoryFinal typedFinal := by
                simpa [memoryReplay, typedReplay, OptionRefines] using
                  replayRefines
              exact unifiedObserveFinal_eq_addressed configuration certificate
                terms memoryFinal typedFinal finalRefines

/-- Whenever unified allocation succeeds, the complete byte-memory checker is
exactly the qualified native byte checker. -/
theorem referenceCheck_eq_nativeBytes_of_allocation
    (configuration : Configuration) (certificate : Certificate)
    (initial : CheckerMemory)
    (decoded :
      decodeCertificate? configuration.certificateBytes = some certificate)
    (allocated : initialMemory? configuration certificate = some initial) :
    referenceCheck configuration =
      nativeCheckBytes configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificateBytes := by
  rw [referenceCheck_eq_addressed_of_allocation configuration certificate
    initial decoded allocated]
  obtain ⟨typed, typedAllocated, _refines⟩ :=
    coupled_allocation_exists configuration certificate initial allocated
  change
    Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.referenceCheck
        (toAddressed configuration certificate initial.resultBase) = _
  rw [Mettapedia.GSLT.LanguageDef.M0GCAddressedCompleteCheckerControlMachine.referenceCheck_eq_native_of_allocation
    (toAddressed configuration certificate initial.resultBase) typed
    typedAllocated]
  simp [nativeCheckBytes, decoded, toAddressed]

/-! ## Explicit six-phase byte-input control machine -/

inductive ControlState where
  | decode
  | prepare (certificate : Certificate)
  | allocate (certificate : Certificate) (terms : TermState)
  | replay (certificate : Certificate) (terms : TermState)
      (remaining : List ProofNode) (memory : CheckerMemory)
  | finalize (certificate : Certificate) (terms : TermState)
      (memory : CheckerMemory)
  | halt (accepted : Bool)
deriving Repr

def observe : ControlState → Option Bool
  | .halt accepted => some accepted
  | _ => none

/-- One explicit control transition.  A replay transition validates and writes
at most one proof record. -/
def step (configuration : Configuration) : ControlState → ControlState
  | .decode =>
      match decodeCertificate? configuration.certificateBytes with
      | none => .halt false
      | some certificate => .prepare certificate
  | .prepare certificate =>
      match cCorePrepare? configuration.profile certificate with
      | none => .halt false
      | some terms => .allocate certificate terms
  | .allocate certificate terms =>
      match initialMemory? configuration certificate with
      | none => .halt false
      | some memory => .replay certificate terms certificate.proofs memory
  | .replay certificate terms [] memory =>
      .finalize certificate terms memory
  | .replay certificate terms (proof :: proofs) memory =>
      match M0GCUnifiedMemoryReplayControlMachine.replayRecord?
          configuration.profile configuration.tables certificate terms
          configuration.replayFuel memory proof with
      | none => .halt false
      | some next => .replay certificate terms proofs next
  | .finalize certificate terms memory =>
      .halt (unifiedObserveFinal configuration certificate terms memory)
  | .halt accepted => .halt accepted

def Transition (configuration : Configuration)
    (before after : ControlState) : Prop :=
  step configuration before = after

theorem transition_deterministic
    (configuration : Configuration) {before afterLeft afterRight : ControlState}
    (left : Transition configuration before afterLeft)
    (right : Transition configuration before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (configuration : Configuration) (accepted : Bool) :
    step configuration (.halt accepted) = .halt accepted := rfl

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

/-- Proof-record count visible after decoding, or zero on malformed input. -/
def decodedProofCount (configuration : Configuration) : Nat :=
  ((decodeCertificate? configuration.certificateBytes).map
    (fun certificate => certificate.proofs.length)).getD 0

/-- Static complete-machine transition budget. -/
def executionSteps (configuration : Configuration) : Nat :=
  decodedProofCount configuration + 5

/-- From replay, one step per remaining record plus empty-list and finalization
steps reaches the exact recursive observation. -/
theorem runSteps_replay_sufficient (configuration : Configuration)
    (certificate : Certificate) (terms : TermState)
    (proofs : List ProofNode) (memory : CheckerMemory) :
    runSteps configuration (proofs.length + 2)
        (.replay certificate terms proofs memory) =
      .halt
        (match M0GCUnifiedMemoryReplayControlMachine.replayLoop
            configuration.profile configuration.tables certificate terms
            configuration.replayFuel proofs memory with
          | none => false
          | some final =>
              unifiedObserveFinal configuration certificate terms final) := by
  induction proofs generalizing memory with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      cases recordResult :
          M0GCUnifiedMemoryReplayControlMachine.replayRecord?
            configuration.profile configuration.tables certificate terms
            configuration.replayFuel memory proof with
      | none =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          simp [M0GCUnifiedMemoryReplayControlMachine.replayLoop, recordResult]
      | some next =>
          rw [show (proof :: proofs).length + 2 =
            (proofs.length + 2) + 1 by simp]
          rw [runSteps, step, recordResult]
          rw [inductionHypothesis next]
          simp [M0GCUnifiedMemoryReplayControlMachine.replayLoop, recordResult]

/-- Decode, prepare, allocate, replay, and finalize in a static budget of one
transition per proof record plus five. -/
theorem runSteps_sufficient (configuration : Configuration) :
    runSteps configuration (executionSteps configuration) .decode =
      .halt (referenceCheck configuration) := by
  unfold executionSteps decodedProofCount
  unfold referenceCheck
  cases decoded : decodeCertificate? configuration.certificateBytes with
  | none =>
      simp [decoded, runSteps, step]
  | some certificate =>
      simp only [Option.map_some, Option.getD_some]
      cases prepared : cCorePrepare? configuration.profile certificate with
      | none =>
          rw [show certificate.proofs.length + 5 =
            (certificate.proofs.length + 4) + 1 by omega]
          rw [runSteps, step, decoded]
          rw [show certificate.proofs.length + 4 =
            (certificate.proofs.length + 3) + 1 by omega]
          rw [runSteps, step, prepared]
          simp
      | some terms =>
          cases allocated : initialMemory? configuration certificate with
          | none =>
              rw [show certificate.proofs.length + 5 =
                (certificate.proofs.length + 4) + 1 by omega]
              rw [runSteps, step, decoded]
              rw [show certificate.proofs.length + 4 =
                (certificate.proofs.length + 3) + 1 by omega]
              rw [runSteps, step, prepared]
              rw [show certificate.proofs.length + 3 =
                (certificate.proofs.length + 2) + 1 by omega]
              rw [runSteps, step, allocated]
              simp
          | some initial =>
              rw [show certificate.proofs.length + 5 =
                (certificate.proofs.length + 4) + 1 by omega]
              rw [runSteps, step, decoded]
              rw [show certificate.proofs.length + 4 =
                (certificate.proofs.length + 3) + 1 by omega]
              rw [runSteps, step, prepared]
              rw [show certificate.proofs.length + 3 =
                (certificate.proofs.length + 2) + 1 by omega]
              rw [runSteps, step, allocated]
              exact runSteps_replay_sufficient configuration certificate terms
                certificate.proofs initial

/-- Execute the statically sufficient complete-machine budget. -/
def execute (configuration : Configuration) : Bool :=
  match runSteps configuration
      (executionSteps configuration) .decode with
  | .halt accepted => accepted
  | _ => false

theorem execute_eq_referenceCheck (configuration : Configuration) :
    execute configuration = referenceCheck configuration := by
  unfold execute
  rw [runSteps_sufficient]

/-- Complete-machine acceptance entails native byte-checker acceptance;
allocation failure is discharged from the observed `true`, not assumed. -/
theorem execute_acceptance_implies_nativeBytes
    (configuration : Configuration) (accepted : execute configuration = true) :
    nativeCheckBytes configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted
        configuration.certificateBytes = true := by
  cases decoded : decodeCertificate? configuration.certificateBytes with
  | none =>
      rw [execute_eq_referenceCheck] at accepted
      simp [referenceCheck, decoded] at accepted
  | some certificate =>
      cases allocated : initialMemory? configuration certificate with
      | none =>
          rw [execute_eq_referenceCheck] at accepted
          unfold referenceCheck at accepted
          rw [decoded] at accepted
          cases prepared : cCorePrepare? configuration.profile certificate <;>
            simp [prepared, allocated] at accepted
      | some initial =>
          rw [execute_eq_referenceCheck,
            referenceCheck_eq_nativeBytes_of_allocation configuration
              certificate initial decoded allocated] at accepted
          exact accepted

/-- A connected generated profile makes acceptance by the complete byte-memory
machine sound for the independently validated source calculus. -/
theorem execute_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {certificateBytes : List UInt8}
    {memoryBase : UInt64}
    (accepted :
      execute
        { profile := candidate.physical.profile
          tables := candidate.physical.tables
          certificateBytes
          replayFuel := candidate.decodeFuel
          submitted
          memoryBase } = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  apply nativeCheckBytes_sound connected
  exact execute_acceptance_implies_nativeBytes _ accepted

/-! ## Positive and adversarial discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def pairConfiguration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    certificateBytes := encodeCertificate certificate
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel
    submitted := M0GCLogicalReplayCanary.pair
    memoryBase := 1 }

/-- Positive end-to-end wire discriminator through all six phases. -/
theorem pair_certificate_accepts : execute pairConfiguration = true := by
  rw [execute_eq_referenceCheck]
  have decoded :
      decodeCertificate? pairConfiguration.certificateBytes =
        some M0GCLogicalReplayCanary.certificate := by
    simpa [pairConfiguration] using
      decodeCertificate?_encodeCertificate M0GCLogicalReplayCanary.certificate
        certificate_encodable
  cases allocated : initialMemory? pairConfiguration
      M0GCLogicalReplayCanary.certificate with
  | none =>
      have allocationExists :
          (initialMemory? pairConfiguration
            M0GCLogicalReplayCanary.certificate).isSome = true := by
        set_option maxRecDepth 20000 in
          decide
      simp [allocated] at allocationExists
  | some initial =>
      rw [referenceCheck_eq_nativeBytes_of_allocation pairConfiguration
        M0GCLogicalReplayCanary.certificate initial decoded allocated]
      unfold nativeCheckBytes
      rw [decoded]
      exact M0GCNativeReplayAdequacy.Canary.pair_native_checker_accepts

def corruptConfiguration : Configuration :=
  { pairConfiguration with
    certificateBytes := 0 :: pairConfiguration.certificateBytes.tail }

/-- Negative wire discriminator: corrupt magic is rejected before allocation. -/
theorem corrupt_magic_rejected : execute corruptConfiguration = false := by
  decide

def overflowingConfiguration : Configuration :=
  { pairConfiguration with
    memoryBase := UInt64.ofNat (UInt64.size - 1) }

/-- Negative physical-resource discriminator: the complete unified image may
not wrap the address space. -/
theorem overflowing_unified_image_rejected :
    execute overflowingConfiguration = false := by
  set_option maxRecDepth 20000 in
    decide

def futureReferenceConfiguration : Configuration :=
  { pairConfiguration with
    profile := futurePremiseProfile
    certificateBytes := encodeCertificate futurePremiseCertificate }

/-- Negative chronology discriminator: a proof cannot cite its own
not-yet-admitted result. -/
theorem current_proof_reference_rejected :
    execute futureReferenceConfiguration = false := by
  set_option maxRecDepth 20000 in
    decide

end Canary

#print axioms unifiedObserveFinal_eq_addressed
#print axioms coupled_allocation_exists
#print axioms referenceCheck_eq_addressed_of_allocation
#print axioms referenceCheck_eq_nativeBytes_of_allocation
#print axioms transition_deterministic
#print axioms runSteps_replay_sufficient
#print axioms runSteps_sufficient
#print axioms execute_eq_referenceCheck
#print axioms execute_acceptance_implies_nativeBytes
#print axioms execute_sound
#print axioms Canary.pair_certificate_accepts
#print axioms Canary.corrupt_magic_rejected
#print axioms Canary.overflowing_unified_image_rejected
#print axioms Canary.current_proof_reference_rejected

end Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryCompleteCheckerControlMachine
