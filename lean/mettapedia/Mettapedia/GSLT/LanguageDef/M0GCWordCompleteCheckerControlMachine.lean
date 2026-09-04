import Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine
import Mettapedia.GSLT.LanguageDef.M0GCWordCheckerBoundaryMachine

/-!
# Complete word-loaded certificate-checker control for M0GC

This module composes the five-stage finite-word loader with the complete
bounded replay machine.  Loading, preparation, every proof-record check,
capacity enforcement, final-proof pinning, and submitted-claim observation
are now transitions of one deterministic machine.  Its terminal Boolean is
proved exactly equal to the prior qualified checker composition.

Maturity boundary: this is a fully connected intermediate proof of concept,
not an endgame implementation.  The word region is immutable, term and proof
stores are persistent Lean arrays, and the fixed execution budget is computed
by the already-qualified loader as a specification-level prepass.  This is
not yet an optimized ABI, mutable target-addressed store, generated
Pancake/Clight/C program, verified object code, OS, or hardware model.  A
backend must replace these representations and the budget prepass by proved
refinements while preserving this terminal observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCWordCompleteCheckerControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.WordRegion

namespace Loader

abbrev State :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.ControlState

abbrev initial : State := .loadHeader

abbrev step :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step

abbrev observe :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe

abbrev runSteps :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps

abbrev execute :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute

end Loader

namespace Complete

abbrev Configuration :=
  Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.Configuration

abbrev State :=
  Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.ControlState

abbrev step :=
  Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.step

abbrev runSteps :=
  Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.runSteps

abbrev execute :=
  Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute

end Complete

/-! ## Composed control machine -/

/-- Parameters fixed for one word-loaded checker invocation. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  replayFuel : Nat
  submitted : Pattern

def Configuration.ofCandidate (candidate : Candidate)
    (submitted : Pattern) : Configuration :=
  { profile := candidate.physical.profile
    tables := candidate.physical.tables
    replayFuel := candidate.decodeFuel
    submitted }

/-- Select the complete decoded-certificate configuration after loading. -/
def checkerConfiguration (configuration : Configuration)
    (certificate : Certificate) : Complete.Configuration :=
  { profile := configuration.profile
    tables := configuration.tables
    certificate
    replayFuel := configuration.replayFuel
    submitted := configuration.submitted }

/-- The outer machine owns either the loader or a complete decoded checker.
An accepting/rejecting inner halt is immediately lifted to the outer halt. -/
inductive ControlState where
  | loading (loader : Loader.State)
  | checking (certificate : Certificate) (checker : Complete.State)
  | halt (accepted : Bool)

def observe : ControlState → Option Bool
  | .halt accepted => some accepted
  | _ => none

/-- Embed an inner checker state without retaining a redundant halted layer. -/
def liftCheckerState (certificate : Certificate) :
    Complete.State → ControlState
  | .halt accepted => .halt accepted
  | checker => .checking certificate checker

/-- One deterministic transition of the complete word-loaded checker. -/
def step (configuration : Configuration) (region : WordRegion) :
    ControlState → ControlState
  | .loading loader =>
      match Loader.observe loader with
      | none => .loading (Loader.step region loader)
      | some none => .halt false
      | some (some certificate) => .checking certificate .prepare
  | .checking certificate checker =>
      liftCheckerState certificate
        (Complete.step (checkerConfiguration configuration certificate)
          checker)
  | .halt accepted => .halt accepted

def Transition (configuration : Configuration) (region : WordRegion)
    (before after : ControlState) : Prop :=
  step configuration region before = after

theorem transition_deterministic
    (configuration : Configuration) (region : WordRegion)
    {before afterLeft afterRight : ControlState}
    (left : Transition configuration region before afterLeft)
    (right : Transition configuration region before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (configuration : Configuration)
    (region : WordRegion) (accepted : Bool) :
    step configuration region (.halt accepted) = .halt accepted := rfl

def runSteps (configuration : Configuration) (region : WordRegion) :
    Nat → ControlState → ControlState
  | 0, state => state
  | fuel + 1, state =>
      runSteps configuration region fuel (step configuration region state)

@[simp] theorem runSteps_halt (configuration : Configuration)
    (region : WordRegion) (fuel : Nat) (accepted : Bool) :
    runSteps configuration region fuel (.halt accepted) = .halt accepted := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [runSteps, inductionHypothesis]

theorem runSteps_add (configuration : Configuration) (region : WordRegion)
    (first second : Nat) (state : ControlState) :
    runSteps configuration region (first + second) state =
      runSteps configuration region second
        (runSteps configuration region first state) := by
  induction first generalizing state with
  | zero => simp [runSteps]
  | succ first inductionHypothesis =>
      simp [Nat.succ_add, runSteps, inductionHypothesis]

/-! ## Loader and checker composition -/

/-- The complete checker transition commutes with its outer-state embedding. -/
theorem step_liftCheckerState (configuration : Configuration)
    (region : WordRegion) (certificate : Certificate)
    (checker : Complete.State) :
    step configuration region (liftCheckerState certificate checker) =
      liftCheckerState certificate
        (Complete.step (checkerConfiguration configuration certificate)
          checker) := by
  cases checker <;> rfl

/-- Any number of inner checker transitions commutes with the embedding. -/
theorem runSteps_liftCheckerState (configuration : Configuration)
    (region : WordRegion) (certificate : Certificate)
    (fuel : Nat) (checker : Complete.State) :
    runSteps configuration region fuel
        (liftCheckerState certificate checker) =
      liftCheckerState certificate
        (Complete.runSteps (checkerConfiguration configuration certificate)
          fuel checker) := by
  induction fuel generalizing checker with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [runSteps, step_liftCheckerState, inductionHypothesis]
      rfl

/-- Six outer transitions finish the loader boundary: five loader phases and
one transition that either rejects or starts the complete checker. -/
theorem runSteps_six_loading (configuration : Configuration)
    (region : WordRegion) :
    runSteps configuration region 6 (.loading Loader.initial) =
      match Loader.execute region with
      | none => .halt false
      | some certificate => .checking certificate .prepare := by
  unfold Loader.execute
  cases headerResult : region.readHeader? with
  | none =>
      simp [runSteps, step, Loader.step, Loader.observe,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
        headerResult]
  | some header =>
      let counts := BodyCounts.ofHeader header
      cases layoutResult : BodyLayout.ofCounts? counts with
      | none =>
          simp [runSteps, step, Loader.step, Loader.observe,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
            headerResult, counts, layoutResult]
      | some layout =>
          cases bodyResult : region.loadBytes? 104 layout.bodyWidth with
          | none =>
              simp [runSteps, step, Loader.step, Loader.observe,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                headerResult, counts, layoutResult, bodyResult]
          | some bodyBytes =>
              cases tablesResult : region.readBodyAt? counts 104 with
              | none =>
                  simp [runSteps, step, Loader.step, Loader.observe,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                    headerResult, counts, layoutResult, bodyResult,
                    tablesResult]
              | some tables =>
                  by_cases checksumMatches :
                      header.bodyChecksum = fnv1a64 bodyBytes
                  · simp [runSteps, step, Loader.step, Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]
                  · simp [runSteps, step, Loader.step, Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]

/-- A specification-level budget: six transitions to cross the loader, then
one preparation, one per proof record, one empty-list transition, and one
final observation. -/
def executionBudget (region : WordRegion) : Nat :=
  match Loader.execute region with
  | none => 6
  | some certificate => 6 + (certificate.proofs.length + 3)

/-- Big-step reference assembled only from the already-qualified loader and
complete decoded checker. -/
def referenceCheck (configuration : Configuration)
    (region : WordRegion) : Bool :=
  match Loader.execute region with
  | none => false
  | some certificate =>
      Complete.execute (checkerConfiguration configuration certificate)

/-- The specification-level budget always reaches the exact composed
terminal observation. -/
theorem runSteps_budget_halts (configuration : Configuration)
    (region : WordRegion) :
    runSteps configuration region (executionBudget region)
        (.loading Loader.initial) =
      .halt (referenceCheck configuration region) := by
  unfold executionBudget referenceCheck
  cases loaded : Loader.execute region with
  | none =>
      rw [runSteps_six_loading, loaded]
  | some certificate =>
      rw [runSteps_add]
      rw [runSteps_six_loading, loaded]
      change
        runSteps configuration region (certificate.proofs.length + 3)
            (liftCheckerState certificate (.prepare : Complete.State)) =
          .halt
            (Complete.execute
              (checkerConfiguration configuration certificate))
      rw [runSteps_liftCheckerState]
      have innerHalt :=
        Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.runSteps_sufficient
          (checkerConfiguration configuration certificate)
      rw [show
        Complete.runSteps (checkerConfiguration configuration certificate)
            (certificate.proofs.length + 3) .prepare =
          Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.ControlState.halt
            (Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.referenceCheck
              (checkerConfiguration configuration certificate)) by
        exact innerHalt]
      change
        ControlState.halt
            (Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.referenceCheck
              (checkerConfiguration configuration certificate)) =
          ControlState.halt
            (Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute
              (checkerConfiguration configuration certificate))
      rw [Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute_eq_referenceCheck]

/-- Execute the complete word-loaded checker. -/
def execute (configuration : Configuration) (region : WordRegion) : Bool :=
  match runSteps configuration region (executionBudget region)
      (.loading Loader.initial) with
  | .halt accepted => accepted
  | _ => false

theorem execute_eq_reference (configuration : Configuration)
    (region : WordRegion) :
    execute configuration region = referenceCheck configuration region := by
  unfold execute
  rw [runSteps_budget_halts]

/-! ## Exact-byte and semantic consequences -/

/-- Successful source-byte compilation and machine acceptance imply
acceptance by the exact source-byte proof-prefix checker. -/
theorem execute_compiled_refines_cCoreCheckBytes
    (configuration : Configuration) (bytes : List UInt8)
    (region : WordRegion)
    (compiled : WordRegion.ofList? bytes = some region)
    (accepted : execute configuration region = true) :
    cCoreCheckBytes configuration.profile configuration.tables
      configuration.replayFuel configuration.submitted bytes = true := by
  rw [execute_eq_reference] at accepted
  unfold referenceCheck at accepted
  cases loaded : Loader.execute region with
  | none => simp [loaded] at accepted
  | some certificate =>
      have flatLoaded : readCertificateFlat? bytes = some certificate := by
        rw [← M0GCWordLoaderControlMachine.execute_ofList?
          bytes region compiled]
        exact loaded
      have decoded :=
        readCertificateFlat?_refines_decodeCertificate?
          bytes certificate flatLoaded
      unfold cCoreCheckBytes
      rw [decoded]
      have completeAccepted :
          Complete.execute
              (checkerConfiguration configuration certificate) = true := by
        simpa [loaded] using accepted
      change
        Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute
            (checkerConfiguration configuration certificate) = true
        at completeAccepted
      rw [Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute_eq_cCoreCheckCertificate]
        at completeAccepted
      exact completeAccepted

/-- Connected-profile acceptance yields a typed derivation in the
independently validated source calculus. -/
theorem execute_ofCandidate_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {region : WordRegion}
    (accepted :
      execute (Configuration.ofCandidate candidate submitted) region = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  rw [execute_eq_reference] at accepted
  unfold referenceCheck Configuration.ofCandidate at accepted
  cases loaded : Loader.execute region with
  | none => simp [loaded] at accepted
  | some certificate =>
      apply Mettapedia.GSLT.LanguageDef.M0GCCompleteReplayControlMachine.execute_sound
        connected
      simpa [loaded, checkerConfiguration] using accepted

/-! ## Positive and negative discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def configuration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel
    submitted := M0GCLogicalReplayCanary.pair }

/-- Positive discriminator through word loading and every replay transition. -/
theorem pair_machine_accepts (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate certificate) = some region) :
    execute configuration region = true := by
  rw [execute_eq_reference]
  unfold referenceCheck Loader.execute
  rw [M0GCWordLoaderControlMachine.execute_encodeCertificate
    certificate certificate_encodable region compiled]
  change
    M0GCCompleteReplayControlMachine.execute
      M0GCCompleteReplayControlMachine.Canary.pairConfiguration = true
  exact M0GCCompleteReplayControlMachine.Canary.pair_certificate_accepts

/-- Negative semantic discriminator: valid bytes do not prove another claim. -/
theorem wrong_claim_rejected (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate certificate) = some region) :
    execute { configuration with submitted := unrelatedClaim } region =
      false := by
  rw [execute_eq_reference]
  unfold referenceCheck Loader.execute
  rw [M0GCWordLoaderControlMachine.execute_encodeCertificate
    certificate certificate_encodable region compiled]
  change
    M0GCCompleteReplayControlMachine.execute
      { M0GCCompleteReplayControlMachine.Canary.pairConfiguration with
        submitted := unrelatedClaim } = false
  rw [M0GCCompleteReplayControlMachine.execute_eq_cCoreCheckCertificate]
  change cCoreCheckCertificate profile
    M0GCCoreLoopCorrespondence.Canary.tables
    M0GCCoreLoopCorrespondence.Canary.canaryFuel unrelatedClaim certificate =
      false
  unfold cCoreCheckCertificate
  rw [M0GCCoreLoopCorrespondence.Canary.pair_core_replay_accepts]
  decide

/-- Negative physical discriminator: checksum corruption never enters the
complete replay submachine. -/
theorem wrong_checksum_rejected (region : WordRegion)
    (compiled : WordRegion.ofList? wrongChecksumCanary = some region) :
    execute configuration region = false := by
  rw [execute_eq_reference]
  unfold referenceCheck Loader.execute
  rw [M0GCWordLoaderControlMachine.wrong_checksum_machine_rejected
    region compiled]

/-- Negative exact-file discriminator: trailing bytes never enter replay. -/
theorem trailing_bytes_rejected (region : WordRegion)
    (compiled :
      WordRegion.ofList?
          (encodeCertificate M0GCWireFormat.canaryCertificate ++ [0]) =
        some region) :
    execute configuration region = false := by
  rw [execute_eq_reference]
  unfold referenceCheck Loader.execute
  rw [M0GCWordLoaderControlMachine.trailing_machine_rejected
    region compiled]

end Canary

#print axioms transition_deterministic
#print axioms runSteps_add
#print axioms step_liftCheckerState
#print axioms runSteps_liftCheckerState
#print axioms runSteps_six_loading
#print axioms runSteps_budget_halts
#print axioms execute_eq_reference
#print axioms execute_compiled_refines_cCoreCheckBytes
#print axioms execute_ofCandidate_sound
#print axioms Canary.pair_machine_accepts
#print axioms Canary.wrong_claim_rejected
#print axioms Canary.wrong_checksum_rejected
#print axioms Canary.trailing_bytes_rejected

end Mettapedia.GSLT.LanguageDef.M0GCWordCompleteCheckerControlMachine
