import Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence
import Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine

/-!
# Combined word-loader and proof-replay boundary machine for M0GC

This module composes the explicit finite-word loader with the independently
qualified proof-prefix replay checker.  It proves that acceptance by the
combined control machine implies acceptance by the exact byte checker and,
for a connected generated profile, a typed derivation in the selected source
calculus.

Maturity boundary: this is a fully connected intermediate proof of concept.
The five loader phases are explicit, but the already-proved proof-prefix
replay remains one atomic control transition here.  This is not yet the
endgame per-proof-record machine, mutable storage semantics, optimized ABI,
Pancake or Clight program, verified compilation, object code, OS, or hardware
model.  The next refinement must split replay into chronological transitions
without weakening this module's terminal-observation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCWordCheckerBoundaryMachine

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

abbrev execute :=
  Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute

end Loader

/-! ## Combined boundary machine -/

/-- Parameters that are fixed for one checker invocation. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  replayFuel : Nat
  submitted : Pattern

/-- Instantiate the executable configuration selected by a qualified
generated profile. -/
def Configuration.ofCandidate (candidate : Candidate)
    (submitted : Pattern) : Configuration :=
  { profile := candidate.physical.profile
    tables := candidate.physical.tables
    replayFuel := candidate.decodeFuel
    submitted }

/-- The loader evolves explicitly.  A decoded certificate then crosses one
named atomic replay boundary before exposing the terminal Boolean result. -/
inductive ControlState where
  | loading (loader : Loader.State)
  | replay (certificate : Certificate)
  | halt (accepted : Bool)

/-- A terminal Boolean is observable only after the machine halts. -/
def observe : ControlState → Option Bool
  | .halt accepted => some accepted
  | _ => none

/-- One deterministic combined transition. -/
def step (configuration : Configuration) (region : WordRegion) :
    ControlState → ControlState
  | .loading loader =>
      match Loader.observe loader with
      | none => .loading (Loader.step region loader)
      | some none => .halt false
      | some (some certificate) => .replay certificate
  | .replay certificate =>
      .halt
        (cCoreCheckCertificate configuration.profile configuration.tables
          configuration.replayFuel configuration.submitted certificate)
  | .halt accepted => .halt accepted

/-- Relational presentation for later backend simulations. -/
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

/-- Execute a fixed number of combined control transitions. -/
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

/-- Five loader steps, one loader-result transition, and one replay
transition suffice.  Earlier loader failure stutters at rejection. -/
theorem runSteps_seven_halts
    (configuration : Configuration) (region : WordRegion) :
    ∃ accepted,
      runSteps configuration region 7 (.loading Loader.initial) =
        .halt accepted := by
  cases headerResult : region.readHeader? with
  | none =>
      exact ⟨false, by simp [runSteps, step, Loader.step,
        Loader.observe,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
        Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
        headerResult]⟩
  | some header =>
      let counts := BodyCounts.ofHeader header
      cases layoutResult : BodyLayout.ofCounts? counts with
      | none =>
          exact ⟨false, by simp [runSteps, step,
            Loader.step, Loader.observe,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
            Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
            headerResult, counts, layoutResult]⟩
      | some layout =>
          cases bodyResult : region.loadBytes? 104 layout.bodyWidth with
          | none =>
              exact ⟨false, by simp [runSteps, step,
                Loader.step, Loader.observe,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                headerResult, counts, layoutResult, bodyResult]⟩
          | some bodyBytes =>
              cases tablesResult : region.readBodyAt? counts 104 with
              | none =>
                  exact ⟨false, by simp [runSteps, step,
                    Loader.step, Loader.observe,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                    headerResult, counts, layoutResult, bodyResult,
                    tablesResult]⟩
              | some tables =>
                  by_cases checksumMatches :
                      header.bodyChecksum = fnv1a64 bodyBytes
                  · refine ⟨cCoreCheckCertificate configuration.profile
                        configuration.tables configuration.replayFuel
                        configuration.submitted
                        (M0GCCanonicalBodyBytes.certificateOfTables
                          header tables), ?_⟩
                    simp [runSteps, step, Loader.step,
                      Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]
                  · exact ⟨false, by simp [runSteps, step,
                      Loader.step, Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]⟩

/-- Terminal observation after the statically sufficient seven transitions. -/
def execute (configuration : Configuration) (region : WordRegion) : Bool :=
  match runSteps configuration region 7 (.loading Loader.initial) with
  | .halt accepted => accepted
  | _ => false

/-- Big-step reference at the exact composition boundary. -/
def referenceCheck (configuration : Configuration)
    (region : WordRegion) : Bool :=
  match Loader.execute region with
  | none => false
  | some certificate =>
      cCoreCheckCertificate configuration.profile configuration.tables
        configuration.replayFuel configuration.submitted certificate

/-- The combined transition system and the independently proved composition
have the same terminal Boolean observation on every finite-word region. -/
theorem execute_eq_reference
    (configuration : Configuration) (region : WordRegion) :
    execute configuration region = referenceCheck configuration region := by
  unfold execute referenceCheck Loader.execute
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
              simp [runSteps, step, Loader.step,
                Loader.observe,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                headerResult, counts, layoutResult, bodyResult]
          | some bodyBytes =>
              cases tablesResult : region.readBodyAt? counts 104 with
              | none =>
                  simp [runSteps, step, Loader.step,
                    Loader.observe,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                    Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                    headerResult, counts, layoutResult, bodyResult,
                    tablesResult]
              | some tables =>
                  by_cases checksumMatches :
                      header.bodyChecksum = fnv1a64 bodyBytes
                  · simp [runSteps, step, Loader.step,
                      Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]
                  · simp [runSteps, step, Loader.step,
                      Loader.observe,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.execute,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.runSteps,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.step,
                      Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine.observe,
                      headerResult, counts, layoutResult, bodyResult,
                      tablesResult, checksumMatches]

/-! ## Exact-byte and semantic consequences -/

/-- Acceptance after a successful source-byte compilation is also acceptance
by the exact source-byte proof-prefix checker.  This is the no-extra-
acceptance direction required of the new physical boundary. -/
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
      simpa [loaded] using accepted

/-- For a connected generated profile, combined-machine acceptance yields a
typed derivation in the independently validated source calculus. -/
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
      exact cCoreCheckCertificate_sound connected
        (by simpa [loaded] using accepted)

/-- The source-byte form records both the actual finite-word compilation and
the resulting typed source derivation. -/
theorem execute_compiled_ofCandidate_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {bytes : List UInt8} {region : WordRegion}
    (compiled : WordRegion.ofList? bytes = some region)
    (accepted :
      execute (Configuration.ofCandidate candidate submitted) region = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  apply cCoreCheckBytes_sound connected
  exact execute_compiled_refines_cCoreCheckBytes
    (Configuration.ofCandidate candidate submitted)
    bytes region compiled accepted

/-! ## Positive and negative discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def configuration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel
    submitted := M0GCLogicalReplayCanary.pair }

/-- Positive discriminator crossing exact bytes, all five loader phases, and
the proof-prefix checker. -/
theorem pair_combined_machine_accepts
    (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate certificate) = some region) :
    execute configuration region = true := by
  rw [execute_eq_reference]
  unfold referenceCheck
  unfold Loader.execute
  rw [M0GCWordLoaderControlMachine.execute_encodeCertificate
    certificate certificate_encodable region compiled]
  exact M0GCCoreLoopCorrespondence.Canary.pair_core_checker_accepts

/-- Negative semantic discriminator: valid certificate bytes do not authorize
a different submitted claim. -/
theorem wrong_claim_combined_machine_rejected
    (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate certificate) = some region) :
    execute { configuration with submitted := unrelatedClaim } region =
      false := by
  rw [execute_eq_reference]
  unfold referenceCheck
  unfold Loader.execute
  rw [M0GCWordLoaderControlMachine.execute_encodeCertificate
    certificate certificate_encodable region compiled]
  change cCoreCheckCertificate profile
    M0GCCoreLoopCorrespondence.Canary.tables
    M0GCCoreLoopCorrespondence.Canary.canaryFuel
    unrelatedClaim certificate = false
  unfold cCoreCheckCertificate
  rw [M0GCCoreLoopCorrespondence.Canary.pair_core_replay_accepts]
  decide

/-- Negative physical discriminator: a checksum mutation cannot reach replay. -/
theorem wrong_checksum_combined_machine_rejected
    (region : WordRegion)
    (compiled : WordRegion.ofList? wrongChecksumCanary = some region) :
    execute configuration region = false := by
  rw [execute_eq_reference]
  unfold referenceCheck
  unfold Loader.execute
  rw [M0GCWordLoaderControlMachine.wrong_checksum_machine_rejected
    region compiled]

/-- Negative exact-file discriminator: trailing bytes cannot reach replay. -/
theorem trailing_combined_machine_rejected
    (region : WordRegion)
    (compiled :
      WordRegion.ofList?
          (encodeCertificate M0GCWireFormat.canaryCertificate ++ [0]) =
        some region) :
    execute configuration region = false := by
  rw [execute_eq_reference]
  unfold referenceCheck
  unfold Loader.execute
  rw [M0GCWordLoaderControlMachine.trailing_machine_rejected
    region compiled]

end Canary

#print axioms transition_deterministic
#print axioms runSteps_seven_halts
#print axioms execute_eq_reference
#print axioms execute_compiled_refines_cCoreCheckBytes
#print axioms execute_ofCandidate_sound
#print axioms execute_compiled_ofCandidate_sound
#print axioms Canary.pair_combined_machine_accepts
#print axioms Canary.wrong_claim_combined_machine_rejected
#print axioms Canary.wrong_checksum_combined_machine_rejected
#print axioms Canary.trailing_combined_machine_rejected

end Mettapedia.GSLT.LanguageDef.M0GCWordCheckerBoundaryMachine
