import Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory

/-!
# Small-step control machine for the M0GC word loader

This module factors the complete finite-word certificate loader into an
explicit sequence of control states.  The purpose is to give future Pancake
and Clight realizations one shared transition contract and one terminal
observation, rather than letting each backend invent its own orchestration.

This is a fully connected intermediate proof of concept.  The state
constructors retain decoded Lean values for proof clarity; they are not an
endgame ABI, optimized register allocation, mutable heap model, file-I/O
semantics, Pancake program, Clight program, compiler proof, or machine-code
semantics.  The machine currently refines certificate loading only.  Logical
replay remains qualified separately by the M0GC core-loop correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine

open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.WordRegion

/-! ## Explicit control states -/

/-- Administrative states of the finite-word certificate loader.  Each
constructor records exactly the values made available to the next phase. -/
inductive ControlState where
  | loadHeader
  | compileLayout (header : Header)
  | loadBody (header : Header) (counts : BodyCounts)
      (layout : BodyLayout)
  | loadTables (header : Header) (counts : BodyCounts)
      (bodyBytes : List UInt8)
  | checkChecksum (header : Header) (bodyBytes : List UInt8)
      (tables : BodyTables)
  | halt (result : Option Certificate)

/-- A halted state exposes an accept/reject result.  A running state has no
terminal observation yet. -/
def observe : ControlState → Option (Option Certificate)
  | .halt result => some result
  | _ => none

/-- One deterministic control transition.  Halting states stutter, making a
fixed-step runner convenient without changing their observation. -/
def step (region : WordRegion) : ControlState → ControlState
  | .loadHeader =>
      match region.readHeader? with
      | none => .halt none
      | some header => .compileLayout header
  | .compileLayout header =>
      let counts := BodyCounts.ofHeader header
      match BodyLayout.ofCounts? counts with
      | none => .halt none
      | some layout => .loadBody header counts layout
  | .loadBody header counts layout =>
      match region.loadBytes? 104 layout.bodyWidth with
      | none => .halt none
      | some bodyBytes => .loadTables header counts bodyBytes
  | .loadTables header counts bodyBytes =>
      match region.readBodyAt? counts 104 with
      | none => .halt none
      | some tables => .checkChecksum header bodyBytes tables
  | .checkChecksum header bodyBytes tables =>
      if header.bodyChecksum = fnv1a64 bodyBytes then
        .halt (some (certificateOfTables header tables))
      else
        .halt none
  | .halt result => .halt result

/-- Relational presentation used by later forward simulations. -/
def Transition (region : WordRegion)
    (before after : ControlState) : Prop :=
  step region before = after

/-- The transition relation is deterministic. -/
theorem transition_deterministic (region : WordRegion)
    {before afterLeft afterRight : ControlState}
    (left : Transition region before afterLeft)
    (right : Transition region before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (region : WordRegion)
    (result : Option Certificate) :
    step region (.halt result) = .halt result := rfl

/-- A terminal observation cannot be changed by another transition. -/
theorem halt_transition_eq (region : WordRegion)
    (result : Option Certificate) {after : ControlState}
    (transition : Transition region (.halt result) after) :
    after = .halt result := by
  exact transition.symm

/-! ## Fixed-step execution -/

/-- Execute exactly `fuel` transitions.  Terminal states stutter. -/
def runSteps (region : WordRegion) : Nat → ControlState → ControlState
  | 0, state => state
  | fuel + 1, state => runSteps region fuel (step region state)

@[simp] theorem runSteps_halt (region : WordRegion)
    (fuel : Nat) (result : Option Certificate) :
    runSteps region fuel (.halt result) = .halt result := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [runSteps, inductionHypothesis]

/-- Five transitions suffice: header, layout, raw body, typed tables, and
checksum.  Earlier rejection merely stutters for the remaining transitions. -/
theorem runSteps_five_halts (region : WordRegion) :
    ∃ result, runSteps region 5 .loadHeader = .halt result := by
  cases headerResult : region.readHeader? with
  | none =>
      exact ⟨none, by simp [runSteps, step, headerResult]⟩
  | some header =>
      let counts := BodyCounts.ofHeader header
      cases layoutResult : BodyLayout.ofCounts? counts with
      | none =>
          exact ⟨none, by simp [runSteps, step, headerResult,
            counts, layoutResult]⟩
      | some layout =>
          cases bodyResult : region.loadBytes? 104 layout.bodyWidth with
          | none =>
              exact ⟨none, by simp [runSteps, step, headerResult,
                counts, layoutResult, bodyResult]⟩
          | some bodyBytes =>
              cases tablesResult : region.readBodyAt? counts 104 with
              | none =>
                  exact ⟨none, by simp [runSteps, step, headerResult,
                    counts, layoutResult, bodyResult, tablesResult]⟩
              | some tables =>
                  by_cases checksumMatches :
                      header.bodyChecksum = fnv1a64 bodyBytes
                  · exact ⟨some (certificateOfTables header tables),
                      by simp [runSteps, step, headerResult, counts,
                        layoutResult, bodyResult, tablesResult,
                        checksumMatches]⟩
                  · exact ⟨none, by simp [runSteps, step, headerResult,
                      counts, layoutResult, bodyResult, tablesResult,
                      checksumMatches]⟩

/-- Terminal result after the statically sufficient five control steps. -/
def execute (region : WordRegion) : Option Certificate :=
  match runSteps region 5 .loadHeader with
  | .halt result => result
  | _ => none

/-- The explicit-state control machine has exactly the complete immutable
word loader's accept/reject behavior on every admitted region. -/
theorem execute_eq_readCertificate? (region : WordRegion) :
    execute region = region.readCertificate? := by
  unfold execute WordRegion.readCertificate?
  cases headerResult : region.readHeader? with
  | none =>
      simp [runSteps, step, headerResult]
  | some header =>
      let counts := BodyCounts.ofHeader header
      cases layoutResult : BodyLayout.ofCounts? counts with
      | none =>
          simp [runSteps, step, headerResult, counts, layoutResult]
      | some layout =>
          cases bodyResult : region.loadBytes? 104 layout.bodyWidth with
          | none =>
              simp [runSteps, step, headerResult, counts, layoutResult,
                bodyResult]
          | some bodyBytes =>
              cases tablesResult : region.readBodyAt? counts 104 with
              | none =>
                  simp [runSteps, step, headerResult, counts, layoutResult,
                    bodyResult, tablesResult]
              | some tables =>
                  by_cases checksumMatches :
                      header.bodyChecksum = fnv1a64 bodyBytes
                  · simp [runSteps, step, headerResult, counts,
                      layoutResult, bodyResult, tablesResult,
                      checksumMatches]
                  · simp [runSteps, step, headerResult, counts,
                      layoutResult, bodyResult, tablesResult,
                      checksumMatches]

/-! ## Source-byte transport and discriminators -/

/-- Successful finite-word compilation transports the control machine to the
proved flat certificate loader. -/
theorem execute_ofList? (bytes : List UInt8) (region : WordRegion)
    (compiled : WordRegion.ofList? bytes = some region) :
    execute region = readCertificateFlat? bytes := by
  rw [execute_eq_readCertificate?]
  exact WordRegion.readCertificate?_ofList? bytes region compiled

/-- Every encodable certificate accepted by the finite-word constructor is
accepted by the control machine. -/
theorem execute_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable)
    (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate certificate) = some region) :
    execute region = some certificate := by
  rw [execute_eq_readCertificate?]
  exact WordRegion.readCertificate?_encodeCertificate
    certificate encodable region compiled

/-- Positive discriminator: the canonical nontrivial certificate reaches an
accepting halt whenever its finite-word region is admitted. -/
theorem canary_machine_accepts (region : WordRegion)
    (compiled :
      WordRegion.ofList? (encodeCertificate canaryCertificate) =
        some region) :
    execute region = some canaryCertificate := by
  exact execute_encodeCertificate
    canaryCertificate canaryCertificate_encodable region compiled

/-- Negative discriminator: checksum corruption reaches a rejecting halt. -/
theorem wrong_checksum_machine_rejected (region : WordRegion)
    (compiled : WordRegion.ofList? wrongChecksumCanary = some region) :
    execute region = none := by
  rw [execute_eq_readCertificate?]
  exact WordRegion.wrong_checksum_word_certificate_rejected region compiled

/-- Negative discriminator: an extra byte remains observable and reaches a
rejecting halt. -/
theorem trailing_machine_rejected (region : WordRegion)
    (compiled :
      WordRegion.ofList?
          (encodeCertificate canaryCertificate ++ [0]) = some region) :
    execute region = none := by
  rw [execute_eq_readCertificate?]
  exact WordRegion.trailing_word_certificate_rejected region compiled

#print axioms transition_deterministic
#print axioms halt_transition_eq
#print axioms runSteps_five_halts
#print axioms execute_eq_readCertificate?
#print axioms execute_ofList?
#print axioms execute_encodeCertificate
#print axioms canary_machine_accepts
#print axioms wrong_checksum_machine_rejected
#print axioms trailing_machine_rejected

end Mettapedia.GSLT.LanguageDef.M0GCWordLoaderControlMachine
