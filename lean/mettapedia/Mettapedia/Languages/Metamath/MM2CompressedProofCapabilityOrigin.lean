import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation

/-!
# Executable capability origin for compressed Metamath verification

Compressed verification stores executable MM2 rules inside inert carrier rows
and republishes them at scanner, lookup, and assertion boundaries.  This module
uses the generic reflective capture interface to distinguish those carrier
values from ordinary source data and retains the carrier family and kind as
part of the authorization decision.

The inventory is supplied by the admitted verifier presentation.  Source proof
data may contain rows with many other heads, but it cannot authorize a carrier
merely by containing an executable payload with a familiar shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Exact carrier decoder -/

inductive CompressedExecutableCarrierFamily where
  | runtime
  | lookup
  | speculative
deriving DecidableEq, Repr

structure CompressedExecutableCapture where
  family : CompressedExecutableCarrierFamily
  kind : String
  payload : Atom
deriving DecidableEq, Repr

def encodeCompressedExecutableCapture
    (capture : CompressedExecutableCapture) : Atom :=
  let head :=
    match capture.family with
    | .runtime => "mm-compressed-owned-runtime-rule"
    | .lookup => "mm-compressed-owned-lookup-handler"
    | .speculative => "mm-compressed-owned-speculative-lookup-handler"
  .expression [.symbol head, .symbol capture.kind, capture.payload]

/-- Decode precisely the inert carrier shapes from which compressed-verifier
rules may later be republished. -/
def decodeCompressedExecutableCapture : Atom → Option CompressedExecutableCapture
  | .expression
      [.symbol "mm-compressed-owned-runtime-rule", .symbol kind, payload] =>
      some ⟨.runtime, kind, payload⟩
  | .expression
      [.symbol "mm-compressed-owned-lookup-handler", .symbol kind, payload] =>
      some ⟨.lookup, kind, payload⟩
  | .expression
      [.symbol "mm-compressed-owned-speculative-lookup-handler",
        .symbol kind, payload] =>
      some ⟨.speculative, kind, payload⟩
  | _ => none

@[simp] theorem decode_encodeCompressedExecutableCapture
    (capture : CompressedExecutableCapture) :
    decodeCompressedExecutableCapture
      (encodeCompressedExecutableCapture capture) = some capture := by
  cases capture with
  | mk family kind payload =>
      cases family <;>
        simp [encodeCompressedExecutableCapture,
          decodeCompressedExecutableCapture]

theorem encodeCompressedExecutableCapture_injective :
    Function.Injective encodeCompressedExecutableCapture := by
  intro left right equal
  have decoded := congrArg decodeCompressedExecutableCapture equal
  simpa using decoded

@[simp] theorem encodeCompressedExecutableCapture_isDynamic_false
    (capture : CompressedExecutableCapture) :
    MM2CompressedProofContinuousRepresentation.isDynamicRow
      (encodeCompressedExecutableCapture capture) = false := by
  rcases capture with ⟨family, kind, payload⟩
  cases family <;>
    simp [encodeCompressedExecutableCapture,
      MM2CompressedProofContinuousRepresentation.isDynamicRow,
      MM2CompressedProofContinuousRepresentation.dynamicRowHeads]

/-- Proof-relevant view of one executable value captured by an inert carrier.
The family and kind are retained existentially so later inversion cannot
silently exchange two distinct continuation roles. -/
def CompressedExecutableCaptureOf (carrier payload : Atom) : Prop :=
  ∃ family kind,
    decodeCompressedExecutableCapture carrier =
      some ⟨family, kind, payload⟩

theorem compressedExecutableCaptureOf_iff_decode
    (carrier payload : Atom) :
    CompressedExecutableCaptureOf carrier payload ↔
      ∃ family kind,
        decodeCompressedExecutableCapture carrier =
          some ⟨family, kind, payload⟩ := by
  rfl

/-! ## Presentation-indexed authority -/

/-- An admitted presentation assigns at most one executable value to every
carrier family and continuation kind.  Compiler transformations construct a
new resolver from their selected target rules instead of inheriting authority
from source data. -/
structure CompressedExecutablePresentation where
  resolve : CompressedExecutableCarrierFamily → String → Option Atom

/-- A carrier is authorized exactly when the admitted presentation resolves
its full family and kind to the captured payload.  Ordinary non-carrier rows
satisfy the predicate without acquiring executable authority. -/
def CompressedExecutableCarrierAuthorized
    (presentation : CompressedExecutablePresentation) (carrier : Atom) : Prop :=
  match decodeCompressedExecutableCapture carrier with
  | none => True
  | some capture =>
      presentation.resolve capture.family capture.kind = some capture.payload

def CompressedExecutableCapabilities
    (presentation : CompressedExecutablePresentation)
    (space : List Atom) : Prop :=
  AtomsWithin (CompressedExecutableCarrierAuthorized presentation) space

theorem compressedExecutableCapabilities_iff_captured
    (presentation : CompressedExecutablePresentation) (space : List Atom) :
    CompressedExecutableCapabilities presentation space ↔
      ∀ carrier ∈ space, ∀ payload,
        CompressedExecutableCaptureOf carrier payload →
          ∃ family kind,
            decodeCompressedExecutableCapture carrier =
                some ⟨family, kind, payload⟩ ∧
              presentation.resolve family kind = some payload := by
  constructor
  · intro within carrier member payload captured
    have authorized := within carrier member
    rcases (compressedExecutableCaptureOf_iff_decode carrier payload).1 captured
      with ⟨family, kind, decoded⟩
    exact ⟨family, kind, decoded, by
      simpa [CompressedExecutableCarrierAuthorized, decoded] using authorized⟩
  · intro origin carrier member
    unfold CompressedExecutableCarrierAuthorized
    cases decoded : decodeCompressedExecutableCapture carrier with
    | none => trivial
    | some capture =>
        rcases capture with ⟨family, kind, payload⟩
        obtain ⟨resolvedFamily, resolvedKind, decodedAgain, resolved⟩ :=
          origin carrier member payload
            ((compressedExecutableCaptureOf_iff_decode carrier payload).2
              ⟨family, kind, decoded⟩)
        have captureEqual := Option.some.inj (decoded.symm.trans decodedAgain)
        cases captureEqual
        exact resolved

theorem CompressedExecutableCapabilities.capture_origin
    {presentation : CompressedExecutablePresentation} {space : List Atom}
    (capabilities : CompressedExecutableCapabilities presentation space)
    {carrier payload : Atom} (member : carrier ∈ space)
    (captured : CompressedExecutableCaptureOf carrier payload) :
    ∃ family kind,
      decodeCompressedExecutableCapture carrier =
          some ⟨family, kind, payload⟩ ∧
        presentation.resolve family kind = some payload := by
  exact
    (compressedExecutableCapabilities_iff_captured presentation space).1
      capabilities carrier member payload captured

theorem CompressedExecutablePresentation.capture_exact
    (presentation : CompressedExecutablePresentation)
    {family : CompressedExecutableCarrierFamily} {kind : String}
    {expected actual : Atom}
    (expectedResolved : presentation.resolve family kind = some expected)
    (actualResolved : presentation.resolve family kind = some actual) :
    actual = expected := by
  exact Option.some.inj (actualResolved.symm.trans expectedResolved)

/-- Exact typed base inventory.  Keeping the key beside the payload makes the
compiler-side authority map explicit before it is rendered as MM2 rows. -/
def compressedBaseExecutableCaptures : List CompressedExecutableCapture :=
  [⟨.runtime, "prefix", compressedPrefixRule⟩,
   ⟨.runtime, "terminal", compressedTerminalRule⟩,
   ⟨.runtime, "proof", compressedProofStepRule⟩,
   ⟨.runtime, "assertion-launch", compressedAssertionLaunchRule⟩,
   ⟨.runtime, "lookup-fault", compressedHeapLookupFaultRule⟩,
   ⟨.runtime, "lookup-advance", compressedHeapLookupAdvanceRule⟩,
   ⟨.runtime, "save", compressedSaveRule⟩,
   ⟨.runtime, "word-advance", compressedWordAdvanceRule⟩,
   ⟨.runtime, "accept", compressedAcceptRule⟩,
   ⟨.runtime, "incomplete", compressedIncompleteRule⟩,
   ⟨.runtime, "invalid-byte", compressedInvalidByteRule⟩,
   ⟨.runtime, "question", compressedQuestionRule⟩,
   ⟨.runtime, "question-open-fault", compressedQuestionOpenFaultRule⟩,
   ⟨.runtime, "save-fault", compressedSaveFaultRule⟩,
   ⟨.lookup, "proof", compressedProofStepRule⟩,
   ⟨.lookup, "assertion", compressedAssertionLaunchRule⟩,
   ⟨.lookup, "fault", compressedHeapLookupFaultRule⟩,
   ⟨.runtime, "assertion-rejoin", compressedAssertionRejoinRule⟩,
   ⟨.runtime, "assertion-resume", compressedAssertionResumeRule⟩]

/-- Exact base presentation inventory rendered as inert MM2 rows. -/
def compressedBaseExecutableCaptureRows : List Atom :=
  compressedBaseExecutableCaptures.map encodeCompressedExecutableCapture

theorem compressedBaseExecutableCaptureRows_eq_existing :
    compressedBaseExecutableCaptureRows =
      compressedScannerRuleCaptureRows ++ compressedHeapLookupReloadRows ++
        compressedAssertionContinuationCaptureRows := by
  rfl

def compressedBaseExecutableRule? :
    CompressedExecutableCarrierFamily → String → Option Atom
  | .runtime, "prefix" => some compressedPrefixRule
  | .runtime, "terminal" => some compressedTerminalRule
  | .runtime, "proof" => some compressedProofStepRule
  | .runtime, "assertion-launch" => some compressedAssertionLaunchRule
  | .runtime, "lookup-fault" => some compressedHeapLookupFaultRule
  | .runtime, "lookup-advance" => some compressedHeapLookupAdvanceRule
  | .runtime, "save" => some compressedSaveRule
  | .runtime, "word-advance" => some compressedWordAdvanceRule
  | .runtime, "accept" => some compressedAcceptRule
  | .runtime, "incomplete" => some compressedIncompleteRule
  | .runtime, "invalid-byte" => some compressedInvalidByteRule
  | .runtime, "question" => some compressedQuestionRule
  | .runtime, "question-open-fault" => some compressedQuestionOpenFaultRule
  | .runtime, "save-fault" => some compressedSaveFaultRule
  | .runtime, "assertion-rejoin" => some compressedAssertionRejoinRule
  | .runtime, "assertion-resume" => some compressedAssertionResumeRule
  | .lookup, "proof" => some compressedProofStepRule
  | .lookup, "assertion" => some compressedAssertionLaunchRule
  | .lookup, "fault" => some compressedHeapLookupFaultRule
  | _, _ => none

def compressedBaseExecutablePresentation : CompressedExecutablePresentation where
  resolve := compressedBaseExecutableRule?

theorem compressedBaseExecutableCaptureRows_authorized :
    CompressedExecutableCapabilities compressedBaseExecutablePresentation
      compressedBaseExecutableCaptureRows := by
  intro carrier member
  rw [compressedBaseExecutableCaptureRows, List.mem_map] at member
  obtain ⟨capture, captureMember, rfl⟩ := member
  simp only [CompressedExecutableCarrierAuthorized,
    decode_encodeCompressedExecutableCapture]
  rcases capture with ⟨family, kind, payload⟩
  simp only [compressedBaseExecutableCaptures, List.mem_cons,
    List.not_mem_nil, or_false] at captureMember
  rcases captureMember with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h
  all_goals cases h
  all_goals rfl

/-- Positive control: the base save continuation is admitted with its exact
runtime kind and payload. -/
theorem base_save_capture_authorized :
    CompressedExecutableCarrierAuthorized compressedBaseExecutablePresentation
      (compressedOwnedRuntimeRuleRow "save" compressedSaveRule) := by
  simp [CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, compressedOwnedRuntimeRuleRow,
    compressedBaseExecutablePresentation, compressedBaseExecutableRule?]

private def swappedPrefixTerminalCarrier : Atom :=
  compressedOwnedRuntimeRuleRow "prefix" compressedTerminalRule

/-- Negative control: an executable payload from the verifier is not enough;
placing it under the wrong continuation kind is rejected. -/
theorem swapped_prefix_terminal_capture_rejected :
    ¬ CompressedExecutableCarrierAuthorized
      compressedBaseExecutablePresentation swappedPrefixTerminalCarrier := by
  have rulesDistinct : compressedTerminalRule ≠ compressedPrefixRule := by
    decide +kernel
  simp [CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, swappedPrefixTerminalCarrier,
    compressedOwnedRuntimeRuleRow, compressedBaseExecutablePresentation,
    compressedBaseExecutableRule?, rulesDistinct.symm]

section AxiomAudit

#print axioms compressedExecutableCaptureOf_iff_decode
#print axioms encodeCompressedExecutableCapture_isDynamic_false
#print axioms compressedExecutableCapabilities_iff_captured
#print axioms CompressedExecutableCapabilities.capture_origin
#print axioms CompressedExecutablePresentation.capture_exact
#print axioms compressedBaseExecutablePresentation
#print axioms compressedBaseExecutableCaptureRows_eq_existing
#print axioms compressedBaseExecutableCaptureRows_authorized
#print axioms base_save_capture_authorized
#print axioms swapped_prefix_terminal_capture_rejected

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
