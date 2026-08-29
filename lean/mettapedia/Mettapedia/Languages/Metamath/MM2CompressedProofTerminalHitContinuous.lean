import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation

/-!
# Continuous transformed-terminal to compressed proof-hit boundary

This module begins the concrete public-boundary segment for one compressed
proof reference.  It exposes the exact generated speculative-terminal input
and output interfaces and constructs its canonical source-derived match
space.  The following module-level obligation is to identify the fired
successor with a direct proof-request frame and compose the two scheduled
steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofTerminalHitContinuous

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Exact generated terminal surface -/

private def terminalSelfPattern : Atom :=
  .expression
    [.symbol "exec", speculativeTerminalDirective.loc,
      .var "terminal-input", .var "terminal-output"]

private def terminalScanPattern : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression
        [.symbol "mm-cons", .var "compressed-byte",
          .var "remaining-bytes"],
      .var "compressed-phase", .var "reverse-prefix"]

private def terminalClassPattern : Atom :=
  .expression
    [.symbol "mm-compressed-terminal-byte", .var "compressed-byte",
      .var "terminal-digit"]

private def terminalOwnedRulePattern (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

private def terminalDirectHandlerPattern
    (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler", .symbol kind,
      .var variableName]

private def terminalPatterns : List Atom :=
  [terminalSelfPattern, terminalScanPattern, terminalClassPattern,
   terminalOwnedRulePattern "proof" "compressed-proof-rule",
   terminalOwnedRulePattern "assertion-launch"
     "compressed-assertion-launch-rule",
   terminalOwnedRulePattern "lookup-fault" "compressed-lookup-fault-rule",
   terminalOwnedRulePattern "lookup-advance" "compressed-lookup-advance-rule",
   terminalDirectHandlerPattern "proof" "compressed-direct-proof-handler",
   terminalDirectHandlerPattern "assertion"
     "compressed-direct-assertion-handler"]

private def terminalPendingPattern : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]

private def terminalLookupPattern : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"],
      (CompressedIndexCode.ofNat 0).atom]

private def terminalSinks : List Sink :=
  [.remove terminalScanPattern,
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-assertion-launch-rule"),
   .add (.var "compressed-lookup-fault-rule"),
   .add (.var "compressed-lookup-advance-rule"),
   .add terminalPendingPattern,
   .add terminalLookupPattern,
   .add (.var "compressed-direct-proof-handler"),
   .add (.var "compressed-direct-assertion-handler")]

private def terminalSinkSurface : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

private def terminalInputSurface : Atom :=
  .expression (.symbol "," :: terminalPatterns)

private def terminalOutputSurface : Atom :=
  .expression (.symbol "O" :: terminalSinks.map terminalSinkSurface)

/-- The transformed terminal consumes exactly the ordinary scanner premises
plus the two generated direct-handler captures. -/
theorem speculative_terminal_input_exact :
    speculativeTerminalDirective.rule.input =
      .compat (mkPattern terminalPatterns) := by
  decide +kernel

/-- Exact output surface of the transformed terminal. -/
theorem speculative_terminal_sinks_exact :
    speculativeTerminalDirective.rule.tmpl.sinks = terminalSinks := by
  decide +kernel

/-- The extracted directive retains the physical executable shell of the
generated terminal rule. -/
theorem speculative_terminal_atom_surface :
    speculativeTerminalDirective.atom =
      .expression
        [.symbol "exec", speculativeTerminalDirective.loc,
          terminalInputSurface, terminalOutputSurface] := by
  decide +kernel

/-! ## Canonical source-derived match space -/

def terminalClassRow (occurrence : ByteOccurrence) : Atom :=
  compressedTerminalByteRow occurrence.byte.toNat
    (occurrence.byte.toNat - 65)

def terminalRuntimeCaptureRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "assertion-launch"
     compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "lookup-fault"
     compressedHeapLookupFaultRule,
   compressedOwnedRuntimeRuleRow "lookup-advance"
     compressedHeapLookupAdvanceRule,
   compressedDirectProofHandlerRow,
   compressedDirectAssertionHandlerRow]

/-- Minimal list on which the transformed terminal has all of its premises.
The scanner row and class row come from the same source byte occurrence. -/
def canonicalTerminalMatchSpace (context : BoundaryContext)
    (before : ScannerBoundary) (occurrence : ByteOccurrence) : List Atom :=
  [speculativeTerminalDirective.atom, scannerRow context before,
    terminalClassRow occurrence] ++ terminalRuntimeCaptureRows

/-- The minimal transformed-terminal space exposes exactly one executable
scheduler candidate.  Opaque capture rows cannot be mistaken for rules. -/
theorem canonicalTerminalMatchSpace_supported_exact
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    cSupportedSourceExecFacts
        (canonicalTerminalMatchSpace context before occurrence) =
      [speculativeTerminalDirective] := by
  rfl

theorem canonicalTerminalMatchSpace_selects_terminal
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (canonicalTerminalMatchSpace context before occurrence)) =
      some speculativeTerminalDirective := by
  rw [canonicalTerminalMatchSpace_supported_exact]
  rfl

/-- The generated transformed terminal performs one concrete non-reflexive
list-machine scheduler step on its canonical source-derived surface. -/
theorem canonicalTerminalMatchSpace_steps
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (canonicalTerminalMatchSpace context before occurrence) =
      some
        (cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective) := by
  unfold cReflectiveSourceWorkQueueStep
  rw [canonicalTerminalMatchSpace_selects_terminal]

/-- The concrete terminal step itself inhabits the exact OSLF native target
type generated from the executable reflective MM2 GSLT. -/
theorem canonicalTerminalMatchSpace_inhabits_exact_native_type
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies
        (canonicalTerminalMatchSpace context before occurrence)
        (reflectiveNativeListExactTargetNativeType .leaveInert
          (cFireReflectiveSourceExecFact
            (canonicalTerminalMatchSpace context before occurrence)
            speculativeTerminalDirective)).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert _ _).2
  exact canonicalTerminalMatchSpace_steps context before occurrence

/-! ## Symbolic terminal matcher -/

private def terminalSelfInput : Atom :=
  match speculativeTerminalDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-terminal-input"

private def terminalSelfOutput : Atom :=
  match speculativeTerminalDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-terminal-output"

private def terminalSelfSubst : Subst :=
  [("terminal-output", terminalSelfOutput),
   ("terminal-input", terminalSelfInput)]

private def terminalScanSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("reverse-prefix", listAtom natAtom before.phase.reversePrefix),
   ("compressed-phase", before.phase.atom),
   ("remaining-bytes",
      listAtom natAtom (after.remainingBytes.map UInt8.toNat)),
   ("compressed-byte", natAtom occurrence.byte.toNat),
   ("word-position", natAtom before.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ terminalSelfSubst

private def terminalClassSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("terminal-digit", natAtom (occurrence.byte.toNat - 65))] ++
    terminalScanSubst context before after occurrence

private def terminalProofSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-proof-rule", compressedProofStepRule)] ++
    terminalClassSubst context before after occurrence

private def terminalAssertionSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-assertion-launch-rule", compressedAssertionLaunchRule)] ++
    terminalProofSubst context before after occurrence

private def terminalFaultSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-lookup-fault-rule", compressedHeapLookupFaultRule)] ++
    terminalAssertionSubst context before after occurrence

private def terminalAdvanceSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-lookup-advance-rule", compressedHeapLookupAdvanceRule)] ++
    terminalFaultSubst context before after occurrence

private def terminalDirectProofSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-direct-proof-handler", compressedDirectProofRule)] ++
    terminalAdvanceSubst context before after occurrence

private def terminalFinalSubst (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Subst :=
  [("compressed-direct-assertion-handler", compressedDirectAssertionRule)] ++
    terminalDirectProofSubst context before after occurrence

private theorem terminalSelf_match :
    Conformance.Computable.cmatchAtom [] terminalSelfPattern
      speculativeTerminalDirective.atom = some terminalSelfSubst := by
  decide +kernel

private theorem terminalScan_match
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    Conformance.Computable.cmatchAtom terminalSelfSubst terminalScanPattern
      (scannerRow context before) =
        some (terminalScanSubst context before after occurrence) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases before with
    ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  rcases after with
    ⟨nextWordPosition, nextBytePosition, nextRemainingBytes, nextPhase⟩
  rcases occurrence with ⟨occurrenceOwner, occurrencePosition, byte⟩
  have headExact : remainingBytes = byte :: nextRemainingBytes :=
    receipt.consumes_head
  subst remainingBytes
  cases phase <;>
    simp [terminalScanSubst, terminalSelfSubst, terminalScanPattern,
      scannerRow, listAtom, consTag, natAtom,
      Conformance.Computable.cmatchAtom,
      Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalClass_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalScanSubst context before after occurrence)
        terminalClassPattern (terminalClassRow occurrence) =
      some (terminalClassSubst context before after occurrence) := by
  cases context
  cases before
  cases after
  cases occurrence
  simp [terminalClassSubst, terminalScanSubst, terminalSelfSubst,
    terminalClassPattern, terminalClassRow, compressedTerminalByteRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalProof_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalClassSubst context before after occurrence)
        (terminalOwnedRulePattern "proof" "compressed-proof-rule")
        (compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule) =
      some (terminalProofSubst context before after occurrence) := by
  simp [terminalProofSubst, terminalClassSubst, terminalScanSubst,
    terminalSelfSubst, terminalOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalAssertion_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalProofSubst context before after occurrence)
        (terminalOwnedRulePattern "assertion-launch"
          "compressed-assertion-launch-rule")
        (compressedOwnedRuntimeRuleRow "assertion-launch"
          compressedAssertionLaunchRule) =
      some (terminalAssertionSubst context before after occurrence) := by
  simp [terminalAssertionSubst, terminalProofSubst, terminalClassSubst,
    terminalScanSubst, terminalSelfSubst, terminalOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalFault_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalAssertionSubst context before after occurrence)
        (terminalOwnedRulePattern "lookup-fault"
          "compressed-lookup-fault-rule")
        (compressedOwnedRuntimeRuleRow "lookup-fault"
          compressedHeapLookupFaultRule) =
      some (terminalFaultSubst context before after occurrence) := by
  simp [terminalFaultSubst, terminalAssertionSubst, terminalProofSubst,
    terminalClassSubst, terminalScanSubst, terminalSelfSubst,
    terminalOwnedRulePattern, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalAdvance_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalFaultSubst context before after occurrence)
        (terminalOwnedRulePattern "lookup-advance"
          "compressed-lookup-advance-rule")
        (compressedOwnedRuntimeRuleRow "lookup-advance"
          compressedHeapLookupAdvanceRule) =
      some (terminalAdvanceSubst context before after occurrence) := by
  simp [terminalAdvanceSubst, terminalFaultSubst, terminalAssertionSubst,
    terminalProofSubst, terminalClassSubst, terminalScanSubst,
    terminalSelfSubst, terminalOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalDirectProof_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalAdvanceSubst context before after occurrence)
        (terminalDirectHandlerPattern "proof"
          "compressed-direct-proof-handler")
        compressedDirectProofHandlerRow =
      some (terminalDirectProofSubst context before after occurrence) := by
  simp [terminalDirectProofSubst, terminalAdvanceSubst, terminalFaultSubst,
    terminalAssertionSubst, terminalProofSubst, terminalClassSubst,
    terminalScanSubst, terminalSelfSubst, terminalDirectHandlerPattern,
    compressedDirectProofHandlerRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem terminalDirectAssertion_match
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    Conformance.Computable.cmatchAtom
        (terminalDirectProofSubst context before after occurrence)
        (terminalDirectHandlerPattern "assertion"
          "compressed-direct-assertion-handler")
        compressedDirectAssertionHandlerRow =
      some (terminalFinalSubst context before after occurrence) := by
  simp [terminalFinalSubst, terminalDirectProofSubst, terminalAdvanceSubst,
    terminalFaultSubst, terminalAssertionSubst, terminalProofSubst,
    terminalClassSubst, terminalScanSubst, terminalSelfSubst,
    terminalDirectHandlerPattern, compressedDirectAssertionHandlerRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem cmatchPattern_go_cons_of_selected
    {space : List Atom} {pattern : Atom} {patterns : List Atom}
    {substitutionIn substitutionMid substitutionOut : Subst}
    {consumedIn consumedOut : List Atom} {concrete : Atom}
    (present : concrete ∈ space)
    (matched : Conformance.Computable.cmatchAtom substitutionIn pattern
      concrete = some substitutionMid)
    (continued : (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space patterns substitutionMid
        (concrete :: consumedIn)) :
    (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space (pattern :: patterns)
        substitutionIn consumedIn := by
  simp only [Conformance.Computable.cmatchPattern.go, List.mem_flatMap]
  refine ⟨(substitutionMid, concrete), ?_, continued⟩
  rw [List.mem_filterMap]
  exact ⟨concrete, present, by rw [matched]; rfl⟩

private def canonicalTerminalConsumed (context : BoundaryContext)
    (before : ScannerBoundary) (occurrence : ByteOccurrence) : List Atom :=
  [compressedDirectAssertionHandlerRow, compressedDirectProofHandlerRow,
   compressedOwnedRuntimeRuleRow "lookup-advance"
     compressedHeapLookupAdvanceRule,
   compressedOwnedRuntimeRuleRow "lookup-fault" compressedHeapLookupFaultRule,
   compressedOwnedRuntimeRuleRow "assertion-launch"
     compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   terminalClassRow occurrence, scannerRow context before,
   speculativeTerminalDirective.atom]

/-- The scheduled terminal is not merely selected: its canonical nine-row
surface has a genuine, source-parameterized matcher substitution. -/
theorem canonicalTerminalMatchSpace_has_match
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    (terminalFinalSubst context before after occurrence,
      canonicalTerminalConsumed context before occurrence) ∈
      Conformance.Computable.cmatchInputSpec []
        (canonicalTerminalMatchSpace context before occurrence)
        speculativeTerminalDirective.rule.input := by
  rw [speculative_terminal_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern]
  unfold terminalPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := speculativeTerminalDirective.atom)
  · simp [canonicalTerminalMatchSpace]
  · exact terminalSelf_match
  apply cmatchPattern_go_cons_of_selected
    (concrete := scannerRow context before)
  · simp [canonicalTerminalMatchSpace]
  · exact terminalScan_match receipt
  apply cmatchPattern_go_cons_of_selected
    (concrete := terminalClassRow occurrence)
  · simp [canonicalTerminalMatchSpace]
  · exact terminalClass_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalProof_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "assertion-launch"
      compressedAssertionLaunchRule)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalAssertion_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "lookup-fault"
      compressedHeapLookupFaultRule)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalFault_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "lookup-advance"
      compressedHeapLookupAdvanceRule)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalAdvance_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedDirectProofHandlerRow)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalDirectProof_match context before after occurrence
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedDirectAssertionHandlerRow)
  · simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows]
  · exact terminalDirectAssertion_match context before after occurrence
  simp [Conformance.Computable.cmatchPattern.go, canonicalTerminalConsumed]

def terminalPendingRow (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", context.scopeOwner,
      context.proofOwner, natAtom before.wordPosition,
      listAtom natAtom (after.remainingBytes.map UInt8.toNat),
      (proofByteCode before occurrence).atom]

def terminalLookupRow (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", context.scopeOwner,
      context.proofOwner, natAtom before.wordPosition,
      listAtom natAtom (after.remainingBytes.map UInt8.toNat),
      (proofByteCode before occurrence).atom,
      (CompressedIndexCode.ofNat 0).atom]

/-- The source-derived terminal substitution produces exactly the two lookup
rows and two direct-handler shells required by the following phase. -/
theorem terminalFinalSubst_instantiates_request
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        terminalPendingPattern =
          some (terminalPendingRow context before after occurrence) ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        terminalLookupPattern =
          some (terminalLookupRow context before after occurrence) ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-direct-proof-handler") =
          some compressedDirectProofRule ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-direct-assertion-handler") =
          some compressedDirectAssertionRule := by
  cases context
  cases before
  cases after
  cases occurrence
  simp [terminalPendingRow, terminalLookupRow, proofByteCode,
    terminalFinalSubst, terminalDirectProofSubst, terminalAdvanceSubst,
    terminalFaultSubst, terminalAssertionSubst, terminalProofSubst,
    terminalClassSubst, terminalScanSubst, terminalSelfSubst,
    terminalPendingPattern, terminalLookupPattern,
    instantiateTemplateAtom?, templateCovered, templatesCovered,
    applySubst, applySubst.applySubstList, Subst.lookup,
    CompressedIndexCode.atom, CompressedIndexCode.ofNat,
    CompressedIndexCode.zero, compressedIndexCodeAtom, listAtom, natAtom,
    nilTag, natTag]

/-- The work-queue firing read reconstructs the canonical terminal space after
removing and re-prepending its unique scheduler shell. -/
theorem canonicalTerminalMatchSpace_read_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    speculativeTerminalDirective.atom ::
        (canonicalTerminalMatchSpace context before occurrence).erase
          speculativeTerminalDirective.atom =
      canonicalTerminalMatchSpace context before occurrence := by
  simp [canonicalTerminalMatchSpace]

def canonicalTerminalMatcherRows (context : BoundaryContext)
    (before : ScannerBoundary) (occurrence : ByteOccurrence) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (canonicalTerminalMatchSpace context before occurrence)
      speculativeTerminalDirective.rule.input).map Prod.fst

theorem terminalFinalSubst_mem_matcherRows
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    terminalFinalSubst context before after occurrence ∈
      canonicalTerminalMatcherRows context before occurrence := by
  unfold canonicalTerminalMatcherRows
  rw [List.mem_map]
  exact ⟨(_, canonicalTerminalConsumed context before occurrence),
    canonicalTerminalMatchSpace_has_match receipt, rfl⟩

/-- The fired terminal successor contains the exact pending request, lookup
cursor, and generated direct handlers.  These facts come from one symbolic
matcher row of the actual sink batch. -/
theorem canonicalTerminalSuccessor_has_request
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    terminalPendingRow context before after occurrence ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      terminalLookupRow context before after occurrence ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      compressedDirectProofRule ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      compressedDirectAssertionRule ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective := by
  have rowMember := terminalFinalSubst_mem_matcherRows receipt
  have instantiated := terminalFinalSubst_instantiates_request
    context before after occurrence
  simp only [cFireReflectiveSourceExecFact,
    canonicalTerminalMatchSpace_read_eq]
  unfold cApplyReflectiveTemplate
  rw [speculative_terminal_sinks_exact]
  change _ ∈ cApplyReflectiveSinkBatch
      (canonicalTerminalMatcherRows context before occurrence) _ _ ∧ _
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (canonicalTerminalMatcherRows context before occurrence)
      ((canonicalTerminalMatchSpace context before occurrence).erase
        speculativeTerminalDirective.atom)
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule")]
      terminalPendingPattern (terminalPendingRow context before after occurrence)
      [.add terminalLookupPattern,
       .add (.var "compressed-direct-proof-handler"),
       .add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.1 (by aesop)
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (canonicalTerminalMatcherRows context before occurrence)
      ((canonicalTerminalMatchSpace context before occurrence).erase
        speculativeTerminalDirective.atom)
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern]
      terminalLookupPattern (terminalLookupRow context before after occurrence)
      [.add (.var "compressed-direct-proof-handler"),
       .add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.1 (by aesop)
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (canonicalTerminalMatcherRows context before occurrence)
      ((canonicalTerminalMatchSpace context before occurrence).erase
        speculativeTerminalDirective.atom)
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern, .add terminalLookupPattern]
      (.var "compressed-direct-proof-handler") compressedDirectProofRule
      [.add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.2.1 (by aesop)
  · exact mem_cApplyReflectiveSinkBatch_append_add_of_row
      (canonicalTerminalMatcherRows context before occurrence)
      ((canonicalTerminalMatchSpace context before occurrence).erase
        speculativeTerminalDirective.atom)
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern, .add terminalLookupPattern,
       .add (.var "compressed-direct-proof-handler")]
      (.var "compressed-direct-assertion-handler")
      compressedDirectAssertionRule
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.2.2

/-- The pending row emitted by the transformed terminal is exactly the
canonical direct-proof pending row.  Byte-derived and natural-number index
encodings meet through the scanner receipt, not through a target-side guess. -/
theorem ProofByteReceipt.terminalPendingRow_eq_direct
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) :
    terminalPendingRow context before after occurrence =
      (directContextAtBoundary context state after index).pendingRow := by
  simp only [terminalPendingRow, directContextAtBoundary,
    DirectProofContext.pendingRow]
  rw [receipt.code_atom_eq_ofNat]
  have wordEqual : before.wordPosition = after.wordPosition :=
    receipt.word_position_eq.symm
  rw [wordEqual]

/-- The initial lookup cursor emitted by the terminal is the exact canonical
cursor-zero lookup row consumed by the direct proof handler. -/
theorem ProofByteReceipt.terminalLookupRow_eq_direct
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) :
    terminalLookupRow context before after occurrence =
      (directContextAtBoundary context state after index).lookupRow := by
  simp only [terminalLookupRow, directContextAtBoundary,
    DirectProofContext.lookupRow]
  rw [receipt.code_atom_eq_ofNat]
  have wordEqual : before.wordPosition = after.wordPosition :=
    receipt.word_position_eq.symm
  rw [wordEqual]

/-- Source-indexed formulation of the terminal successor control seam. -/
theorem canonicalTerminalSuccessor_has_direct_control
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) :
    (directContextAtBoundary context state after index).pendingRow ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      (directContextAtBoundary context state after index).lookupRow ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      compressedDirectProofRule ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective ∧
      compressedDirectAssertionRule ∈
        cFireReflectiveSourceExecFact
          (canonicalTerminalMatchSpace context before occurrence)
          speculativeTerminalDirective := by
  have emitted := canonicalTerminalSuccessor_has_request receipt
  rw [ProofByteReceipt.terminalPendingRow_eq_direct receipt state] at emitted
  rw [ProofByteReceipt.terminalLookupRow_eq_direct receipt state] at emitted
  exact emitted

/-! ## Whole-source preterminal frame -/

/-- Persistent source rows required after the terminal has published the
direct request.  They are reconstructed from the source state and ledger; no
target occurrence witness is accepted as input. -/
def sourceProofTerminalExtraRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (after : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) : List Atom :=
  let directContext := directContextAtBoundary context state after index
  [heapProofRow context.proofOwner index item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   directContext.machineRow, directContext.stackSuccessorRow] ++
    directProofContinuationRows ++
    sourceProofAdditionalRows context state ledger index item

def sourceProofTerminalSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) : List Atom :=
  canonicalTerminalMatchSpace context before occurrence ++
    sourceProofTerminalExtraRows context state ledger after index item

/-- The source-derived terminal extension is scheduler-inert before the
terminal fires. -/
theorem sourceProofTerminalExtraRows_no_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (after : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) :
    cSupportedSourceExecFacts
      (sourceProofTerminalExtraRows context state ledger after index item) =
        [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  unfold sourceProofTerminalExtraRows at member
  simp only [List.mem_append] at member
  rcases member with beforeAdditional | additional
  · rcases beforeAdditional with required | continuation
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at required
      rcases required with (rfl | rfl | rfl | rfl)
      all_goals simp [extractSupportedSourceExecFact, extractRawExecFact,
        heapProofRow, MM2CompressedProofHeapEncoding.nodeRow,
        directContextAtBoundary, DirectProofContext.machineRow,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow,
        compressedStackOwner]
    · simp only [directProofContinuationRows, List.mem_cons,
        List.not_mem_nil, or_false] at continuation
      rcases continuation with (rfl | rfl | rfl | rfl | rfl)
      all_goals simp [extractSupportedSourceExecFact, extractRawExecFact,
        compressedOwnedRuntimeRuleRow]
  · exact extractSupportedSourceExecFact_eq_none_of_dynamic row
      (canonicalPassiveRows_all_dynamic context state ledger row
        (List.mem_filter.mp additional).1)

/-- Adding the complete source display does not perturb terminal selection. -/
theorem sourceProofTerminalSpace_supported_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) :
    cSupportedSourceExecFacts
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item) = [speculativeTerminalDirective] := by
  unfold sourceProofTerminalSpace cSupportedSourceExecFacts
  rw [List.filterMap_append]
  change cSupportedSourceExecFacts
      (canonicalTerminalMatchSpace context before occurrence) ++
      cSupportedSourceExecFacts
        (sourceProofTerminalExtraRows context state ledger after index item) =
    [speculativeTerminalDirective]
  rw [canonicalTerminalMatchSpace_supported_exact,
    sourceProofTerminalExtraRows_no_supported]
  rfl

theorem sourceProofTerminalSpace_selects_terminal
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) :
    selectNextScheduled
      (cSupportedSourceExecFacts
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item)) = some speculativeTerminalDirective := by
  rw [sourceProofTerminalSpace_supported_exact]
  rfl

/-- The exact scheduler read of the assembled source space is the space
itself: the terminal shell is removed once and prepended once. -/
theorem sourceProofTerminalSpace_read_eq
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) :
    speculativeTerminalDirective.atom ::
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item).erase speculativeTerminalDirective.atom =
      sourceProofTerminalSpace context state ledger before after occurrence
        index item := by
  simp [sourceProofTerminalSpace, canonicalTerminalMatchSpace]

def sourceProofTerminalMatcherRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (speculativeTerminalDirective.atom ::
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item).erase speculativeTerminalDirective.atom)
      speculativeTerminalDirective.rule.input).map Prod.fst

/-- The canonical source-derived matcher row lifts monotonically into the
complete preterminal source display. -/
theorem terminalFinalSubst_mem_sourceProofTerminalMatcherRows
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    terminalFinalSubst context before after occurrence ∈
      sourceProofTerminalMatcherRows context state ledger before after
        occurrence index item := by
  have canonicalMatch := canonicalTerminalMatchSpace_has_match receipt
  unfold sourceProofTerminalMatcherRows
  rw [List.mem_map]
  refine ⟨(_, canonicalTerminalConsumed context before occurrence), ?_, rfl⟩
  rw [speculative_terminal_input_exact] at canonicalMatch ⊢
  have included : ∀ atom,
      atom ∈ canonicalTerminalMatchSpace context before occurrence →
        atom ∈ speculativeTerminalDirective.atom ::
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item).erase speculativeTerminalDirective.atom := by
    intro atom member
    rw [sourceProofTerminalSpace_read_eq]
    exact List.mem_append_left _ member
  exact Conformance.Computable.cmatchPattern_mono []
    (canonicalTerminalMatchSpace context before occurrence)
    (speculativeTerminalDirective.atom ::
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item).erase speculativeTerminalDirective.atom)
    _ included _ _ canonicalMatch

theorem sourceProofTerminalSpace_steps
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) =
      some
        (cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective) := by
  unfold cReflectiveSourceWorkQueueStep
  rw [sourceProofTerminalSpace_selects_terminal]

theorem sourceProofTerminalSpace_inhabits_exact_native_type
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (item : ProofOccurrence) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item)
        (reflectiveNativeListExactTargetNativeType .leaveInert
          (cFireReflectiveSourceExecFact
            (sourceProofTerminalSpace context state ledger before after
              occurrence index item) speculativeTerminalDirective)).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert _ _).2
  exact sourceProofTerminalSpace_steps context state ledger before after
    occurrence index item

private theorem terminalSinkBatch_has_request
    (rows : List Subst) (space : List Atom)
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence)
    (rowMember : terminalFinalSubst context before after occurrence ∈ rows)
    (instantiated := terminalFinalSubst_instantiates_request
      context before after occurrence) :
    terminalPendingRow context before after occurrence ∈
        cApplyReflectiveSinkBatch rows space terminalSinks ∧
      terminalLookupRow context before after occurrence ∈
        cApplyReflectiveSinkBatch rows space terminalSinks ∧
      compressedDirectProofRule ∈
        cApplyReflectiveSinkBatch rows space terminalSinks ∧
      compressedDirectAssertionRule ∈
        cApplyReflectiveSinkBatch rows space terminalSinks := by
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row rows space
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule")]
      terminalPendingPattern (terminalPendingRow context before after occurrence)
      [.add terminalLookupPattern,
       .add (.var "compressed-direct-proof-handler"),
       .add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.1 (by aesop)
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row rows space
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern]
      terminalLookupPattern (terminalLookupRow context before after occurrence)
      [.add (.var "compressed-direct-proof-handler"),
       .add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.1 (by aesop)
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row rows space
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern, .add terminalLookupPattern]
      (.var "compressed-direct-proof-handler") compressedDirectProofRule
      [.add (.var "compressed-direct-assertion-handler")]
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.2.1 (by aesop)
  · exact mem_cApplyReflectiveSinkBatch_append_add_of_row rows space
      [.remove terminalScanPattern,
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-assertion-launch-rule"),
       .add (.var "compressed-lookup-fault-rule"),
       .add (.var "compressed-lookup-advance-rule"),
       .add terminalPendingPattern, .add terminalLookupPattern,
       .add (.var "compressed-direct-proof-handler")]
      (.var "compressed-direct-assertion-handler")
      compressedDirectAssertionRule
      (terminalFinalSubst context before after occurrence) rowMember
      instantiated.2.2.2

/-- The actual assembled terminal successor publishes the direct request
control rows while retaining the source-derived frame in its input space. -/
theorem sourceProofTerminalSuccessor_has_direct_control
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    (directContextAtBoundary context state after index).pendingRow ∈
        cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective ∧
      (directContextAtBoundary context state after index).lookupRow ∈
        cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective ∧
      compressedDirectProofRule ∈
        cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective ∧
      compressedDirectAssertionRule ∈
        cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective := by
  have rowMember :=
    terminalFinalSubst_mem_sourceProofTerminalMatcherRows receipt state ledger
      item
  have emitted :
      terminalPendingRow context before after occurrence ∈
          cFireReflectiveSourceExecFact
            (sourceProofTerminalSpace context state ledger before after
              occurrence index item) speculativeTerminalDirective ∧
        terminalLookupRow context before after occurrence ∈
          cFireReflectiveSourceExecFact
            (sourceProofTerminalSpace context state ledger before after
              occurrence index item) speculativeTerminalDirective ∧
        compressedDirectProofRule ∈
          cFireReflectiveSourceExecFact
            (sourceProofTerminalSpace context state ledger before after
              occurrence index item) speculativeTerminalDirective ∧
        compressedDirectAssertionRule ∈
          cFireReflectiveSourceExecFact
            (sourceProofTerminalSpace context state ledger before after
              occurrence index item) speculativeTerminalDirective := by
    unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
    rw [speculative_terminal_sinks_exact]
    change _ ∈ cApplyReflectiveSinkBatch
        (sourceProofTerminalMatcherRows context state ledger before after
          occurrence index item) _ terminalSinks ∧ _
    exact terminalSinkBatch_has_request _ _ context before after occurrence
      rowMember
  rw [ProofByteReceipt.terminalPendingRow_eq_direct receipt state] at emitted
  rw [ProofByteReceipt.terminalLookupRow_eq_direct receipt state] at emitted
  exact emitted

#print axioms speculative_terminal_input_exact
#print axioms speculative_terminal_sinks_exact
#print axioms speculative_terminal_atom_surface
#print axioms canonicalTerminalMatchSpace_supported_exact
#print axioms canonicalTerminalMatchSpace_selects_terminal
#print axioms canonicalTerminalMatchSpace_steps
#print axioms canonicalTerminalMatchSpace_inhabits_exact_native_type
#print axioms canonicalTerminalMatchSpace_has_match
#print axioms terminalFinalSubst_instantiates_request
#print axioms canonicalTerminalMatchSpace_read_eq
#print axioms terminalFinalSubst_mem_matcherRows
#print axioms canonicalTerminalSuccessor_has_request
#print axioms ProofByteReceipt.terminalPendingRow_eq_direct
#print axioms ProofByteReceipt.terminalLookupRow_eq_direct
#print axioms canonicalTerminalSuccessor_has_direct_control
#print axioms sourceProofTerminalExtraRows_no_supported
#print axioms sourceProofTerminalSpace_supported_exact
#print axioms sourceProofTerminalSpace_selects_terminal
#print axioms sourceProofTerminalSpace_read_eq
#print axioms terminalFinalSubst_mem_sourceProofTerminalMatcherRows
#print axioms sourceProofTerminalSpace_steps
#print axioms sourceProofTerminalSpace_inhabits_exact_native_type
#print axioms sourceProofTerminalSuccessor_has_direct_control

end Mettapedia.Languages.Metamath.MM2CompressedProofTerminalHitContinuous
