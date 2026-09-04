import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation

/-!
# Continuous transformed-terminal to compressed proof-hit boundary

This module gives the concrete public-boundary segment for one compressed
proof reference.  It exposes the exact generated speculative-terminal input
and output interfaces, constructs its canonical source-derived match space,
identifies the fired successor with a direct proof-request frame, and composes
the terminal and proof-hit transitions through the actual scheduler.
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
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
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

private theorem cmatchAtom_filterMap_witness
    {space : List Atom} {before after : Subst} {pattern atom : Atom}
    (member : (after, atom) ∈ space.filterMap fun candidate =>
      (Conformance.Computable.cmatchAtom before pattern candidate).map
        (·, candidate)) :
    atom ∈ space ∧
      Conformance.Computable.cmatchAtom before pattern atom = some after := by
  rw [List.mem_filterMap] at member
  obtain ⟨candidate, candidateMember, mapped⟩ := member
  simp only [Option.map_eq_some_iff] at mapped
  obtain ⟨substitution, matched, equal⟩ := mapped
  cases equal
  exact ⟨candidateMember, matched⟩

private theorem terminalSelf_candidate_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) {beforeSubst afterSubst : Subst} {atom : Atom}
    (member : atom ∈ canonicalTerminalMatchSpace context before occurrence)
    (matched : Conformance.Computable.cmatchAtom beforeSubst
      terminalSelfPattern atom = some afterSubst) :
    atom = speculativeTerminalDirective.atom := by
  simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals simp [terminalSelfPattern,
    scannerRow, terminalClassRow, compressedTerminalByteRow,
    compressedOwnedRuntimeRuleRow, compressedDirectProofHandlerRow,
    compressedDirectAssertionHandlerRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList] at matched

private theorem terminalScan_candidate_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) {beforeSubst afterSubst : Subst} {atom : Atom}
    (member : atom ∈ canonicalTerminalMatchSpace context before occurrence)
    (matched : Conformance.Computable.cmatchAtom beforeSubst
      terminalScanPattern atom = some afterSubst) :
    atom = scannerRow context before := by
  simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [speculative_terminal_atom_surface, terminalScanPattern,
      Conformance.Computable.cmatchAtom,
      Conformance.Computable.cmatchAtomList] at matched
  · rfl
  all_goals simp [terminalScanPattern, terminalClassRow,
    compressedTerminalByteRow, compressedOwnedRuntimeRuleRow,
    compressedDirectProofHandlerRow, compressedDirectAssertionHandlerRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList] at matched

private theorem terminalClass_candidate_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) {beforeSubst afterSubst : Subst} {atom : Atom}
    (member : atom ∈ canonicalTerminalMatchSpace context before occurrence)
    (matched : Conformance.Computable.cmatchAtom beforeSubst
      terminalClassPattern atom = some afterSubst) :
    atom = terminalClassRow occurrence := by
  simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [speculative_terminal_atom_surface, terminalClassPattern,
      Conformance.Computable.cmatchAtom,
      Conformance.Computable.cmatchAtomList] at matched
  · simp [terminalClassPattern, scannerRow,
      Conformance.Computable.cmatchAtom,
      Conformance.Computable.cmatchAtomList] at matched
  · rfl
  all_goals simp [terminalClassPattern, compressedOwnedRuntimeRuleRow,
    compressedDirectProofHandlerRow, compressedDirectAssertionHandlerRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList] at matched

private theorem terminalOwnedRule_candidate_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) (kind variableName : String)
    (expectedRule : Atom)
    (kindCase : (kind, expectedRule) = ("proof", compressedProofStepRule) ∨
      (kind, expectedRule) =
        ("assertion-launch", compressedAssertionLaunchRule) ∨
      (kind, expectedRule) = ("lookup-fault", compressedHeapLookupFaultRule) ∨
      (kind, expectedRule) =
        ("lookup-advance", compressedHeapLookupAdvanceRule))
    {beforeSubst afterSubst : Subst} {atom : Atom}
    (member : atom ∈ canonicalTerminalMatchSpace context before occurrence)
    (matched : Conformance.Computable.cmatchAtom beforeSubst
      (terminalOwnedRulePattern kind variableName) atom = some afterSubst) :
    atom = compressedOwnedRuntimeRuleRow kind expectedRule := by
  rcases kindCase with kindCase | kindCase | kindCase | kindCase <;>
    cases kindCase
  all_goals
    simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows] at member
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals simp [speculative_terminal_atom_surface, terminalOwnedRulePattern,
    scannerRow, terminalClassRow, compressedTerminalByteRow,
    compressedOwnedRuntimeRuleRow, compressedDirectProofHandlerRow,
    compressedDirectAssertionHandlerRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList] at matched

private theorem terminalDirectHandler_candidate_eq
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) (kind variableName : String)
    (expectedRule : Atom)
    (kindCase : (kind, expectedRule) = ("proof", compressedDirectProofRule) ∨
      (kind, expectedRule) = ("assertion", compressedDirectAssertionRule))
    {beforeSubst afterSubst : Subst} {atom : Atom}
    (member : atom ∈ canonicalTerminalMatchSpace context before occurrence)
    (matched : Conformance.Computable.cmatchAtom beforeSubst
      (terminalDirectHandlerPattern kind variableName) atom = some afterSubst) :
    atom = .expression
      [.symbol "mm-compressed-owned-speculative-lookup-handler", .symbol kind,
        expectedRule] := by
  rcases kindCase with kindCase | kindCase <;> cases kindCase
  all_goals
    simp [canonicalTerminalMatchSpace, terminalRuntimeCaptureRows] at member
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals simp [speculative_terminal_atom_surface,
    terminalDirectHandlerPattern, scannerRow, terminalClassRow,
    compressedTerminalByteRow, compressedOwnedRuntimeRuleRow,
    compressedDirectProofHandlerRow, compressedDirectAssertionHandlerRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList] at matched

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

theorem terminalFinalSubst_instantiates_runtime_rules
    (context : BoundaryContext) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) :
    instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-proof-rule") = some compressedProofStepRule ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-assertion-launch-rule") =
          some compressedAssertionLaunchRule ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-lookup-fault-rule") =
          some compressedHeapLookupFaultRule ∧
      instantiateTemplateAtom?
        (terminalFinalSubst context before after occurrence)
        (.var "compressed-lookup-advance-rule") =
          some compressedHeapLookupAdvanceRule := by
  simp [terminalFinalSubst, terminalDirectProofSubst,
    terminalAdvanceSubst, terminalFaultSubst, terminalAssertionSubst,
    terminalProofSubst, terminalClassSubst, terminalScanSubst,
    terminalSelfSubst, instantiateTemplateAtom?, templateCovered,
    applySubst, Subst.lookup]

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

/-- Every successful canonical terminal match reconstructs the same captured
rule inventory.  This is no-invention by matcher inversion rather than by
normalizing the complete nine-premise search. -/
theorem canonicalTerminalMatcherRow_eq
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {substitution : Subst}
    (rowMember : substitution ∈
      canonicalTerminalMatcherRows context before occurrence) :
    substitution = terminalFinalSubst context before after occurrence := by
  unfold canonicalTerminalMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  dsimp only at substEq
  subst substitution
  rw [speculative_terminal_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold terminalPatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, finished⟩ := r8
  obtain ⟨a1Member, m1⟩ := cmatchAtom_filterMap_witness f1
  have a1Eq := terminalSelf_candidate_eq context before occurrence a1Member m1
  subst a1
  have s1Eq : s1 = terminalSelfSubst :=
    Option.some.inj (m1.symm.trans terminalSelf_match)
  subst s1
  obtain ⟨a2Member, m2⟩ := cmatchAtom_filterMap_witness f2
  have a2Eq := terminalScan_candidate_eq context before occurrence a2Member m2
  subst a2
  have s2Eq : s2 = terminalScanSubst context before after occurrence :=
    Option.some.inj (m2.symm.trans (terminalScan_match receipt))
  subst s2
  obtain ⟨a3Member, m3⟩ := cmatchAtom_filterMap_witness f3
  have a3Eq := terminalClass_candidate_eq context before occurrence a3Member m3
  subst a3
  have s3Eq : s3 = terminalClassSubst context before after occurrence :=
    Option.some.inj
      (m3.symm.trans (terminalClass_match context before after occurrence))
  subst s3
  obtain ⟨a4Member, m4⟩ := cmatchAtom_filterMap_witness f4
  have a4Eq := terminalOwnedRule_candidate_eq context before occurrence
    "proof" "compressed-proof-rule" compressedProofStepRule (Or.inl rfl)
    a4Member m4
  subst a4
  have s4Eq : s4 = terminalProofSubst context before after occurrence :=
    Option.some.inj
      (m4.symm.trans (terminalProof_match context before after occurrence))
  subst s4
  obtain ⟨a5Member, m5⟩ := cmatchAtom_filterMap_witness f5
  have a5Eq := terminalOwnedRule_candidate_eq context before occurrence
    "assertion-launch" "compressed-assertion-launch-rule"
      compressedAssertionLaunchRule (Or.inr (Or.inl rfl)) a5Member m5
  subst a5
  have s5Eq : s5 = terminalAssertionSubst context before after occurrence :=
    Option.some.inj
      (m5.symm.trans (terminalAssertion_match context before after occurrence))
  subst s5
  obtain ⟨a6Member, m6⟩ := cmatchAtom_filterMap_witness f6
  have a6Eq := terminalOwnedRule_candidate_eq context before occurrence
    "lookup-fault" "compressed-lookup-fault-rule" compressedHeapLookupFaultRule
      (Or.inr (Or.inr (Or.inl rfl))) a6Member m6
  subst a6
  have s6Eq : s6 = terminalFaultSubst context before after occurrence :=
    Option.some.inj
      (m6.symm.trans (terminalFault_match context before after occurrence))
  subst s6
  obtain ⟨a7Member, m7⟩ := cmatchAtom_filterMap_witness f7
  have a7Eq := terminalOwnedRule_candidate_eq context before occurrence
    "lookup-advance" "compressed-lookup-advance-rule"
      compressedHeapLookupAdvanceRule (Or.inr (Or.inr (Or.inr rfl)))
      a7Member m7
  subst a7
  have s7Eq : s7 = terminalAdvanceSubst context before after occurrence :=
    Option.some.inj
      (m7.symm.trans (terminalAdvance_match context before after occurrence))
  subst s7
  obtain ⟨a8Member, m8⟩ := cmatchAtom_filterMap_witness f8
  have a8Eq := terminalDirectHandler_candidate_eq context before occurrence
    "proof" "compressed-direct-proof-handler" compressedDirectProofRule
      (Or.inl rfl) a8Member m8
  change a8 = compressedDirectProofHandlerRow at a8Eq
  subst a8
  have s8Eq : s8 = terminalDirectProofSubst context before after occurrence :=
    Option.some.inj
      (m8.symm.trans (terminalDirectProof_match context before after occurrence))
  subst s8
  obtain ⟨a9Member, m9⟩ := cmatchAtom_filterMap_witness f9
  have a9Eq := terminalDirectHandler_candidate_eq context before occurrence
    "assertion" "compressed-direct-assertion-handler"
      compressedDirectAssertionRule (Or.inr rfl) a9Member m9
  change a9 = compressedDirectAssertionHandlerRow at a9Eq
  subst a9
  have s9Eq : s9 = terminalFinalSubst context before after occurrence :=
    Option.some.inj
      (m9.symm.trans
        (terminalDirectAssertion_match context before after occurrence))
  subst s9
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  exact finished.1

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

/-! The terminal reads opaque rule carriers as data.  Persistent source-state
rows have disjoint heads, so extending the canonical matcher space with the
complete source display cannot create a second capture substitution. -/

private theorem terminalPattern_never_matches_heapProofRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (position : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom σ pattern
        (heapProofRow owner position item) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, heapProofRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_assertionHeapRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (position assertionPosition : Nat) (label : String) :
    Conformance.Computable.cmatchAtom σ pattern
        (.expression
          [.symbol "mm-compressed-heap-assertion", owner,
            (CompressedIndexCode.ofNat position).atom,
            natAtom assertionPosition, stringAtom label]) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_nodeRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom σ pattern
        (MM2CompressedProofHeapEncoding.nodeRow owner item) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, MM2CompressedProofHeapEncoding.nodeRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_compressedStackRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (position : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom σ pattern
        (compressedStackRow owner position item) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, compressedStackRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_normalStackRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (position : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom σ pattern
        (normalStackRow owner position item) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, normalStackRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_saveReceiptRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (owner : Atom) (position : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom σ pattern
        (saveReceiptRow owner position item) = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, saveReceiptRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_directMachineRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (context : DirectProofContext) :
    Conformance.Computable.cmatchAtom σ pattern context.machineRow = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, DirectProofContext.machineRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_stackSuccessorRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (context : DirectProofContext) :
    Conformance.Computable.cmatchAtom σ pattern
        context.stackSuccessorRow = none := by
  simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, DirectProofContext.stackSuccessorRow,
    compressedIndexSuccessorRow, compressedStackOwner,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem terminalPattern_never_matches_continuationRow
    (σ : Subst) (pattern : Atom) (member : pattern ∈ terminalPatterns)
    (row : Atom) (rowMember : row ∈ directProofContinuationRows) :
    Conformance.Computable.cmatchAtom σ pattern row = none := by
  simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
    or_false] at rowMember
  rcases rowMember with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [terminalPatterns, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [terminalSelfPattern, terminalScanPattern,
    terminalClassPattern, terminalOwnedRulePattern,
    terminalDirectHandlerPattern, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]

private theorem heapProofRowsFrom_never_match_terminalPattern
    {Other : Type} (owner : Atom) (position : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other))
    (σ : Subst) (pattern : Atom) (patternMember : pattern ∈ terminalPatterns) :
    ∀ row ∈ heapProofRowsFrom owner position heap,
      Conformance.Computable.cmatchAtom σ pattern row = none := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | occurrence item =>
          intro row member
          simp only [heapProofRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · exact terminalPattern_never_matches_heapProofRow σ pattern
              patternMember owner position item
          · exact induction (position + 1) row tail
      | «opaque» value =>
          intro row member
          exact induction (position + 1) row
            (by simpa [heapProofRowsFrom] using member)

private theorem assertionHeapRowsFrom_never_match_terminalPattern
    {source : SourcePrefix} (owner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (σ : Subst) (pattern : Atom) (patternMember : pattern ∈ terminalPatterns) :
    ∀ row ∈ assertionHeapRowsFrom owner position heap,
      Conformance.Computable.cmatchAtom σ pattern row = none := by
  induction heap generalizing position with
  | nil => simp [assertionHeapRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | proof nodeId =>
          intro row member
          exact induction (position + 1) row
            (by simpa [assertionHeapRowsFrom] using member)
      | assertion assertion =>
          intro row member
          simp only [assertionHeapRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · exact terminalPattern_never_matches_assertionHeapRow σ pattern
              patternMember owner position (assertionPosition source assertion)
                assertion.label
          · exact induction (position + 1) row tail

private theorem sourceNodeRowsFrom_never_match_terminalPattern
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (owner : Atom) (position : Nat) (nodes : List (ProofNode source target))
    (occurrences : List Atom) (σ : Subst) (pattern : Atom)
    (patternMember : pattern ∈ terminalPatterns) :
    ∀ row ∈ sourceNodeRowsFrom owner position nodes occurrences,
      Conformance.Computable.cmatchAtom σ pattern row = none := by
  induction nodes generalizing position occurrences with
  | nil => simp [sourceNodeRowsFrom]
  | cons node nodes induction =>
      cases occurrences with
      | nil => simp [sourceNodeRowsFrom]
      | cons occurrence occurrences =>
          intro row member
          simp only [sourceNodeRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · exact terminalPattern_never_matches_nodeRow σ pattern
              patternMember owner (displayedProofOccurrence position node occurrence)
          · exact induction (position + 1) occurrences row tail

private theorem sourceStackRowsFrom_never_match_terminalPattern
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (owner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (stack : List Nat)
    (σ : Subst) (pattern : Atom) (patternMember : pattern ∈ terminalPatterns) :
    ∀ row ∈ sourceStackRowsFrom owner state ledger position stack,
      Conformance.Computable.cmatchAtom σ pattern row = none := by
  induction stack generalizing position with
  | nil => simp [sourceStackRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceStackRowsFrom] at member
      split at member
      next node occurrence nodeLookup occurrenceLookup =>
        rw [List.mem_append] at member
        rcases member with ownRows | tail
        · simp only [List.mem_cons] at ownRows
          rcases ownRows with rfl | ownRows
          · exact terminalPattern_never_matches_compressedStackRow σ pattern
              patternMember owner position _
          · rcases ownRows with rfl | impossible
            · exact terminalPattern_never_matches_normalStackRow σ pattern
                patternMember owner position _
            · simp at impossible
        · exact induction (position + 1) row tail
      next => exact induction (position + 1) row (by simpa using member)

private theorem sourceSaveRowsFrom_never_match_terminalPattern
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (saves : List Nat)
    (σ : Subst) (pattern : Atom) (patternMember : pattern ∈ terminalPatterns) :
    ∀ row ∈ sourceSaveRowsFrom context state ledger position saves,
      Conformance.Computable.cmatchAtom σ pattern row = none := by
  induction saves generalizing position with
  | nil => simp [sourceSaveRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceSaveRowsFrom] at member
      split at member
      next node occurrence nodeLookup occurrenceLookup =>
        rw [List.mem_append] at member
        rcases member with ownRows | tail
        · simp only [List.mem_singleton] at ownRows
          subst row
          exact terminalPattern_never_matches_saveReceiptRow σ pattern
            patternMember context.proofOwner
              (context.initialHeapLength + position) _
        · exact induction (position + 1) row tail
      next => exact induction (position + 1) row (by simpa using member)

private theorem canonicalPassiveRows_never_match_terminalPattern
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (row : Atom)
    (rowMember : row ∈ canonicalPassiveRows context state ledger)
    (σ : Subst) (pattern : Atom) (patternMember : pattern ∈ terminalPatterns) :
    Conformance.Computable.cmatchAtom σ pattern row = none := by
  simp only [canonicalPassiveRows] at rowMember
  rcases List.mem_append.mp rowMember with beforeSave | save
  rcases List.mem_append.mp beforeSave with beforeStack | stack
  rcases List.mem_append.mp beforeStack with beforeNode | node
  rcases List.mem_append.mp beforeNode with heapProof | assertionHeap
  · exact heapProofRowsFrom_never_match_terminalPattern context.proofOwner 0
      (displayedHeap state ledger) σ pattern patternMember row heapProof
  · exact assertionHeapRowsFrom_never_match_terminalPattern
      context.proofOwner 0 state.heap σ pattern patternMember row assertionHeap
  · exact sourceNodeRowsFrom_never_match_terminalPattern context.proofOwner 0
      state.nodes ledger.occurrences σ pattern patternMember row node
  · exact sourceStackRowsFrom_never_match_terminalPattern context.proofOwner
      state ledger 0 state.stack σ pattern patternMember row stack
  · exact sourceSaveRowsFrom_never_match_terminalPattern context state ledger
      0 state.saves σ pattern patternMember row save

private theorem sourceProofTerminalExtraRows_never_match_terminalPattern
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (after : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) (σ : Subst) (pattern : Atom)
    (patternMember : pattern ∈ terminalPatterns) (row : Atom)
    (rowMember : row ∈
      sourceProofTerminalExtraRows context state ledger after index item) :
    Conformance.Computable.cmatchAtom σ pattern row = none := by
  unfold sourceProofTerminalExtraRows at rowMember
  simp only [List.mem_append] at rowMember
  rcases rowMember with beforeAdditional | additional
  · rcases beforeAdditional with required | continuation
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at required
      rcases required with rfl | rfl | rfl | rfl
      · exact terminalPattern_never_matches_heapProofRow σ pattern
          patternMember context.proofOwner index item
      · exact terminalPattern_never_matches_nodeRow σ pattern patternMember
          context.proofOwner item
      · exact terminalPattern_never_matches_directMachineRow σ pattern
          patternMember (directContextAtBoundary context state after index)
      · exact terminalPattern_never_matches_stackSuccessorRow σ pattern
          patternMember (directContextAtBoundary context state after index)
    · exact terminalPattern_never_matches_continuationRow σ pattern
        patternMember row continuation
  · exact canonicalPassiveRows_never_match_terminalPattern context state ledger
      row (List.mem_filter.mp additional).1 σ pattern patternMember

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

/-- The complete source display contributes no terminal captures: the actual
assembled matcher rows are exactly those of the canonical nine-row terminal
slice. -/
theorem sourceProofTerminal_matcher_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchInputSpec []
        (speculativeTerminalDirective.atom ::
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item).erase speculativeTerminalDirective.atom)
        speculativeTerminalDirective.rule.input =
      Conformance.Computable.cmatchInputSpec []
        (canonicalTerminalMatchSpace context before occurrence)
        speculativeTerminalDirective.rule.input := by
  rw [sourceProofTerminalSpace_read_eq]
  unfold sourceProofTerminalSpace
  rw [speculative_terminal_input_exact]
  apply Conformance.Computable.cmatchPattern_append_of_right_never_matches
  intro σ pattern patternMember row rowMember
  exact sourceProofTerminalExtraRows_never_match_terminalPattern context state
    ledger after index item σ pattern patternMember row rowMember

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

theorem sourceProofTerminalMatcherRow_eq
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) {substitution : Subst}
    (rowMember : substitution ∈
      sourceProofTerminalMatcherRows context state ledger before after occurrence
        index item) :
    substitution = terminalFinalSubst context before after occurrence := by
  unfold sourceProofTerminalMatcherRows at rowMember
  rw [sourceProofTerminal_matcher_exact context state ledger before after
    occurrence index item] at rowMember
  exact canonicalTerminalMatcherRow_eq receipt rowMember

def TerminalSuccessorSupportedWithin (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate ∈ directLookupInterface

private theorem sourceProofTerminalLive_eq
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    (sourceProofTerminalSpace context state ledger before after occurrence
        index item).erase speculativeTerminalDirective.atom =
      [scannerRow context before, terminalClassRow occurrence] ++
        terminalRuntimeCaptureRows ++
        sourceProofTerminalExtraRows context state ledger after index item := by
  simp [sourceProofTerminalSpace, canonicalTerminalMatchSpace]

private theorem sourceProofTerminalLive_supported_within
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    AtomsWithin TerminalSuccessorSupportedWithin
      ((sourceProofTerminalSpace context state ledger before after occurrence
        index item).erase speculativeTerminalDirective.atom) := by
  intro atom member
  rw [sourceProofTerminalLive_eq] at member
  simp only [List.mem_append] at member
  rcases member with canonical | extra
  · rcases canonical with boundary | runtime
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at boundary
      rcases boundary with rfl | rfl
      all_goals intro candidate extracted
      all_goals simp [scannerRow,
        terminalClassRow, compressedTerminalByteRow,
        extractSupportedSourceExecFact, extractRawExecFact] at extracted
    · simp only [terminalRuntimeCaptureRows, List.mem_cons,
        List.not_mem_nil, or_false] at runtime
      rcases runtime with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals intro candidate extracted
      all_goals simp [
        compressedOwnedRuntimeRuleRow, compressedDirectProofHandlerRow,
        compressedDirectAssertionHandlerRow, extractSupportedSourceExecFact,
        extractRawExecFact] at extracted
  · intro candidate extracted
    have noSupported := sourceProofTerminalExtraRows_no_supported context state
      ledger after index item
    unfold cSupportedSourceExecFacts at noSupported
    rw [List.filterMap_eq_nil_iff] at noSupported
    rw [noSupported atom extra] at extracted
    contradiction

private theorem speculativeTerminal_support_set :
    ReflectiveSupportSetTemplate speculativeTerminalDirective.rule.tmpl := by
  intro sink member
  rw [speculative_terminal_sinks_exact] at member
  simp only [terminalSinks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals trivial

private theorem sourceProofTerminal_additions_supported_within
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    ReflectiveAddedAtomsWithin TerminalSuccessorSupportedWithin
      (sourceProofTerminalMatcherRows context state ledger before after
        occurrence index item) speculativeTerminalDirective.rule.tmpl := by
  intro atom added
  rcases added with
    ⟨sink, sinkMember, authored, rfl, substitution, rowMember, instantiated⟩
  have substitutionEq := sourceProofTerminalMatcherRow_eq receipt state ledger
    item rowMember
  subst substitution
  rw [speculative_terminal_sinks_exact] at sinkMember
  simp [terminalSinks] at sinkMember
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [(terminalFinalSubst_instantiates_runtime_rules context before after
      occurrence).1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_compressedProofStepRule_exact] at extracted
    cases extracted
    simp [directLookupInterface]
  · rw [(terminalFinalSubst_instantiates_runtime_rules context before after
      occurrence).2.1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_compressedAssertionLaunchRule_exact] at extracted
    cases extracted
    simp [directLookupInterface]
  · rw [(terminalFinalSubst_instantiates_runtime_rules context before after
      occurrence).2.2.1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_compressedHeapLookupFaultRule_exact] at extracted
    cases extracted
    simp [directLookupInterface]
  · rw [(terminalFinalSubst_instantiates_runtime_rules context before after
      occurrence).2.2.2] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_compressedHeapLookupAdvanceRule_exact] at extracted
    cases extracted
    simp [directLookupInterface]
  · rw [(terminalFinalSubst_instantiates_request context before after
      occurrence).1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    simp [terminalPendingRow, extractSupportedSourceExecFact,
      extractRawExecFact] at extracted
  · rw [(terminalFinalSubst_instantiates_request context before after
      occurrence).2.1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    simp [terminalLookupRow, extractSupportedSourceExecFact,
      extractRawExecFact] at extracted
  · rw [(terminalFinalSubst_instantiates_request context before after
      occurrence).2.2.1] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_speculativeDirectProofDirective_exact] at extracted
    cases extracted
    simp [directLookupInterface]
  · rw [(terminalFinalSubst_instantiates_request context before after
      occurrence).2.2.2] at instantiated
    have atomEq := Option.some.inj instantiated
    subst atom
    intro candidate extracted
    rw [extract_speculativeDirectAssertionDirective_exact] at extracted
    cases extracted
    simp [directLookupInterface]

theorem sourceProofTerminalSuccessor_supported_within
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    AtomsWithin TerminalSuccessorSupportedWithin
      (cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective) := by
  unfold cFireReflectiveSourceExecFact
  apply cApplyReflectiveTemplate_atomsWithin
  · exact speculativeTerminal_support_set
  · exact sourceProofTerminalLive_supported_within context state ledger before
      after occurrence index item
  · exact sourceProofTerminal_additions_supported_within receipt state ledger
      item

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

/-! ## Literal successor as a direct-proof matcher frame -/

/-- The terminal sink batch preserves any resident expression whose head is
neither the scanner head consumed by the unique remove sink nor an executable
shell.  The executable-head exclusion also guarantees that removing the
selected terminal shell cannot remove the candidate first. -/
private theorem sourceProofTerminalSuccessor_retains_expression
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence)
    (head : String) (tail : List Atom)
    (notExec : head ≠ "exec") (notScan : head ≠ "mm-compressed-scan")
    (present : (.expression (.symbol head :: tail) : Atom) ∈
      sourceProofTerminalSpace context state ledger before after occurrence
        index item) :
    (.expression (.symbol head :: tail) : Atom) ∈
      cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective := by
  let candidate : Atom := .expression (.symbol head :: tail)
  have notTerminal : candidate ≠ speculativeTerminalDirective.atom := by
    intro equal
    rw [speculative_terminal_atom_surface] at equal
    simp [candidate, notExec] at equal
  have live : candidate ∈
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item).erase speculativeTerminalDirective.atom :=
    (List.mem_erase_of_ne notTerminal).2 present
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_terminal_sinks_exact]
  apply mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    (rows := sourceProofTerminalMatcherRows context state ledger before after
      occurrence index item)
  · intro sink member
    simp only [terminalSinks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨terminalScanPattern, rfl, fun substitution _ => by
        unfold terminalScanPattern
        apply instantiateTemplateAtom?_expression_symbol_head_ne
        exact notScan.symm⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact live

private theorem sourceProofTerminalSuccessor_retains_heap_row
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    heapProofRow context.proofOwner index item ∈
      cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective := by
  apply sourceProofTerminalSuccessor_retains_expression context state ledger
    before after occurrence index item "mm-compressed-heap-proof" _
    (by decide) (by decide)
  simp [sourceProofTerminalSpace, sourceProofTerminalExtraRows, heapProofRow]

private theorem sourceProofTerminalSuccessor_retains_node_row
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
      cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective := by
  apply sourceProofTerminalSuccessor_retains_expression context state ledger
    before after occurrence index item "mm-compressed-node" _
    (by decide) (by decide)
  simp [sourceProofTerminalSpace, sourceProofTerminalExtraRows,
    MM2CompressedProofHeapEncoding.nodeRow]

private theorem sourceProofTerminalSuccessor_retains_machine_row
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    (directContextAtBoundary context state after index).machineRow ∈
      cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective := by
  apply sourceProofTerminalSuccessor_retains_expression context state ledger
    before after occurrence index item "mm-compressed-machine" _
    (by decide) (by decide)
  simp [sourceProofTerminalSpace, sourceProofTerminalExtraRows,
    directContextAtBoundary, DirectProofContext.machineRow]

private theorem sourceProofTerminalSuccessor_retains_stack_successor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence) :
    (directContextAtBoundary context state after index).stackSuccessorRow ∈
      cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective := by
  apply sourceProofTerminalSuccessor_retains_expression context state ledger
    before after occurrence index item "mm-compressed-index-successor" _
    (by decide) (by decide)
  simp [sourceProofTerminalSpace, sourceProofTerminalExtraRows,
    directContextAtBoundary, DirectProofContext.stackSuccessorRow,
    compressedIndexSuccessorRow]

private theorem sourceProofTerminalSuccessor_retains_continuation
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (before after : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat) (item : ProofOccurrence)
    (row : Atom) (member : row ∈ directProofContinuationRows) :
    row ∈ cFireReflectiveSourceExecFact
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item) speculativeTerminalDirective := by
  simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply sourceProofTerminalSuccessor_retains_expression context state ledger
      before after occurrence index item "mm-compressed-owned-runtime-rule" _
      (by decide) (by decide)
    simp [sourceProofTerminalSpace, sourceProofTerminalExtraRows,
      directProofContinuationRows, compressedOwnedRuntimeRuleRow]

/-- A scheduler-inert row resident in a space survives erasure of the direct
proof shell and therefore remains visible to that directive's matcher. -/
private theorem mem_directProofLive_of_mem_of_inert
    {space : List Atom} {row : Atom}
    (inert : extractSupportedSourceExecFact row = none)
    (present : row ∈ space) :
    row ∈ directProofLive space := by
  unfold directProofLive
  apply (List.mem_erase_of_ne ?_).2 present
  intro equal
  have atomExact : speculativeDirectProofDirective.atom =
      compressedDirectProofRule := by
    decide +kernel
  rw [equal, atomExact, extract_speculativeDirectProofDirective_exact] at inert
  contradiction

/-- The literal successor of the transformed terminal has the exact positive
matcher witness needed by the direct proof handler.  No post-terminal space is
reconstructed: every premise is either emitted by the first firing or proved
to survive that same sink batch. -/
theorem sourceProofTerminalSuccessor_has_exact_direct_match
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    ExactDirectProofMatch
      (directContextAtBoundary context state after index) item
      (cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective) := by
  let directContext := directContextAtBoundary context state after index
  let successor := cFireReflectiveSourceExecFact
    (sourceProofTerminalSpace context state ledger before after occurrence
      index item) speculativeTerminalDirective
  have control := sourceProofTerminalSuccessor_has_direct_control receipt state
    ledger item
  have heapPresent := sourceProofTerminalSuccessor_retains_heap_row context state
    ledger before after occurrence index item
  have nodePresent := sourceProofTerminalSuccessor_retains_node_row context state
    ledger before after occurrence index item
  have machinePresent := sourceProofTerminalSuccessor_retains_machine_row context
    state ledger before after occurrence index item
  have stackSuccessorPresent :=
    sourceProofTerminalSuccessor_retains_stack_successor context state ledger
      before after occurrence index item
  rcases canonical_slice_instantiates_frame directContext item with
    ⟨substitution, sliceRow, pending, lookup, machine, nextMachine,
      compactStack, normalStack, resumedScan⟩
  refine ⟨substitution, ?_, pending, lookup, machine, nextMachine,
    compactStack, normalStack, resumedScan⟩
  unfold canonicalDirectProofSliceRows at sliceRow
  unfold directProofMatcherRows
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
  rw [speculative_direct_proof_input_exact] at matched ⊢
  apply Conformance.Computable.cmatchPattern_mono []
    (canonicalDirectProofMatchSlice directContext item)
    (speculativeDirectProofDirective.atom :: directProofLive successor)
    _ ?_ _ _ matched
  intro atom member
  simp only [canonicalDirectProofMatchSlice, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with fixed | continuation
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ control.1
      simp [DirectProofContext.pendingRow, extractSupportedSourceExecFact,
        extractRawExecFact]
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ control.2.1
      simp [DirectProofContext.lookupRow, extractSupportedSourceExecFact,
        extractRawExecFact]
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ heapPresent
      simp [heapProofRow, extractSupportedSourceExecFact, extractRawExecFact]
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ nodePresent
      simp [MM2CompressedProofHeapEncoding.nodeRow,
        extractSupportedSourceExecFact, extractRawExecFact]
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ machinePresent
      simp [DirectProofContext.machineRow, extractSupportedSourceExecFact,
        extractRawExecFact]
    · apply List.mem_cons_of_mem
      apply mem_directProofLive_of_mem_of_inert _ stackSuccessorPresent
      simp [DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow,
        extractSupportedSourceExecFact, extractRawExecFact]
  · apply List.mem_cons_of_mem
    apply mem_directProofLive_of_mem_of_inert _
      (sourceProofTerminalSuccessor_retains_continuation context state ledger
        before after occurrence index item atom continuation)
    simp only [directProofContinuationRows, List.mem_cons,
      List.not_mem_nil, or_false] at continuation
    rcases continuation with rfl | rfl | rfl | rfl | rfl <;>
      simp [compressedOwnedRuntimeRuleRow, extractSupportedSourceExecFact,
        extractRawExecFact]

theorem sourceProofTerminalSuccessor_has_direct_supported
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    speculativeDirectProofDirective ∈
      cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective) := by
  have control := sourceProofTerminalSuccessor_has_direct_control receipt state
    ledger item
  unfold cSupportedSourceExecFacts
  rw [List.mem_filterMap]
  exact ⟨compressedDirectProofRule, control.2.2.1,
    extract_speculativeDirectProofDirective_exact⟩

theorem sourceProofTerminalSuccessor_supported_facts_within
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    ∀ candidate ∈ cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective),
      candidate ∈ directLookupInterface := by
  intro candidate member
  unfold cSupportedSourceExecFacts at member
  rw [List.mem_filterMap] at member
  obtain ⟨atom, atomMember, extracted⟩ := member
  exact sourceProofTerminalSuccessor_supported_within receipt state ledger item
    atom atomMember candidate extracted

theorem sourceProofTerminalSuccessor_selects_direct
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    selectNextScheduled
      (cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact
          (sourceProofTerminalSpace context state ledger before after occurrence
            index item) speculativeTerminalDirective)) =
      some speculativeDirectProofDirective := by
  exact select_direct_proof_of_supported_within
    (sourceProofTerminalSuccessor_has_direct_supported receipt state ledger item)
    (sourceProofTerminalSuccessor_supported_facts_within receipt state ledger item)

theorem sourceProofTerminalSuccessor_steps_direct
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    let terminalSuccessor := cFireReflectiveSourceExecFact
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item) speculativeTerminalDirective
    cReflectiveSourceWorkQueueStep .leaveInert terminalSuccessor =
      some
        (cFireReflectiveSourceExecFact terminalSuccessor
          speculativeDirectProofDirective) := by
  dsimp only
  unfold cReflectiveSourceWorkQueueStep
  rw [sourceProofTerminalSuccessor_selects_direct receipt state ledger item]

theorem sourceProofTerminalSuccessor_inhabits_exact_native_type
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (item : ProofOccurrence) :
    let terminalSuccessor := cFireReflectiveSourceExecFact
      (sourceProofTerminalSpace context state ledger before after occurrence
        index item) speculativeTerminalDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies terminalSuccessor
        (reflectiveNativeListExactTargetNativeType .leaveInert
          (cFireReflectiveSourceExecFact terminalSuccessor
            speculativeDirectProofDirective)).pred := by
  dsimp only
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert _ _).2
  exact sourceProofTerminalSuccessor_steps_direct receipt state ledger item

/-- The direct rule fired on the literal terminal successor represents the
same semantic proof occurrence selected by the source heap.  This theorem is
scheduler-neutral: the remaining selection theorem must show that this
already-enabled direct rule is the next least-key executable candidate. -/
theorem sourceProofTerminalSuccessor_direct_fire_represents_hit
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index nodeId : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let directContext := directContextAtBoundary context state after index
      let terminalSuccessor := cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective
      let semanticBefore := displayedProofRequestState state ledger index
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step semanticBefore
          (semanticHitAfter directContext item semanticBefore) ∧
        ExactDirectProofMatch directContext item terminalSuccessor ∧
        RepresentsProofHit context.proofOwner state.stack.length
          (semanticHitAfter directContext item semanticBefore)
          (cFireReflectiveSourceExecFact terminalSuccessor
            speculativeDirectProofDirective) := by
  obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof state ledger index nodeId node heapLookup nodeLookup
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let directContext := directContextAtBoundary context state after index
  let terminalSuccessor := cFireReflectiveSourceExecFact
    (sourceProofTerminalSpace context state ledger before after occurrence
      index item) speculativeTerminalDirective
  let semanticBefore := displayedProofRequestState state ledger index
  have exactMatch : ExactDirectProofMatch directContext item terminalSuccessor :=
    sourceProofTerminalSuccessor_has_exact_direct_match receipt state ledger item
  have heapPresent : heapProofRow context.proofOwner index item ∈
      terminalSuccessor :=
    sourceProofTerminalSuccessor_retains_heap_row context state ledger before
      after occurrence index item
  have nodePresent : MM2CompressedProofHeapEncoding.nodeRow
      context.proofOwner item ∈ terminalSuccessor :=
    sourceProofTerminalSuccessor_retains_node_row context state ledger before
      after occurrence index item
  have heapLive : heapProofRow directContext.proofOwner directContext.index item ∈
      directProofLive terminalSuccessor := by
    apply mem_directProofLive_of_mem_of_inert _ heapPresent
    simp [heapProofRow, extractSupportedSourceExecFact, extractRawExecFact]
  have nodeLive : MM2CompressedProofHeapEncoding.nodeRow
      directContext.proofOwner item ∈ directProofLive terminalSuccessor := by
    apply mem_directProofLive_of_mem_of_inert _ nodePresent
    simp [MM2CompressedProofHeapEncoding.nodeRow, extractSupportedSourceExecFact,
      extractRawExecFact]
  have retainedHeap := direct_fire_retains_heap_row directContext item
    terminalSuccessor heapLive
  have retainedNode := direct_fire_retains_node_row directContext item
    terminalSuccessor nodeLive
  obtain ⟨compactStack, normalStack⟩ :=
    direct_fire_adds_stack_rows directContext item terminalSuccessor exactMatch
  refine ⟨sourceOccurrence, occurrenceLookup, ?_, exactMatch, ?_⟩
  · exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
      (displayedHeap state ledger) 0 index (.occurrence item) displayedLookup
  · exact ⟨index, item, rfl, displayedLookup, retainedHeap, retainedNode,
      compactStack, normalStack⟩

/-- One source-derived proof byte now spans two actual scheduled MM2
transitions.  The terminal publishes the lookup interface; the literal
successor schedules the direct proof hit, inhabits its exact OSLF native type,
and represents the exact semantic heap occurrence. -/
theorem sourceProofTerminal_scheduled_proof_hit_square
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index nodeId : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let directContext := directContextAtBoundary context state after index
      let terminalSuccessor := cFireReflectiveSourceExecFact
        (sourceProofTerminalSpace context state ledger before after occurrence
          index item) speculativeTerminalDirective
      let directSuccessor := cFireReflectiveSourceExecFact terminalSuccessor
        speculativeDirectProofDirective
      let semanticBefore := displayedProofRequestState state ledger index
      cReflectiveSourceWorkQueueStep .leaveInert terminalSuccessor =
          some directSuccessor ∧
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT .leaveInert)).satisfies terminalSuccessor
            (reflectiveNativeListExactTargetNativeType .leaveInert
              directSuccessor).pred ∧
        Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step semanticBefore
          (semanticHitAfter directContext item semanticBefore) ∧
        RepresentsProofHit context.proofOwner state.stack.length
          (semanticHitAfter directContext item semanticBefore) directSuccessor := by
  obtain ⟨sourceOccurrence, occurrenceLookup, semanticStep, _exactMatch,
      represented⟩ :=
    sourceProofTerminalSuccessor_direct_fire_represents_hit receipt state ledger
      node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_, ?_, semanticStep, represented⟩
  · exact sourceProofTerminalSuccessor_steps_direct receipt state ledger
      (displayedProofOccurrence nodeId node sourceOccurrence)
  · exact sourceProofTerminalSuccessor_inhabits_exact_native_type receipt state
      ledger (displayedProofOccurrence nodeId node sourceOccurrence)

#print axioms speculative_terminal_input_exact
#print axioms speculative_terminal_sinks_exact
#print axioms speculative_terminal_atom_surface
#print axioms canonicalTerminalMatchSpace_supported_exact
#print axioms canonicalTerminalMatchSpace_selects_terminal
#print axioms canonicalTerminalMatchSpace_steps
#print axioms canonicalTerminalMatchSpace_inhabits_exact_native_type
#print axioms canonicalTerminalMatchSpace_has_match
#print axioms terminalFinalSubst_instantiates_request
#print axioms terminalFinalSubst_instantiates_runtime_rules
#print axioms canonicalTerminalMatchSpace_read_eq
#print axioms terminalFinalSubst_mem_matcherRows
#print axioms canonicalTerminalMatcherRow_eq
#print axioms canonicalTerminalSuccessor_has_request
#print axioms ProofByteReceipt.terminalPendingRow_eq_direct
#print axioms ProofByteReceipt.terminalLookupRow_eq_direct
#print axioms canonicalTerminalSuccessor_has_direct_control
#print axioms sourceProofTerminalExtraRows_no_supported
#print axioms sourceProofTerminalSpace_supported_exact
#print axioms sourceProofTerminalSpace_selects_terminal
#print axioms sourceProofTerminalSpace_read_eq
#print axioms terminalFinalSubst_mem_sourceProofTerminalMatcherRows
#print axioms sourceProofTerminal_matcher_exact
#print axioms sourceProofTerminalMatcherRow_eq
#print axioms sourceProofTerminalSpace_steps
#print axioms sourceProofTerminalSpace_inhabits_exact_native_type
#print axioms sourceProofTerminalSuccessor_has_direct_control
#print axioms sourceProofTerminalSuccessor_has_exact_direct_match
#print axioms sourceProofTerminalSuccessor_supported_within
#print axioms sourceProofTerminalSuccessor_has_direct_supported
#print axioms sourceProofTerminalSuccessor_supported_facts_within
#print axioms sourceProofTerminalSuccessor_selects_direct
#print axioms sourceProofTerminalSuccessor_steps_direct
#print axioms sourceProofTerminalSuccessor_inhabits_exact_native_type
#print axioms sourceProofTerminalSuccessor_direct_fire_represents_hit
#print axioms sourceProofTerminal_scheduled_proof_hit_square

end Mettapedia.Languages.Metamath.MM2CompressedProofTerminalHitContinuous
