import Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness

/-!
# Capability origin for the speculative compressed-verifier presentation

The speculative lookup pass replaces the terminal scanner rule and derives
two direct lookup handlers.  This module turns that compiler result into the
same family-and-kind-indexed executable authority used by the base verifier.
Unchanged continuation kinds delegate to the base presentation; the three
transformed kinds are read from the compiler artifact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Presentation selected by one successful speculative compiler result.
Only the terminal runtime carrier and the two new speculative handler carriers
change; every other family/kind is resolved by the admitted base inventory. -/
def executablePresentationOf
    (compiled : CompiledPresentation) : CompressedExecutablePresentation where
  resolve
    | .runtime, "terminal" =>
        some compiled.selected.artifact.targetTerminalRule
    | .speculative, "proof" =>
        some compiled.selected.artifact.directProofRule
    | .speculative, "assertion" =>
        some compiled.selected.artifact.directOpaqueRule
    | family, kind => compressedBaseExecutableRule? family kind

def speculativeBaseExecutablePresentation :
    CompressedExecutablePresentation :=
  executablePresentationOf baseCompiledPresentation

@[simp] theorem speculativeBase_resolves_terminal :
    speculativeBaseExecutablePresentation.resolve .runtime "terminal" =
      some compressedSpeculativeTerminalRule := by
  rfl

@[simp] theorem speculativeBase_resolves_direct_proof :
    speculativeBaseExecutablePresentation.resolve .speculative "proof" =
      some compressedDirectProofRule := by
  rfl

@[simp] theorem speculativeBase_resolves_direct_assertion :
    speculativeBaseExecutablePresentation.resolve .speculative "assertion" =
      some compressedDirectAssertionRule := by
  rfl

/-- Typed executable inventory expected after the maintained speculative pass.
It is the base inventory with the terminal payload replaced and the two
compiler-derived speculative handlers appended. -/
def speculativeBaseExecutableCaptures : List CompressedExecutableCapture :=
  [⟨.runtime, "prefix", compressedPrefixRule⟩,
   ⟨.runtime, "terminal", compressedSpeculativeTerminalRule⟩,
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
   ⟨.runtime, "assertion-resume", compressedAssertionResumeRule⟩,
   ⟨.speculative, "proof", compressedDirectProofRule⟩,
   ⟨.speculative, "assertion", compressedDirectAssertionRule⟩]

def speculativeBaseExecutableCaptureRows : List Atom :=
  speculativeBaseExecutableCaptures.map encodeCompressedExecutableCapture

theorem speculativeBaseExecutableCaptureRows_authorized :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      speculativeBaseExecutableCaptureRows := by
  intro carrier member
  rw [speculativeBaseExecutableCaptureRows, List.mem_map] at member
  obtain ⟨capture, captureMember, rfl⟩ := member
  simp only [CompressedExecutableCarrierAuthorized,
    decode_encodeCompressedExecutableCapture]
  rcases capture with ⟨family, kind, payload⟩
  simp only [speculativeBaseExecutableCaptures, List.mem_cons,
    List.not_mem_nil, or_false] at captureMember
  rcases captureMember with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h
  all_goals cases h
  all_goals rfl

/-- Executable carriers in the compiler-produced static target are covered by
the typed transformed inventory.  Non-carrier static data is intentionally
ignored by this check. -/
def speculativeTargetStaticCarrierCoverage : Bool :=
  baseCompiledPresentation.targetStaticRows.all fun row =>
    match decodeCompressedExecutableCapture row with
    | none => true
    | some _ => row ∈ speculativeBaseExecutableCaptureRows

theorem speculativeTargetStaticCarrierCoverage_eq_true :
    speculativeTargetStaticCarrierCoverage = true := by
  decide +kernel

/-- The compiler-produced persistent target rows all satisfy the authority map
derived from the same compiler artifact. -/
theorem speculative_target_static_rows_authorized :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      baseCompiledPresentation.targetStaticRows := by
  intro carrier member
  have covered := (List.all_eq_true.mp
    speculativeTargetStaticCarrierCoverage_eq_true) carrier member
  cases decoded : decodeCompressedExecutableCapture carrier with
  | none => simp [CompressedExecutableCarrierAuthorized, decoded]
  | some capture =>
      simp only [decoded] at covered
      exact speculativeBaseExecutableCaptureRows_authorized carrier
        (by simpa using covered)

/-- Positive transformed control: the replacement terminal is admitted under
the terminal key selected by the compiler result. -/
theorem speculative_terminal_capture_authorized :
    CompressedExecutableCarrierAuthorized
      speculativeBaseExecutablePresentation targetTerminalCaptureRow := by
  simp [targetTerminalCaptureRow, compressedOwnedRuntimeRuleRow,
    CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, speculativeBaseExecutablePresentation,
    executablePresentationOf, baseCompiledPresentation,
    compressedSpeculativeTerminalRule]
  change compressedSpeculativeLookupSelectedArtifact.artifact.targetTerminalRule =
    compressedSpeculativeLookupSelectedArtifact.artifact.targetTerminalRule
  rfl

/-- Positive transformed control: the generated direct proof handler is
admitted only in the speculative proof family. -/
theorem speculative_direct_proof_capture_authorized :
    CompressedExecutableCarrierAuthorized
      speculativeBaseExecutablePresentation compressedDirectProofHandlerRow := by
  simp [compressedDirectProofHandlerRow,
    CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, speculativeBaseExecutablePresentation,
    executablePresentationOf, baseCompiledPresentation,
    compressedDirectProofRule]
  change compressedSpeculativeLookupSelectedArtifact.artifact.directProofRule =
    compressedSpeculativeLookupSelectedArtifact.artifact.directProofRule
  rfl

/-- The replaced source terminal no longer has authority in the transformed
presentation. -/
theorem source_terminal_capture_rejected_after_transform :
    ¬ CompressedExecutableCarrierAuthorized
      speculativeBaseExecutablePresentation sourceTerminalCaptureRow := by
  intro authorized
  have distinct : compressedTerminalRule ≠ compressedSpeculativeTerminalRule := by
    decide +kernel
  simp [sourceTerminalCaptureRow, compressedOwnedRuntimeRuleRow,
    CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, speculativeBaseExecutablePresentation,
    executablePresentationOf] at authorized
  exact distinct authorized.symm

/-- A generated direct proof rule cannot be relabelled as the assertion
handler; family and kind remain part of the capability. -/
theorem swapped_direct_handler_kind_rejected :
    ¬ CompressedExecutableCarrierAuthorized
      speculativeBaseExecutablePresentation
      (.expression
        [.symbol "mm-compressed-owned-speculative-lookup-handler",
          .symbol "assertion", compressedDirectProofRule]) := by
  intro authorized
  have distinct : compressedDirectProofRule ≠ compressedDirectAssertionRule := by
    decide +kernel
  simp [CompressedExecutableCarrierAuthorized,
    decodeCompressedExecutableCapture, speculativeBaseExecutablePresentation,
    executablePresentationOf] at authorized
  exact distinct authorized.symm

/-! ## The transformed presentation at a save boundary -/

def speculativeTargetStaticRowsCleanCheck : Bool :=
  baseCompiledPresentation.targetStaticRows.all fun row =>
    isDynamicRow row == false

theorem speculativeTargetStaticRowsCleanCheck_eq_true :
    speculativeTargetStaticRowsCleanCheck = true := by
  decide +kernel

theorem speculativeTargetStaticRows_clean :
    StaticFrame baseCompiledPresentation.targetStaticRows := by
  intro row member
  have checked := (List.all_eq_true.mp
    speculativeTargetStaticRowsCleanCheck_eq_true) row member
  cases dynamic : isDynamicRow row <;> simp_all

/-- The save-specific structural rows are attached to the actual transformed
persistent code inventory. -/
def speculativeSaveStaticFrame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) : List Atom :=
  [compressedSaveDirective.atom,
   compressedIndexSuccessorRow
     (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   compressedIndexSuccessorRow
     (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom] ++
    baseCompiledPresentation.targetStaticRows

theorem speculativeSaveStaticFrame_clean
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    StaticFrame (speculativeSaveStaticFrame context before stackTopPosition) := by
  intro row member
  simp only [speculativeSaveStaticFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with fixed | transformed
  · rcases fixed with rfl | rfl | rfl
    all_goals
      simp [isDynamicRow, dynamicRowHeads, compressedSaveDirective,
        compressedSaveRule, compressedIndexSuccessorRow,
        compressedStackOwner, compressedHeapOwner]
  · exact speculativeTargetStaticRows_clean row transformed

theorem speculativeSaveStaticFrame_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      (speculativeSaveStaticFrame context before stackTopPosition) := by
  intro row member
  simp only [speculativeSaveStaticFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with fixed | transformed
  · rcases fixed with rfl | rfl | rfl
    all_goals
      simp [CompressedExecutableCarrierAuthorized,
        decodeCompressedExecutableCapture, compressedSaveDirective,
        compressedSaveRule, compressedIndexSuccessorRow,
        compressedStackOwner, compressedHeapOwner]
  · exact speculative_target_static_rows_authorized row transformed

private def hasExpressionHead (expected : String) : Atom -> Bool
  | .expression (.symbol head :: _) => head == expected
  | _ => false

private def speculativeTargetStaticNoIndexSuccessorCheck : Bool :=
  baseCompiledPresentation.targetStaticRows.all fun row =>
    !hasExpressionHead "mm-compressed-index-successor" row

private theorem speculativeTargetStaticNoIndexSuccessorCheck_eq_true :
    speculativeTargetStaticNoIndexSuccessorCheck = true := by
  decide +kernel

theorem speculativeTargetStaticRows_no_index_successor
    (row : Atom) (member : row ∈ baseCompiledPresentation.targetStaticRows)
    (owner current next : Atom) :
    row ≠ compressedIndexSuccessorRow owner current next := by
  have checked := (List.all_eq_true.mp
    speculativeTargetStaticNoIndexSuccessorCheck_eq_true) row member
  intro equal
  subst row
  simp [hasExpressionHead, compressedIndexSuccessorRow] at checked

/-- The compiler-produced presentation shares the source-indexed heap
frontier discipline even though its captured runtime rule inventory differs
from the base presentation. -/
theorem speculativeSaveStaticFrame_heapAuthority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    SaveHeapFrontierAuthority context before
      (speculativeSaveStaticFrame context before stackTopPosition) := by
  refine
    { directive := by simp [speculativeSaveStaticFrame]
      successor := by simp [speculativeSaveStaticFrame]
      functional := ?_ }
  intro next member
  simp only [speculativeSaveStaticFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (save | stack | heap) | transformed
  · have rawEqual := congrArg extractRawExecFact save
    simp [compressedSaveDirective, compressedSaveRule,
      compressedIndexSuccessorRow, extractRawExecFact] at rawEqual
  · simp [compressedIndexSuccessorRow, compressedStackOwner,
      compressedHeapOwner] at stack
  · simpa [compressedIndexSuccessorRow] using heap
  · exact False.elim
      (speculativeTargetStaticRows_no_index_successor _ transformed
        (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom next rfl)

/-- The compiler-produced static presentation supplies both source-indexed
frontier edges, including uniqueness of the stack predecessor consumed by
the save matcher. -/
theorem speculativeSaveStaticFrame_frontierAuthority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    SaveFrontierAuthority context before stackTopPosition
      (speculativeSaveStaticFrame context before stackTopPosition) := by
  refine
    { directive := by simp [speculativeSaveStaticFrame]
      stackSuccessor := by simp [speculativeSaveStaticFrame]
      stackPredecessorFunctional := ?_
      heapSuccessor := by simp [speculativeSaveStaticFrame]
      heapSuccessorFunctional :=
        (speculativeSaveStaticFrame_heapAuthority context before
          stackTopPosition).functional }
  intro previous member
  simp only [speculativeSaveStaticFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (save | stack | heap) | transformed
  · have rawEqual := congrArg extractRawExecFact save
    simp [compressedSaveDirective, compressedSaveRule,
      compressedIndexSuccessorRow, extractRawExecFact] at rawEqual
  · simpa [compressedIndexSuccessorRow] using stack
  · simp [compressedIndexSuccessorRow, compressedStackOwner,
      compressedHeapOwner] at heap
  · exact False.elim
      (speculativeTargetStaticRows_no_index_successor _ transformed
        (compressedStackOwner context.proofOwner) previous
        (CompressedIndexCode.ofNat before.stack.length).atom rfl)

/-- The runtime bundle selected by the speculative compiler.  Only its
terminal field differs from the base save bundle; the direct handlers belong
to later lookup stages rather than the save matcher itself. -/
def speculativeSaveRuntimeRuleBundle : SaveRuntimeRuleBundle where
  prefixRule := compressedPrefixRule
  terminalRule := compressedSpeculativeTerminalRule
  proofRule := compressedProofStepRule
  invalidByteRule := compressedInvalidByteRule
  questionRule := compressedQuestionRule
  questionOpenFaultRule := compressedQuestionOpenFaultRule

def speculativeSaveRuntimeRuleAuthority :
    SaveRuntimeRuleAuthority speculativeBaseExecutablePresentation where
  rules := speculativeSaveRuntimeRuleBundle
  prefixResolved := rfl
  terminalResolved := speculativeBase_resolves_terminal
  proofResolved := rfl
  invalidByteResolved := rfl
  questionResolved := rfl
  questionOpenFaultResolved := rfl
  prefixStatic := by
    simp [speculativeSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedPrefixRule]
  terminalStatic := by decide +kernel
  proofStatic := by
    simp [speculativeSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedProofStepRule]
  invalidByteStatic := by
    simp [speculativeSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedInvalidByteRule]
  questionStatic := by
    simp [speculativeSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedQuestionRule]
  questionOpenFaultStatic := by
    simp [speculativeSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedQuestionOpenFaultRule]

/-- Every runtime payload activated by the speculative save is an ordinary
four-field executable directive. -/
theorem speculativeSaveRuntimeRuleBundle_payload_exec_shape
    (row : Atom)
    (member : row ∈ speculativeSaveRuntimeRuleBundle.payloadRows) :
    ∃ tail, row = .expression (.symbol "exec" :: tail) ∧ tail.length = 3 := by
  simp only [SaveRuntimeRuleBundle.payloadRows,
    speculativeSaveRuntimeRuleBundle, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- Activated runtime code cannot share a physical key with either moving
save control.  This is a compact-encoding head theorem, not an assumption
that static and dynamic rows are globally disjoint by fiat. -/
theorem speculativeSaveRuntimeRuleBundle_payload_key_ne_save_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (row : Atom)
    (member : row ∈ speculativeSaveRuntimeRuleBundle.payloadRows) :
    morkSupportKey row ≠ morkSupportKey (scannerRow context scanner) ∧
      morkSupportKey row ≠ morkSupportKey (machineRow context state) := by
  obtain ⟨tail, rfl, tailLength⟩ :=
    speculativeSaveRuntimeRuleBundle_payload_exec_shape row member
  constructor
  · unfold scannerRow
    apply morkSupportKey_expression_symbol_head_ne
    · omega
    · simp
    · decide
    · decide
    · decide
    · decide
    · decide
  · unfold machineRow
    apply morkSupportKey_expression_symbol_head_ne
    · omega
    · simp
    · decide
    · decide
    · decide
    · decide
    · decide

def speculativeSaveRuntimeCaptureCoverage : Bool :=
  speculativeSaveRuntimeRuleBundle.captureRows.all fun row =>
    row ∈ baseCompiledPresentation.targetStaticRows

theorem speculativeSaveRuntimeCaptureCoverage_eq_true :
    speculativeSaveRuntimeCaptureCoverage = true := by
  decide +kernel

theorem speculativeSaveRuntimeCaptureRows_mem_target
    (row : Atom) (member : row ∈ speculativeSaveRuntimeRuleBundle.captureRows) :
    row ∈ baseCompiledPresentation.targetStaticRows := by
  have checked := speculativeSaveRuntimeCaptureCoverage_eq_true
  unfold speculativeSaveRuntimeCaptureCoverage at checked
  exact of_decide_eq_true ((List.all_eq_true.mp checked) row member)

theorem speculativeSaveStaticFrame_supportFor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context before
      stackTopPosition
      (speculativeSaveStaticFrame context before stackTopPosition) := by
  exact
    { directive := by simp [speculativeSaveStaticFrame]
      stackSuccessor := by simp [speculativeSaveStaticFrame]
      heapSuccessor := by simp [speculativeSaveStaticFrame]
      captures := by
        intro row member
        apply List.mem_append_right
        exact speculativeSaveRuntimeCaptureRows_mem_target row member }

def speculativeSaveBoundarySpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) : List Atom :=
  canonicalBoundaryRows context state ledger scanner ++
    speculativeSaveStaticFrame context state stackTopPosition

/-! ## Exact transformed scheduler boundary -/

/-- Finite compiler-artifact check: none of the transformed persistent carrier
rows is itself a scheduler-visible directive.  The executable payloads remain
inert until an admitted directive republishes them. -/
def speculativeTargetStaticNoSupportedCheck : Bool :=
  baseCompiledPresentation.targetStaticRows.all fun row =>
    (extractSupportedSourceExecFact row).isNone

theorem speculativeTargetStaticNoSupportedCheck_eq_true :
    speculativeTargetStaticNoSupportedCheck = true := by
  decide +kernel

theorem speculativeTargetStaticRows_no_supported :
    cSupportedSourceExecFacts
        baseCompiledPresentation.targetStaticRows = [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  have checked := speculativeTargetStaticNoSupportedCheck_eq_true
  unfold speculativeTargetStaticNoSupportedCheck at checked
  have rowChecked := (List.all_eq_true.mp checked) row member
  exact Option.isNone_iff_eq_none.mp rowChecked

/-- Every row reconstructed from a source compressed-proof boundary is
dynamic and hence cannot compete with the admitted save directive. -/
theorem canonicalBoundaryRows_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary) :
    ∀ row, row ∈ canonicalBoundaryRows context state ledger scanner →
      isDynamicRow row = true := by
  intro row member
  simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with fixed | passive
  · rcases fixed with rfl | rfl
    · exact machineRow_isDynamic context state
    · exact scannerRow_isDynamic context scanner
  · exact canonicalPassiveRows_all_dynamic context state ledger row passive

theorem canonicalBoundaryRows_no_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary) :
    cSupportedSourceExecFacts
        (canonicalBoundaryRows context state ledger scanner) = [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  exact extractSupportedSourceExecFact_eq_none_of_dynamic row
    (canonicalBoundaryRows_all_dynamic context state ledger scanner row member)

/-- The transformed static save frame has exactly one scheduled directive;
the compiled runtime rules are inert typed carriers. -/
theorem speculativeSaveStaticFrame_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (stackTopPosition : Nat) :
    cSupportedSourceExecFacts
        (speculativeSaveStaticFrame context state stackTopPosition) =
      [compressedSaveDirective] := by
  unfold speculativeSaveStaticFrame cSupportedSourceExecFacts
  rw [List.filterMap_append]
  have transformed :
      List.filterMap extractSupportedSourceExecFact
          baseCompiledPresentation.targetStaticRows = [] := by
    simpa [cSupportedSourceExecFacts] using
      speculativeTargetStaticRows_no_supported
  rw [transformed, List.append_nil]
  have saveExact :
      extractSupportedSourceExecFact compressedSaveDirective.atom =
        some compressedSaveDirective := by
    rfl
  have stackInert :
      extractSupportedSourceExecFact
        (compressedIndexSuccessorRow
          (compressedStackOwner context.proofOwner)
          (CompressedIndexCode.ofNat stackTopPosition).atom
          (CompressedIndexCode.ofNat state.stack.length).atom) = none := by
    rfl
  have heapInert :
      extractSupportedSourceExecFact
        (compressedIndexSuccessorRow
          (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat state.heap.length).atom
          (CompressedIndexCode.ofNat (state.heap.length + 1)).atom) = none := by
    rfl
  simp only [List.filterMap_cons, List.filterMap_nil, saveExact, stackInert,
    heapInert]

/-- Source-derived dynamic rows do not alter the exact transformed scheduler
inventory. -/
theorem speculativeSaveBoundarySpace_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) :
    cSupportedSourceExecFacts
        (speculativeSaveBoundarySpace context state ledger scanner
          stackTopPosition) = [compressedSaveDirective] := by
  unfold speculativeSaveBoundarySpace cSupportedSourceExecFacts
  rw [List.filterMap_append]
  have dynamicRows :
      List.filterMap extractSupportedSourceExecFact
          (canonicalBoundaryRows context state ledger scanner) = [] := by
    simpa [cSupportedSourceExecFacts] using
      canonicalBoundaryRows_no_supported context state ledger scanner
  have staticRows :
      List.filterMap extractSupportedSourceExecFact
          (speculativeSaveStaticFrame context state stackTopPosition) =
        [compressedSaveDirective] := by
    simpa [cSupportedSourceExecFacts] using
      speculativeSaveStaticFrame_supported context state stackTopPosition
  rw [dynamicRows, staticRows]
  rfl

/-- The ordinary reflective scheduler takes the real save transition on the
complete transformed boundary. -/
theorem speculativeSaveBoundarySpace_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (speculativeSaveBoundarySpace context state ledger scanner
          stackTopPosition) =
      some (cFireReflectiveSourceExecFact
        (speculativeSaveBoundarySpace context state ledger scanner
          stackTopPosition) compressedSaveDirective) := by
  unfold cReflectiveSourceWorkQueueStep
  rw [speculativeSaveBoundarySpace_supported]
  rfl

/-- Any physical presentation of the same source-derived save boundary has
the same singleton scheduler inventory.  Storage order is irrelevant; row
multiplicity is controlled by `PhysicalRunningBoundary`. -/
theorem physical_speculative_save_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space) :
    cSupportedSourceExecFacts space = [compressedSaveDirective] := by
  have perm := represented.supportedFacts_perm
  have canonical :
      cSupportedSourceExecFacts
          (canonicalBoundaryRows context state ledger scanner ++
            speculativeSaveStaticFrame context state stackTopPosition) =
        [compressedSaveDirective] := by
    simpa [speculativeSaveBoundarySpace] using
      speculativeSaveBoundarySpace_supported context state ledger scanner
        stackTopPosition
  rw [canonical] at perm
  simpa using perm

/-- A save directive admitted by an arbitrary represented static frame is
physically present in every permutation of that boundary. -/
theorem physical_save_directive_mem_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame) :
    compressedSaveDirective.atom ∈ space := by
  apply (represented.exact_rows compressedSaveDirective.atom).2
  apply List.mem_append_right
  exact directivePresent

/-- The specialized compiler-produced save frame contains the save directive. -/
theorem physical_speculative_save_directive_mem
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space) :
    compressedSaveDirective.atom ∈ space := by
  exact physical_save_directive_mem_of_frame represented
    (by simp [speculativeSaveStaticFrame])

/-- On any represented frame containing the save directive, compact-key
removal is exactly ordinary one-row erasure. -/
theorem physical_save_live_eq_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame) :
    morkEraseSupport space compressedSaveDirective.atom =
      space.erase compressedSaveDirective.atom := by
  exact morkEraseSupport_eq_erase_of_mem space compressedSaveDirective.atom
    represented.list_nodup represented.mork_nodup
    (physical_save_directive_mem_of_frame represented directivePresent)

theorem physical_speculative_save_live_eq
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space) :
    morkEraseSupport space compressedSaveDirective.atom =
      space.erase compressedSaveDirective.atom := by
  exact physical_save_live_eq_of_frame represented
    (by simp [speculativeSaveStaticFrame])

/-- The physical and reflective read copies are permutations for any admitted
frame. Their order differs because physical insertion appends. -/
theorem physical_save_read_perm_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame) :
    (morkInsertSupport
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.atom).Perm
      (compressedSaveDirective.atom ::
        space.erase compressedSaveDirective.atom) := by
  rw [physical_save_live_eq_of_frame represented directivePresent]
  have absent : morkSupportContains
      (space.erase compressedSaveDirective.atom)
        compressedSaveDirective.atom = false := by
    rw [← physical_save_live_eq_of_frame represented directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      compressedSaveDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact
    (List.perm_append_singleton compressedSaveDirective.atom
      (space.erase compressedSaveDirective.atom))

theorem physical_speculative_save_read_perm
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space) :
    (morkInsertSupport
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.atom).Perm
      (compressedSaveDirective.atom ::
        space.erase compressedSaveDirective.atom) := by
  exact physical_save_read_perm_of_frame represented
    (by simp [speculativeSaveStaticFrame])

/-- Save matcher membership is invariant between physical and reflective read
copies for every admitted frame. This is membership, not list equality. -/
theorem physical_save_matcher_mem_iff_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedSaveDirective.atom)
            compressedSaveDirective.atom)
          compressedSaveDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedSaveDirective.atom ::
            space.erase compressedSaveDirective.atom)
          compressedSaveDirective.rule.input := by
  rw [compressedSaveDirective_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  let physicalRead :=
    morkInsertSupport
      (morkEraseSupport space compressedSaveDirective.atom)
      compressedSaveDirective.atom
  let reflectiveRead :=
    compressedSaveDirective.atom :: space.erase compressedSaveDirective.atom
  have readPerm : physicalRead.Perm reflectiveRead := by
    exact physical_save_read_perm_of_frame represented directivePresent
  constructor
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] physicalRead
      reflectiveRead (mkPattern savePatterns)
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] reflectiveRead
      physicalRead (mkPattern savePatterns)
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

theorem physical_speculative_save_matcher_mem_iff
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedSaveDirective.atom)
            compressedSaveDirective.atom)
          compressedSaveDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedSaveDirective.atom ::
            space.erase compressedSaveDirective.atom)
          compressedSaveDirective.rule.input := by
  exact physical_save_matcher_mem_iff_of_frame represented
    (by simp [speculativeSaveStaticFrame]) substitution consumed

/-- Matcher substitutions used by the actual rule-scoped save firing. -/
def physicalSaveMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space compressedSaveDirective.atom
  let read := morkInsertSupport live compressedSaveDirective.atom
  ((cMatchInputSpecMork [] read compressedSaveDirective.rule.input).filter fun
      (substitution, _) =>
        matchSourceGuards substitution compressedSaveDirective.rule.guards).map
    Prod.fst

/-- Every physical save matcher substitution from an arbitrary admitted frame
is also one of the reflective substitutions. -/
theorem physicalSaveMatcherRows_subset_saveMatcherRows_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {substitution : Subst}
    (member : substitution ∈ physicalSaveMatcherRows space) :
    substitution ∈ saveMatcherRows space := by
  unfold physicalSaveMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  have matched :
      (matchedSubstitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedSaveDirective.atom)
            compressedSaveDirective.atom)
          compressedSaveDirective.rule.input :=
    (List.mem_filter.mp filtered).1
  have reflective :=
    (physical_save_matcher_mem_iff_of_frame represented directivePresent
      matchedSubstitution consumed).1 matched
  subst substitution
  exact List.mem_map_of_mem reflective

theorem physicalSaveMatcherRows_subset_saveMatcherRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space)
    {substitution : Subst}
    (member : substitution ∈ physicalSaveMatcherRows space) :
    substitution ∈ saveMatcherRows space := by
  exact physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
    (by simp [speculativeSaveStaticFrame]) member

/-- Every save sink uses only variables bound by the authored save input. -/
theorem compressedSaveDirective_sinks_variablesInherited :
    ruleSinksVariablesInherited compressedSaveDirective.rule.input
      compressedSaveDirective.rule.tmpl.sinks = true := by
  decide +kernel

/-- Exact source-derived save observations reconstructed by the matcher used
by the physical rule-scoped firing.  This is intentionally separate from
`ExactSaveMatch`: every output equality below uses the rule-scoped
instantiator that the MORK transition actually executes. -/
def PhysicalExactSaveMatch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary) (item : ProofOccurrence)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalSaveMatcherRows space,
    instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveScanTemplate =
        some (scannerRow context scannerBefore) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveMachineTemplate =
        some (machineRow context before) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item)

/-- The physical matcher contains the exact source save witness for every
permutation of the represented boundary.  No target substitution is supplied:
the witness is reconstructed from the source stack, node table, occurrence
ledger, scanner receipt, and action step. -/
theorem physical_source_save_exact_match_of_support
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame) :
    PhysicalExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence) space := by
  let stackTopPosition := before.stack.length - 1
  have included := source_save_canonical_read_included_for
    speculativeSaveRuntimeRuleBundle ledger represented.semantic stackTop
      nodeLookup occurrenceLookup support
  have reflectiveExact :
      ExactSaveMatch context before after scannerBefore scannerAfter
        (displayedProofOccurrence nodeId node sourceOccurrence) space :=
    (canonicalSaveMatchSpaceFor_exact_match receipt step
      speculativeSaveRuntimeRuleBundle stackTopPosition
      (displayedProofOccurrence nodeId node sourceOccurrence)).mono_read included
  rcases reflectiveExact with
    ⟨substitution, substitutionMember, scanBefore, machineBefore,
      machineAfter, scanAfter, heapAfter, receiptAfter⟩
  unfold saveMatcherRows at substitutionMember
  rw [List.mem_map] at substitutionMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, equal⟩ :=
    substitutionMember
  subst substitution
  have physicalMatched :
      (matchedSubstitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedSaveDirective.atom)
            compressedSaveDirective.atom)
          compressedSaveDirective.rule.input :=
    (physical_save_matcher_mem_iff_of_frame represented support.directive
      matchedSubstitution consumed).2 matched
  have physicalMember :
      matchedSubstitution ∈ physicalSaveMatcherRows space := by
    have filtered :
        (matchedSubstitution, consumed) ∈
          (cMatchInputSpecMork []
            (morkInsertSupport
              (morkEraseSupport space compressedSaveDirective.atom)
              compressedSaveDirective.atom)
            compressedSaveDirective.rule.input).filter fun
              (candidate, _) =>
                matchSourceGuards candidate
                  compressedSaveDirective.rule.guards :=
      List.mem_filter.mpr
        ⟨physicalMatched, by
          change matchSourceGuards matchedSubstitution [] = true
          rfl⟩
    rw [show physicalSaveMatcherRows space =
        ((cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedSaveDirective.atom)
            compressedSaveDirective.atom)
          compressedSaveDirective.rule.input).filter fun
            (candidate, _) =>
              matchSourceGuards candidate
                compressedSaveDirective.rule.guards).map Prod.fst by rfl]
    exact List.mem_map_of_mem filtered
  refine ⟨matchedSubstitution, physicalMember, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact scanBefore
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact machineBefore
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact machineAfter
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact scanAfter
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact heapAfter
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact receiptAfter
    · decide +kernel

theorem physical_source_save_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space) :
    PhysicalExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence) space := by
  exact physical_source_save_exact_match_of_support ledger receipt step
    stackTop nodeLookup occurrenceLookup represented
    (speculativeSaveStaticFrame_supportFor context before
      (before.stack.length - 1))

/-- The four dynamic successor rows are instantiated by actual add sinks of
the physical save firing.  This theorem records exact sink provenance; it does
not confuse instantiation with survival under compact-key insertion. -/
theorem physical_exact_save_match_dynamic_additions
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    {space : List Atom}
    (matched : PhysicalExactSaveMatch context before after scannerBefore
      scannerAfter item space) :
    RuleScopedAddedAtom compressedSaveDirective.rule.input
        (physicalSaveMatcherRows space)
        compressedSaveDirective.rule.tmpl.sinks (machineRow context after) ∧
      RuleScopedAddedAtom compressedSaveDirective.rule.input
        (physicalSaveMatcherRows space)
        compressedSaveDirective.rule.tmpl.sinks
        (scannerRow context scannerAfter) ∧
      RuleScopedAddedAtom compressedSaveDirective.rule.input
        (physicalSaveMatcherRows space)
        compressedSaveDirective.rule.tmpl.sinks
        (heapProofRow context.proofOwner before.heap.length item) ∧
      RuleScopedAddedAtom compressedSaveDirective.rule.input
        (physicalSaveMatcherRows space)
        compressedSaveDirective.rule.tmpl.sinks
        (saveReceiptRow context.proofOwner before.heap.length item) := by
  rcases matched with
    ⟨substitution, substitutionMember, _scanBefore, _machineBefore,
      machineAfter, scanAfter, heapAfter, receiptAfter⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨.add afterSaveMachineTemplate, by
      rw [compressedSaveDirective_sinks_exact]
      simp, afterSaveMachineTemplate, rfl, substitution,
        substitutionMember, machineAfter⟩
  · exact ⟨.add afterSaveScanTemplate, by
      rw [compressedSaveDirective_sinks_exact]
      simp, afterSaveScanTemplate, rfl, substitution,
        substitutionMember, scanAfter⟩
  · exact ⟨.add savedHeapTemplate, by
      rw [compressedSaveDirective_sinks_exact]
      simp, savedHeapTemplate, rfl, substitution,
        substitutionMember, heapAfter⟩
  · exact ⟨.add saveReceiptTemplate, by
      rw [compressedSaveDirective_sinks_exact]
      simp, saveReceiptTemplate, rfl, substitution,
        substitutionMember, receiptAfter⟩

/-- Source identities and exact physical matcher/output provenance for a save
step.  The occurrence is recovered from the source ledger at the stack-top
node selected by `ActionStep.save`; it is not carried by the target as an
independent authority. -/
def PhysicalSaveOutputWitness
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary) (space : List Atom) : Prop :=
  ∃ nodeId node sourceOccurrence,
    before.stack.getLast? = some nodeId ∧
      before.nodes[nodeId]? = some node ∧
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      PhysicalExactSaveMatch context before after scannerBefore scannerAfter
        (displayedProofOccurrence nodeId node sourceOccurrence) space

theorem physical_save_output_witness_dynamic_additions
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary} {space : List Atom}
    (witness : PhysicalSaveOutputWitness context before after ledger
      scannerBefore scannerAfter space) :
    ∃ nodeId node sourceOccurrence,
      before.stack.getLast? = some nodeId ∧
        before.nodes[nodeId]? = some node ∧
        ledger.occurrences[nodeId]? = some sourceOccurrence ∧
        RuleScopedAddedAtom compressedSaveDirective.rule.input
            (physicalSaveMatcherRows space)
            compressedSaveDirective.rule.tmpl.sinks
            (machineRow context after) ∧
        RuleScopedAddedAtom compressedSaveDirective.rule.input
            (physicalSaveMatcherRows space)
            compressedSaveDirective.rule.tmpl.sinks
            (scannerRow context scannerAfter) ∧
        RuleScopedAddedAtom compressedSaveDirective.rule.input
            (physicalSaveMatcherRows space)
            compressedSaveDirective.rule.tmpl.sinks
            (heapProofRow context.proofOwner before.heap.length
              (displayedProofOccurrence nodeId node sourceOccurrence)) ∧
        RuleScopedAddedAtom compressedSaveDirective.rule.input
            (physicalSaveMatcherRows space)
            compressedSaveDirective.rule.tmpl.sinks
            (saveReceiptRow context.proofOwner before.heap.length
              (displayedProofOccurrence nodeId node sourceOccurrence)) := by
  rcases witness with
    ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
      occurrenceLookup, matched⟩
  exact ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
    occurrenceLookup,
    physical_exact_save_match_dynamic_additions matched⟩

/-- Every physical source-derived save step reconstructs its output witness
without accepting a target-authored occurrence or substitution. -/
def physical_save_output_witness
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space) :
    PhysicalSaveOutputWitness context before after ledger scannerBefore
      scannerAfter space := by
  obtain ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
      occurrenceLookup, _heapExact⟩ := displayedHeap_save_exact ledger 0 step
  exact ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
    occurrenceLookup,
    physical_source_save_exact_match ledger receipt step stackTop nodeLookup
      occurrenceLookup represented⟩

def saveAdministrativeSinks : List Sink :=
  [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .remove saveScanTemplate, .remove saveMachineTemplate]

def saveDynamicOutputSinks : List Sink :=
  [.add afterSaveMachineTemplate, .add afterSaveScanTemplate,
   .add savedHeapTemplate, .add saveReceiptTemplate]

private theorem compressedSaveDirective_sinks_split :
    compressedSaveDirective.rule.tmpl.sinks =
      saveAdministrativeSinks ++ saveDynamicOutputSinks := by
  rfl

/-- Exact physical carrier shape after the administrative save sinks and the
four source-derived dynamic additions have run. -/
def physicalSaveSuccessorResult (space : List Atom) (rows : List Subst)
    (machineAfter scanAfter heapAfter receiptAfter : Atom) : List Atom :=
  let live := morkEraseSupport space compressedSaveDirective.atom
  let administrative :=
    cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows live
      saveAdministrativeSinks
  let afterMachine := morkUnionSupport administrative [machineAfter]
  let afterScan := morkUnionSupport afterMachine [scanAfter]
  let afterHeap := morkUnionSupport afterScan [heapAfter]
  morkUnionSupport afterHeap [receiptAfter]

/-- If every matcher row instantiates one sink to the same atom, independent
physical staging produces exactly one representative. -/
private theorem foldl_stageRuleScopedSink_singleton_of_all_exact
    (input : InputSpec) (sink : Sink) (rows : List Subst) (atom : Atom)
    (nonempty : rows ≠ [])
    (instantiates : ∀ substitution ∈ rows,
      instantiateRuleTemplateAtom? input substitution sink.atom = some atom) :
    rows.foldl (stageRuleScopedSink input sink) [] = [atom] := by
  cases rows with
  | nil => simp at nonempty
  | cons first rest =>
    simp only [List.foldl_cons]
    have firstExact := instantiates first (by simp)
    have firstStage :
        stageRuleScopedSink input sink [] first = [atom] := by
      simp [stageRuleScopedSink, firstExact, morkInsertSupport,
        morkSupportContains, morkSupportFind?, sameMorkSupportAtom]
    rw [firstStage]
    have tailFixed : ∀ remaining : List Subst,
        (∀ substitution ∈ remaining,
          instantiateRuleTemplateAtom? input substitution sink.atom =
            some atom) →
        remaining.foldl (stageRuleScopedSink input sink) [atom] = [atom] := by
      intro remaining allExact
      induction remaining with
      | nil => rfl
      | cons head tail induction =>
          simp only [List.foldl_cons]
          have headExact := allExact head (by simp)
          have headStage :
              stageRuleScopedSink input sink [atom] head = [atom] := by
            simp [stageRuleScopedSink, headExact, morkInsertSupport,
              morkSupportContains, morkSupportFind?, sameMorkSupportAtom]
          rw [headStage]
          apply induction
          intro substitution member
          exact allExact substitution (by simp [member])
    exact tailFixed rest fun substitution member =>
      instantiates substitution (by simp [member])

/-- Every physical matcher row over an arbitrary admitted frame computes the
same four dynamic save outputs.  The frame contributes finite cursor
authority but cannot contribute an alternative source observation. -/
theorem physical_save_matcher_dynamic_rows_exact_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (substitution : Subst) (rowMember : substitution ∈
      physicalSaveMatcherRows space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item) := by
  dsimp only
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      frontier.directive rowMember
  have controls := saveMatcherRow_successor_controls_exact receipt step
    represented.semantic frontier.heapFrontier reflectiveMember
  have outputs := saveMatcherRow_saved_outputs_exact receipt step stackTop
    nodeLookup occurrenceLookup represented.semantic frontier reflectiveMember
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact controls.1
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact controls.2.1
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact outputs.1
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact outputs.2
    · decide +kernel

/-- Every physical matcher row computes the same four dynamic save outputs.
The speculative compiler frame is one instance of the frame-parametric
statement above. -/
theorem physical_save_matcher_dynamic_rows_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space)
    (substitution : Subst) (rowMember : substitution ∈
      physicalSaveMatcherRows space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item) := by
  exact physical_save_matcher_dynamic_rows_exact_of_frame ledger receipt step
    stackTop nodeLookup occurrenceLookup represented
    (speculativeSaveStaticFrame_frontierAuthority context before
      (before.stack.length - 1)) substitution rowMember

/-- Every matcher row used by the key-aware physical save removes exactly the
represented predecessor scanner and machine controls.  Rule scoping changes
coverage policy for output-local variables, but these two templates inherit
all of their variables from the input pattern. -/
theorem physical_save_matcher_predecessor_controls_exact_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {substitution : Subst}
    (rowMember : substitution ∈ physicalSaveMatcherRows space) :
    instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
        substitution saveScanTemplate = some (scannerRow context scanner) ∧
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
        substitution saveMachineTemplate = some (machineRow context before) := by
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      directivePresent rowMember
  have exact := saveMatcherRow_predecessor_controls_exact represented.semantic
    directivePresent reflectiveMember
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact exact.1
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact exact.2
    · decide +kernel

/-- A physical matcher row re-instantiates the self factor exactly when its
source replay is known.  Coverage is reconstructed from the actual match; it
is not inferred merely from the supplied replay equality. -/
theorem physical_save_matcher_self_instantiation_exact_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {substitution : Subst}
    (rowMember : substitution ∈ physicalSaveMatcherRows space)
    (replay :
      applySubst substitution saveSelfTemplate = compressedSaveDirective.atom) :
    instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
        substitution saveSelfTemplate = some compressedSaveDirective.atom := by
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      directivePresent rowMember
  have origin : ∃ beforeFactor afterFactor carrier,
      carrier ∈ compressedSaveDirective.atom :: saveLive space ∧
        Conformance.Computable.cmatchAtom beforeFactor saveSelfTemplate carrier =
          some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution saveSelfTemplate = carrier :=
    Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
      (compressedSaveDirective.atom :: saveLive space)
      (mkPattern savePatterns) saveSelfTemplate
      (by simp [savePatterns, mkPattern]) reflectiveMember
  obtain ⟨beforeFactor, afterFactor, carrier, _carrierMember, matched,
      finalExtends, _carrierReplay⟩ := origin
  have coveredAtMatch : templateCovered afterFactor saveSelfTemplate = true :=
    Conformance.Computable.cmatchAtom_templateCovered beforeFactor
      saveSelfTemplate carrier afterFactor matched
  have covered : templateCovered substitution saveSelfTemplate = true :=
    Conformance.Computable.templateCovered_of_lookupExtends finalExtends
      saveSelfTemplate coveredAtMatch
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
  · exact (instantiateTemplateAtom_of_covered substitution saveSelfTemplate
      covered).trans (congrArg some replay)
  · decide +kernel

/-- Any input row other than the consumed directive survives the physical
save when its compact key differs from the two exact predecessor controls.
All add sinks are harmless; the preceding theorem discharges the only two
remove sinks for every matcher assignment. -/
theorem physical_save_preserves_input_row_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (row : Atom) (rowMember : row ∈ space)
    (notDirective : row ≠ compressedSaveDirective.atom)
    (notScannerKey :
      morkSupportKey row ≠ morkSupportKey (scannerRow context scanner))
    (notMachineKey :
      morkSupportKey row ≠ morkSupportKey (machineRow context before)) :
    row ∈ cFireRuleScopedSourceExecFact space compressedSaveDirective := by
  let rows := physicalSaveMatcherRows space
  have liveMember :
      row ∈ morkEraseSupport space compressedSaveDirective.atom := by
    rw [physical_save_live_eq_of_frame represented directivePresent]
    exact (List.mem_erase_of_ne notDirective).2 rowMember
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change row ∈ cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input
      rows (morkEraseSupport space compressedSaveDirective.atom)
      compressedSaveDirective.rule.tmpl.sinks
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    compressedSaveDirective.rule.input rows
  · intro sink sinkMember
    rw [compressedSaveDirective_sinks_exact] at sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨saveScanTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented directivePresent substitutionMember
          have removedExact : removed = scannerRow context scanner :=
            Option.some.inj (instantiated.symm.trans exact.1)
          simpa [removedExact] using notScannerKey⟩
      | exact Or.inr ⟨saveMachineTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented directivePresent substitutionMember
          have removedExact : removed = machineRow context before :=
            Option.some.inj (instantiated.symm.trans exact.2)
          simpa [removedExact] using notMachineKey⟩
  · exact liveMember

/-- The complete physical save result has one exact quotient-carrier shape.
All matcher rows agree on the four source-derived outputs, so support-valued
staging contributes exactly one representative of each output key. -/
theorem physical_save_result_exact_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame) :
    let rows := physicalSaveMatcherRows space
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    cFireRuleScopedSourceExecFact space compressedSaveDirective =
      physicalSaveSuccessorResult space rows
        (machineRow context after) (scannerRow context scannerAfter)
        (heapProofRow context.proofOwner before.heap.length item)
        (saveReceiptRow context.proofOwner before.heap.length item) := by
  dsimp only
  let rows := physicalSaveMatcherRows space
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let machineAfter := machineRow context after
  let scanAfter := scannerRow context scannerAfter
  let heapAfter := heapProofRow context.proofOwner before.heap.length item
  let receiptAfter :=
    saveReceiptRow context.proofOwner before.heap.length item
  have matcherExact : ∀ substitution ∈ rows,
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate = some machineAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate = some scanAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate = some heapAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate = some receiptAfter := by
    intro substitution member
    simpa [rows, item, machineAfter, scanAfter, heapAfter, receiptAfter] using
      physical_save_matcher_dynamic_rows_exact_of_frame ledger receipt step
        stackTop nodeLookup occurrenceLookup represented frontier substitution
        member
  have rowsNonempty : rows ≠ [] := by
    have matched := physical_source_save_exact_match_of_support ledger receipt
      step stackTop nodeLookup occurrenceLookup represented support
    rcases matched with ⟨substitution, member, _⟩
    have member' : substitution ∈ rows := by simpa [rows] using member
    intro empty
    rw [empty] at member'
    simp at member'
  have stagedMachine :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add afterSaveMachineTemplate)) [] = [machineAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add afterSaveMachineTemplate) rows
      machineAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).1
  have stagedScan :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add afterSaveScanTemplate)) [] = [scanAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add afterSaveScanTemplate) rows
      scanAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.1
  have stagedHeap :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add savedHeapTemplate)) [] = [heapAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add savedHeapTemplate) rows
      heapAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.2.1
  have stagedReceipt :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add saveReceiptTemplate)) [] = [receiptAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add saveReceiptTemplate) rows
      receiptAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.2.2
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      compressedSaveDirective.rule.tmpl.sinks = _
  rw [compressedSaveDirective_sinks_split,
    cApplyRuleScopedSinkBatch_append]
  simp only [saveDynamicOutputSinks, cApplyRuleScopedSinkBatch,
    finalizeRuleScopedSink, stagedMachine, stagedScan, stagedHeap,
    stagedReceipt]
  rfl

/-- A physical save consumes both moving predecessor controls.  The proof is
about the actual key-aware sink batch: the matched removes establish absence,
and the four later source-derived additions cannot recreate either control. -/
theorem physical_save_consumes_old_controls_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame) :
    machineRow context before ∉
        cFireRuleScopedSourceExecFact space compressedSaveDirective ∧
      scannerRow context scannerBefore ∉
        cFireRuleScopedSourceExecFact space compressedSaveDirective := by
  let rows := physicalSaveMatcherRows space
  have matched := physical_source_save_exact_match_of_support ledger receipt
    step stackTop nodeLookup occurrenceLookup represented support
  rcases matched with
    ⟨witness, witnessMember, witnessScan, witnessMachine,
      _witnessMachineAfter, _witnessScanAfter, _witnessHeap,
      _witnessReceipt⟩
  have matcherExact : ∀ substitution ∈ rows,
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate =
            some (machineRow context after) ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate =
            some (scannerRow context scannerAfter) ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate =
            some (heapProofRow context.proofOwner before.heap.length
              (displayedProofOccurrence nodeId node sourceOccurrence)) ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate =
            some (saveReceiptRow context.proofOwner before.heap.length
              (displayedProofOccurrence nodeId node sourceOccurrence)) := by
    intro substitution member
    simpa [rows] using
      physical_save_matcher_dynamic_rows_exact_of_frame ledger receipt step
        stackTop nodeLookup occurrenceLookup represented frontier substitution
        member
  have machineDifferent :
      machineRow context after ≠ machineRow context before := by
    cases step
    simp only [machineRow, List.length_append, List.length_singleton]
    intro equal
    have atomsEqual := Atom.expression.inj equal
    have tail1 := (List.cons.inj atomsEqual).2
    have tail2 := (List.cons.inj tail1).2
    have tail3 := (List.cons.inj tail2).2
    have heapEqual := (List.cons.inj tail3).1
    have codeEqual :=
      MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective heapEqual
    have lengthEqual :=
      MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective codeEqual
    omega
  have scannerDifferent :
      scannerRow context scannerAfter ≠ scannerRow context scannerBefore := by
    intro equal
    have atomsEqual := Atom.expression.inj equal
    have tail1 := (List.cons.inj atomsEqual).2
    have tail2 := (List.cons.inj tail1).2
    have tail3 := (List.cons.inj tail2).2
    have tail4 := (List.cons.inj tail3).2
    have tail5 := (List.cons.inj tail4).2
    have phaseEqual := (List.cons.inj tail5).1
    simp [receipt.phase_before, receipt.phase_after, ScannerPhase.atom] at phaseEqual
  have machineNotScan :
      machineRow context after ≠ scannerRow context scannerBefore := by
    simp [machineRow, scannerRow]
  have heapNotScan :
      heapProofRow context.proofOwner before.heap.length
          (displayedProofOccurrence nodeId node sourceOccurrence) ≠
        scannerRow context scannerBefore := by
    simp [heapProofRow, scannerRow]
  have receiptNotScan :
      saveReceiptRow context.proofOwner before.heap.length
          (displayedProofOccurrence nodeId node sourceOccurrence) ≠
        scannerRow context scannerBefore := by
    simp [saveReceiptRow, scannerRow]
  have scanNotMachine :
      scannerRow context scannerAfter ≠ machineRow context before := by
    simp [scannerRow, machineRow]
  have heapNotMachine :
      heapProofRow context.proofOwner before.heap.length
          (displayedProofOccurrence nodeId node sourceOccurrence) ≠
        machineRow context before := by
    simp [heapProofRow, machineRow]
  have receiptNotMachine :
      saveReceiptRow context.proofOwner before.heap.length
          (displayedProofOccurrence nodeId node sourceOccurrence) ≠
        machineRow context before := by
    simp [saveReceiptRow, machineRow]
  have scannerAbsent : scannerRow context scannerBefore ∉
      cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.rule.tmpl.sinks := by
    rw [compressedSaveDirective_sinks_exact]
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule")]
      saveScanTemplate (scannerRow context scannerBefore)
      [.remove saveMachineTemplate, .add afterSaveMachineTemplate,
       .add afterSaveScanTemplate, .add savedHeapTemplate,
       .add saveReceiptTemplate] witness
      (by simpa [rows] using witnessMember) witnessScan
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨saveMachineTemplate, rfl⟩
    · exact Or.inr ⟨afterSaveMachineTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).1]
        exact fun equal => machineNotScan (Option.some.inj equal)⟩
    · exact Or.inr ⟨afterSaveScanTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.1]
        exact fun equal => scannerDifferent (Option.some.inj equal)⟩
    · exact Or.inr ⟨savedHeapTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.2.1]
        exact fun equal => heapNotScan (Option.some.inj equal)⟩
    · exact Or.inr ⟨saveReceiptTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.2.2]
        exact fun equal => receiptNotScan (Option.some.inj equal)⟩
  have machineAbsent : machineRow context before ∉
      cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.rule.tmpl.sinks := by
    rw [compressedSaveDirective_sinks_exact]
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule"),
       .remove saveScanTemplate]
      saveMachineTemplate (machineRow context before)
      [.add afterSaveMachineTemplate, .add afterSaveScanTemplate,
       .add savedHeapTemplate, .add saveReceiptTemplate] witness
      (by simpa [rows] using witnessMember) witnessMachine
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨afterSaveMachineTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).1]
        exact fun equal => machineDifferent (Option.some.inj equal)⟩
    · exact Or.inr ⟨afterSaveScanTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.1]
        exact fun equal => scanNotMachine (Option.some.inj equal)⟩
    · exact Or.inr ⟨savedHeapTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.2.1]
        exact fun equal => heapNotMachine (Option.some.inj equal)⟩
    · exact Or.inr ⟨saveReceiptTemplate, rfl, by
        intro substitution member
        rw [(matcherExact substitution member).2.2.2]
        exact fun equal => receiptNotMachine (Option.some.inj equal)⟩
  simpa [cFireRuleScopedSourceExecFact, cApplyRuleScopedTemplate, rows,
    physicalSaveMatcherRows] using
    And.intro machineAbsent scannerAbsent

/-- The actual MORK result contains the four source-determined successor rows
by physical support identity.  This is stronger than merely exhibiting output
templates and is stable under the carrier's erase/append order.  Exact nominal
membership is the subsequent ground-key faithfulness obligation. -/
theorem physical_save_successor_support_present_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    morkSupportContains result (machineRow context after) = true ∧
      morkSupportContains result (scannerRow context scannerAfter) = true ∧
      morkSupportContains result
        (heapProofRow context.proofOwner before.heap.length item) = true ∧
      morkSupportContains result
        (saveReceiptRow context.proofOwner before.heap.length item) = true := by
  dsimp only
  let rows := physicalSaveMatcherRows space
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let machineAfter := machineRow context after
  let scanAfter := scannerRow context scannerAfter
  let heapAfter := heapProofRow context.proofOwner before.heap.length item
  let receiptAfter :=
    saveReceiptRow context.proofOwner before.heap.length item
  have matcherExact : ∀ substitution ∈ rows,
      instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveMachineTemplate = some machineAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution afterSaveScanTemplate = some scanAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution savedHeapTemplate = some heapAfter ∧
        instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
          substitution saveReceiptTemplate = some receiptAfter := by
    intro substitution member
    simpa [rows, item, machineAfter, scanAfter, heapAfter, receiptAfter] using
      physical_save_matcher_dynamic_rows_exact_of_frame ledger receipt step
        stackTop nodeLookup occurrenceLookup represented frontier substitution
        member
  have rowsNonempty : rows ≠ [] := by
    have matched := physical_source_save_exact_match_of_support ledger receipt
      step stackTop nodeLookup occurrenceLookup represented support
    rcases matched with ⟨substitution, member, _⟩
    have member' : substitution ∈ rows := by simpa [rows] using member
    intro empty
    rw [empty] at member'
    simp at member'
  have stagedMachine :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add afterSaveMachineTemplate)) [] = [machineAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add afterSaveMachineTemplate) rows
      machineAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).1
  have stagedScan :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add afterSaveScanTemplate)) [] = [scanAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add afterSaveScanTemplate) rows
      scanAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.1
  have stagedHeap :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add savedHeapTemplate)) [] = [heapAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add savedHeapTemplate) rows
      heapAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.2.1
  have stagedReceipt :
      rows.foldl
          (stageRuleScopedSink compressedSaveDirective.rule.input
            (.add saveReceiptTemplate)) [] = [receiptAfter] :=
    foldl_stageRuleScopedSink_singleton_of_all_exact
      compressedSaveDirective.rule.input (.add saveReceiptTemplate) rows
      receiptAfter rowsNonempty fun substitution member =>
        (matcherExact substitution member).2.2.2
  let live := morkEraseSupport space compressedSaveDirective.atom
  let administrative :=
    cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows live
      saveAdministrativeSinks
  let afterMachine := morkUnionSupport administrative [machineAfter]
  let afterScan := morkUnionSupport afterMachine [scanAfter]
  let afterHeap := morkUnionSupport afterScan [heapAfter]
  let afterReceipt := morkUnionSupport afterHeap [receiptAfter]
  have machineAtMachine :
      morkSupportContains afterMachine machineAfter = true := by
    exact morkSupportContains_morkUnionSupport_of_mem_staged administrative
      [machineAfter] machineAfter (by simp)
  have machineAtReceipt :
      morkSupportContains afterReceipt machineAfter = true := by
    apply morkSupportContains_morkUnionSupport_of_contains
    apply morkSupportContains_morkUnionSupport_of_contains
    apply morkSupportContains_morkUnionSupport_of_contains
    exact machineAtMachine
  have scanAtScan : morkSupportContains afterScan scanAfter = true := by
    exact morkSupportContains_morkUnionSupport_of_mem_staged afterMachine
      [scanAfter] scanAfter (by simp)
  have scanAtReceipt :
      morkSupportContains afterReceipt scanAfter = true := by
    apply morkSupportContains_morkUnionSupport_of_contains
    apply morkSupportContains_morkUnionSupport_of_contains
    exact scanAtScan
  have heapAtHeap : morkSupportContains afterHeap heapAfter = true := by
    exact morkSupportContains_morkUnionSupport_of_mem_staged afterScan
      [heapAfter] heapAfter (by simp)
  have heapAtReceipt :
      morkSupportContains afterReceipt heapAfter = true := by
    apply morkSupportContains_morkUnionSupport_of_contains
    exact heapAtHeap
  have receiptAtReceipt :
      morkSupportContains afterReceipt receiptAfter = true := by
    exact morkSupportContains_morkUnionSupport_of_mem_staged afterHeap
      [receiptAfter] receiptAfter (by simp)
  have resultExact :
      cFireRuleScopedSourceExecFact space compressedSaveDirective =
        afterReceipt := by
    unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
    change cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
      live compressedSaveDirective.rule.tmpl.sinks = afterReceipt
    rw [compressedSaveDirective_sinks_split,
      cApplyRuleScopedSinkBatch_append]
    simp only [saveDynamicOutputSinks, cApplyRuleScopedSinkBatch,
      finalizeRuleScopedSink, stagedMachine, stagedScan, stagedHeap,
      stagedReceipt]
    rfl
  rw [resultExact]
  exact ⟨machineAtReceipt, scanAtReceipt, heapAtReceipt, receiptAtReceipt⟩

/-- All six runtime directives activated from protected capture rows are
physically present after the save.  Their authored add positions are tracked
individually, while the only later removes are proved to target the exact old
scanner and machine keys. -/
theorem physical_save_runtime_payload_support_present_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation staticFrame)
    (row : Atom)
    (payloadMember : row ∈ speculativeSaveRuntimeRuleBundle.payloadRows) :
    morkSupportContains
      (cFireRuleScopedSourceExecFact space compressedSaveDirective) row = true := by
  let rows := physicalSaveMatcherRows space
  have matched := physical_source_save_exact_match_of_support ledger receipt
    step stackTop nodeLookup occurrenceLookup represented support
  rcases matched with ⟨witness, witnessMember, _⟩
  have witnessMember' : witness ∈ rows := by
    simpa [rows] using witnessMember
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      support.directive witnessMember'
  have runtime := saveMatcherRow_runtime_rules_exact_of_resolved
    speculativeBaseExecutablePresentation represented.semantic
    support.directive capabilities
    speculativeSaveRuntimeRuleBundle.prefixRule
    speculativeSaveRuntimeRuleBundle.terminalRule
    speculativeSaveRuntimeRuleBundle.proofRule
    speculativeSaveRuntimeRuleBundle.invalidByteRule
    speculativeSaveRuntimeRuleBundle.questionRule
    speculativeSaveRuntimeRuleBundle.questionOpenFaultRule
    speculativeSaveRuntimeRuleAuthority.prefixResolved
    speculativeSaveRuntimeRuleAuthority.terminalResolved
    speculativeSaveRuntimeRuleAuthority.proofResolved
    speculativeSaveRuntimeRuleAuthority.invalidByteResolved
    speculativeSaveRuntimeRuleAuthority.questionResolved
    speculativeSaveRuntimeRuleAuthority.questionOpenFaultResolved
    reflectiveMember
  have controlKeys :=
    speculativeSaveRuntimeRuleBundle_payload_key_ne_save_controls context before
      scannerBefore row payloadMember
  have sinksSafe : ∀ sink ∈ compressedSaveDirective.rule.tmpl.sinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows, ∀ removed,
            instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
                substitution authored = some removed →
              morkSupportKey row ≠ morkSupportKey removed := by
    intro sink sinkMember
    rw [compressedSaveDirective_sinks_exact] at sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨saveScanTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented support.directive substitutionMember
          have removedExact : removed = scannerRow context scannerBefore :=
            Option.some.inj (instantiated.symm.trans exact.1)
          simpa [removedExact] using controlKeys.1⟩
      | exact Or.inr ⟨saveMachineTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented support.directive substitutionMember
          have removedExact : removed = machineRow context before :=
            Option.some.inj (instantiated.symm.trans exact.2)
          simpa [removedExact] using controlKeys.2⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change morkSupportContains
      (cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.rule.tmpl.sinks) row = true
  rw [compressedSaveDirective_sinks_exact]
  simp only [SaveRuntimeRuleBundle.payloadRows,
    speculativeSaveRuntimeRuleBundle, List.mem_cons, List.not_mem_nil,
    or_false] at payloadMember
  rcases payloadMember with rfl | rfl | rfl | rfl | rfl | rfl
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate] (.var "compressed-prefix-rule")
      speculativeSaveRuntimeRuleBundle.prefixRule _ witness witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.1
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule")]
      (.var "compressed-terminal-rule")
      speculativeSaveRuntimeRuleBundle.terminalRule _ witness witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.2.1
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule")]
      (.var "compressed-proof-rule")
      speculativeSaveRuntimeRuleBundle.proofRule _ witness witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.2.2.1
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule")]
      (.var "compressed-invalid-byte-rule")
      speculativeSaveRuntimeRuleBundle.invalidByteRule _ witness witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.2.2.2.1
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule")]
      (.var "compressed-question-rule")
      speculativeSaveRuntimeRuleBundle.questionRule _ witness witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.2.2.2.2.1
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])
  · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      compressedSaveDirective.rule.input rows
      (morkEraseSupport space compressedSaveDirective.atom)
      [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule")]
      (.var "compressed-question-open-fault-rule")
      speculativeSaveRuntimeRuleBundle.questionOpenFaultRule _ witness
      witnessMember'
    · rw [instantiateRuleTemplateAtom?_inputVariable]
      · exact runtime.2.2.2.2.2
      · decide +kernel
    · intro sink member
      exact sinksSafe sink (by simp [member, compressedSaveDirective_sinks_exact])

/-- Specialized support-presence theorem for the maintained speculative
compiler frame. -/
theorem physical_save_successor_support_present
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    morkSupportContains result (machineRow context after) = true ∧
      morkSupportContains result (scannerRow context scannerAfter) = true ∧
      morkSupportContains result
        (heapProofRow context.proofOwner before.heap.length item) = true ∧
      morkSupportContains result
        (saveReceiptRow context.proofOwner before.heap.length item) = true := by
  exact physical_save_successor_support_present_of_frame ledger receipt step
    stackTop nodeLookup occurrenceLookup represented
    (speculativeSaveStaticFrame_supportFor context before
      (before.stack.length - 1))
    (speculativeSaveStaticFrame_frontierAuthority context before
      (before.stack.length - 1))

/-- Any exact atom introduced by a rule-scoped save add sink over an arbitrary
admitted frame has a matching reflective addition witness.  This transfers
the established source-derived output classification without equating the two
storage algorithms. -/
theorem physical_save_added_to_reflective_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {atom : Atom}
    (added : RuleScopedAddedAtom compressedSaveDirective.rule.input
      (physicalSaveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom) :
    ReflectiveAddedAtom (saveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom := by
  rcases added with
    ⟨sink, sinkMember, authored, rfl, substitution, rowMember, instantiated⟩
  refine ⟨.add authored, sinkMember, authored, rfl, substitution,
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      directivePresent rowMember, ?_⟩
  have sinkInherited :
      ruleSinkVariablesInherited compressedSaveDirective.rule.input
        (.add authored) = true :=
    (List.all_eq_true.mp compressedSaveDirective_sinks_variablesInherited)
      (.add authored) sinkMember
  have inherited :
      ruleTemplateVariablesInherited compressedSaveDirective.rule.input
        authored = true := by
    change ruleTemplateVariablesInherited compressedSaveDirective.rule.input
      authored = true at sinkInherited
    exact sinkInherited
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    compressedSaveDirective.rule.input substitution authored inherited]
    at instantiated
  exact instantiated

/-- Specialized addition bridge for the maintained speculative frame. -/
theorem physical_save_added_to_reflective
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space)
    {atom : Atom}
    (added : RuleScopedAddedAtom compressedSaveDirective.rule.input
      (physicalSaveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom) :
    ReflectiveAddedAtom (saveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom := by
  exact physical_save_added_to_reflective_of_frame represented
    (by simp [speculativeSaveStaticFrame]) added

/-- The authored save template contains only support-valued add and remove
sinks. -/
theorem compressedSaveDirective_supportSet :
    ReflectiveSupportSetTemplate compressedSaveDirective.rule.tmpl := by
  intro sink sinkMember
  rw [compressedSaveDirective_sinks_exact] at sinkMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (subst sink; trivial)

/-- The existing source-derived save-output classification applies to every
exact dynamic atom introduced by a physical rule-scoped sink batch over an
arbitrary admitted frame. -/
theorem physical_save_added_dynamic_atom_exact_of_frame
    (presentation : CompressedExecutablePresentation)
    (runtimeAuthority : SaveRuntimeRuleAuthority presentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    {atom : Atom}
    (added : RuleScopedAddedAtom compressedSaveDirective.rule.input
      (physicalSaveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom)
    (dynamic : isDynamicRow atom = true) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    atom = machineRow context after ∨
      atom = scannerRow context scannerAfter ∨
      atom = heapProofRow context.proofOwner before.heap.length item ∨
      atom = saveReceiptRow context.proofOwner before.heap.length item := by
  exact save_added_dynamic_atom_exact
    presentation runtimeAuthority
    receipt step stackTop nodeLookup occurrenceLookup represented.semantic
    frontier capabilities
    (physical_save_added_to_reflective_of_frame represented
      frontier.directive added) dynamic

/-- Under an exact self-replay premise, every non-dynamic atom added by a
physical save belongs to the successor static frame: either it was the save
directive itself or it is one of the six admitted runtime payloads activated
from protected capture rows. -/
theorem physical_save_added_nondynamic_mem_frame_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation staticFrame)
    (selfExact : ∀ substitution ∈ physicalSaveMatcherRows space,
      applySubst substitution saveSelfTemplate = compressedSaveDirective.atom)
    {atom : Atom}
    (added : RuleScopedAddedAtom compressedSaveDirective.rule.input
      (physicalSaveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom)
    (nondynamic : isDynamicRow atom = false) :
    atom ∈ staticFrame ++ speculativeSaveRuntimeRuleBundle.payloadRows := by
  rcases added with
    ⟨sink, sinkMember, authored, sinkExact, substitution,
      substitutionMember, instantiated⟩
  rw [compressedSaveDirective_sinks_exact] at sinkMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      support.directive substitutionMember
  have runtime := saveMatcherRow_runtime_rules_exact_of_resolved
    speculativeBaseExecutablePresentation represented.semantic
    support.directive capabilities
    speculativeSaveRuntimeRuleBundle.prefixRule
    speculativeSaveRuntimeRuleBundle.terminalRule
    speculativeSaveRuntimeRuleBundle.proofRule
    speculativeSaveRuntimeRuleBundle.invalidByteRule
    speculativeSaveRuntimeRuleBundle.questionRule
    speculativeSaveRuntimeRuleBundle.questionOpenFaultRule
    speculativeSaveRuntimeRuleAuthority.prefixResolved
    speculativeSaveRuntimeRuleAuthority.terminalResolved
    speculativeSaveRuntimeRuleAuthority.proofResolved
    speculativeSaveRuntimeRuleAuthority.invalidByteResolved
    speculativeSaveRuntimeRuleAuthority.questionResolved
    speculativeSaveRuntimeRuleAuthority.questionOpenFaultResolved
    reflectiveMember
  have outputs :=
    physical_save_matcher_dynamic_rows_exact_of_frame ledger receipt step
      stackTop nodeLookup occurrenceLookup represented frontier substitution
      substitutionMember
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals cases sinkExact
  · have exact := selfExact substitution substitutionMember
    have atomExact : atom = compressedSaveDirective.atom := by
      unfold instantiateRuleTemplateAtom? at instantiated
      split at instantiated
      · exact (Option.some.inj instantiated).symm.trans exact
      · contradiction
    subst atom
    exact List.mem_append_left _ support.directive
  · have atomExact : atom = speculativeSaveRuntimeRuleBundle.prefixRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.1,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom = speculativeSaveRuntimeRuleBundle.terminalRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.2.1,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom = speculativeSaveRuntimeRuleBundle.proofRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.2.2.1,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom = speculativeSaveRuntimeRuleBundle.invalidByteRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.2.2.2.1,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom = speculativeSaveRuntimeRuleBundle.questionRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.2.2.2.2.1,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom =
        speculativeSaveRuntimeRuleBundle.questionOpenFaultRule := by
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
        at instantiated
      · simpa [instantiateTemplateAtom?, templateCovered, runtime.2.2.2.2.2,
          applySubst] using instantiated.symm
      · decide +kernel
    subst atom
    exact List.mem_append_right _ (by
      simp [SaveRuntimeRuleBundle.payloadRows])
  · have atomExact : atom = machineRow context after :=
      (Option.some.inj (outputs.1.symm.trans instantiated)).symm
    subst atom
    rw [machineRow_isDynamic context after] at nondynamic
    contradiction
  · have atomExact : atom = scannerRow context scannerAfter :=
      (Option.some.inj (outputs.2.1.symm.trans instantiated)).symm
    subst atom
    rw [scannerRow_isDynamic context scannerAfter] at nondynamic
    contradiction
  · have atomExact : atom = heapProofRow context.proofOwner
        before.heap.length
        (displayedProofOccurrence nodeId node sourceOccurrence) :=
      (Option.some.inj (outputs.2.2.1.symm.trans instantiated)).symm
    subst atom
    simp [heapProofRow, isDynamicRow, dynamicRowHeads] at nondynamic
  · have atomExact : atom = saveReceiptRow context.proofOwner
        before.heap.length
        (displayedProofOccurrence nodeId node sourceOccurrence) :=
      (Option.some.inj (outputs.2.2.2.symm.trans instantiated)).symm
    subst atom
    simp [saveReceiptRow, isDynamicRow, dynamicRowHeads] at nondynamic

/-- Every exact representative surviving a physical save belongs to the full
source-derived successor presentation.  The successor static frame includes
the six runtime rules activated by the save; obsolete machine and scanner
controls are excluded by the actual rule-scoped remove sinks. -/
theorem physical_save_result_rows_within_successor_of_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (support : SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context
      before (before.stack.length - 1) staticFrame)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation staticFrame)
    (selfExact : ∀ substitution ∈ physicalSaveMatcherRows space,
      applySubst substitution saveSelfTemplate = compressedSaveDirective.atom)
    (row : Atom)
    (member : row ∈
      cFireRuleScopedSourceExecFact space compressedSaveDirective) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ++
      (staticFrame ++ speculativeSaveRuntimeRuleBundle.payloadRows) := by
  dsimp only
  have oldAbsent := physical_save_consumes_old_controls_of_frame ledger receipt
    step stackTop nodeLookup occurrenceLookup represented support frontier
  unfold cFireRuleScopedSourceExecFact at member
  change row ∈ cApplyRuleScopedTemplate compressedSaveDirective.rule.input
      (morkEraseSupport space compressedSaveDirective.atom)
      (physicalSaveMatcherRows space) compressedSaveDirective.rule.tmpl at member
  rcases mem_cApplyRuleScopedTemplate_of_supportSet
      compressedSaveDirective.rule.input
      (morkEraseSupport space compressedSaveDirective.atom)
      (physicalSaveMatcherRows space) compressedSaveDirective.rule.tmpl
      compressedSaveDirective_supportSet member with prior | added
  · have sourceMember : row ∈ space := (List.mem_filter.mp prior).1
    have representedMember := (represented.exact_rows row).1 sourceMember
    rcases List.mem_append.mp representedMember with canonical | static
    · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at canonical
      rcases canonical with (rfl | rfl) | passive
      · exact False.elim (oldAbsent.1 member)
      · exact False.elim (oldAbsent.2 member)
      · have passiveAfter :=
          (canonicalPassiveRows_save_iff represented.semantic.source_wellFormed ledger
            proofPosition step nodeId node sourceOccurrence stackTop nodeLookup
            occurrenceLookup row).2 (Or.inl passive)
        apply List.mem_append_left
        simp [canonicalBoundaryRows, passiveAfter]
    · exact List.mem_append_right _
        (List.mem_append_left _ static)
  · cases dynamic : isDynamicRow row with
    | false =>
        exact List.mem_append_right _
          (physical_save_added_nondynamic_mem_frame_of_frame ledger receipt
            step stackTop nodeLookup occurrenceLookup represented support
            frontier capabilities selfExact added dynamic)
    | true =>
        have exactAdded := physical_save_added_dynamic_atom_exact_of_frame
          speculativeBaseExecutablePresentation
          speculativeSaveRuntimeRuleAuthority receipt step stackTop nodeLookup
          occurrenceLookup represented frontier capabilities added dynamic
        rcases exactAdded with rfl | rfl | heapExact | receiptExact
        · exact List.mem_append_left _ (by simp [canonicalBoundaryRows])
        · exact List.mem_append_left _ (by simp [canonicalBoundaryRows])
        · apply List.mem_append_left
          have passiveAfter :=
            (canonicalPassiveRows_save_iff represented.semantic.source_wellFormed ledger
              proofPosition step nodeId node sourceOccurrence stackTop
              nodeLookup occurrenceLookup _).2
              (Or.inr (Or.inl heapExact))
          simp [canonicalBoundaryRows, passiveAfter]
        · apply List.mem_append_left
          have passiveAfter :=
            (canonicalPassiveRows_save_iff represented.semantic.source_wellFormed ledger
              proofPosition step nodeId node sourceOccurrence stackTop
              nodeLookup occurrenceLookup _).2
              (Or.inr (Or.inr receiptExact))
          simp [canonicalBoundaryRows, passiveAfter]

/-- Specialized dynamic addition classification for the maintained
speculative frame. -/
theorem physical_save_added_dynamic_atom_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space)
    {atom : Atom}
    (added : RuleScopedAddedAtom compressedSaveDirective.rule.input
      (physicalSaveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom)
    (dynamic : isDynamicRow atom = true) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    atom = machineRow context after ∨
      atom = scannerRow context scannerAfter ∨
      atom = heapProofRow context.proofOwner before.heap.length item ∨
      atom = saveReceiptRow context.proofOwner before.heap.length item := by
  exact physical_save_added_dynamic_atom_exact_of_frame
    speculativeBaseExecutablePresentation speculativeSaveRuntimeRuleAuthority
    receipt step stackTop nodeLookup occurrenceLookup represented
    (speculativeSaveStaticFrame_frontierAuthority context before
      (before.stack.length - 1))
    (speculativeSaveStaticFrame_capabilities context before
      (before.stack.length - 1)) added dynamic

/-- Every dynamic atom in a physical save result over an arbitrary admitted
frame either came from the represented source boundary or is one of the four
source-determined save outputs. -/
theorem physical_save_dynamic_no_invention_of_frame
    (presentation : CompressedExecutablePresentation)
    (runtimeAuthority : SaveRuntimeRuleAuthority presentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (frontier : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    {atom : Atom}
    (member : atom ∈
      cFireRuleScopedSourceExecFact space compressedSaveDirective)
    (dynamic : isDynamicRow atom = true) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    atom ∈ canonicalBoundaryRows context before ledger scannerBefore ∨
      atom = machineRow context after ∨
      atom = scannerRow context scannerAfter ∨
      atom = heapProofRow context.proofOwner before.heap.length item ∨
      atom = saveReceiptRow context.proofOwner before.heap.length item := by
  dsimp only
  unfold cFireRuleScopedSourceExecFact at member
  change atom ∈ cApplyRuleScopedTemplate
      compressedSaveDirective.rule.input
      (morkEraseSupport space compressedSaveDirective.atom)
      (physicalSaveMatcherRows space) compressedSaveDirective.rule.tmpl at member
  rcases mem_cApplyRuleScopedTemplate_of_supportSet
      compressedSaveDirective.rule.input
      (morkEraseSupport space compressedSaveDirective.atom)
      (physicalSaveMatcherRows space) compressedSaveDirective.rule.tmpl
      compressedSaveDirective_supportSet member with prior | added
  · have sourceMember : atom ∈ space :=
      (List.mem_filter.mp prior).1
    have representedMember := (represented.semantic.exact_rows atom).1 sourceMember
    rcases List.mem_append.mp representedMember with canonical | static
    · exact Or.inl canonical
    · have clean := represented.semantic.staticFrame_clean atom static
      rw [dynamic] at clean
      contradiction
  · exact Or.inr
      (physical_save_added_dynamic_atom_exact_of_frame presentation
        runtimeAuthority receipt step stackTop nodeLookup occurrenceLookup
        represented frontier capabilities added dynamic)

/-- Specialized dynamic no-invention theorem for the maintained speculative
frame. -/
theorem physical_save_dynamic_no_invention
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space)
    {atom : Atom}
    (member : atom ∈
      cFireRuleScopedSourceExecFact space compressedSaveDirective)
    (dynamic : isDynamicRow atom = true) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    atom ∈ canonicalBoundaryRows context before ledger scannerBefore ∨
      atom = machineRow context after ∨
      atom = scannerRow context scannerAfter ∨
      atom = heapProofRow context.proofOwner before.heap.length item ∨
      atom = saveReceiptRow context.proofOwner before.heap.length item := by
  exact physical_save_dynamic_no_invention_of_frame
    speculativeBaseExecutablePresentation speculativeSaveRuntimeRuleAuthority
    receipt step stackTop nodeLookup occurrenceLookup represented
    (speculativeSaveStaticFrame_frontierAuthority context before
      (before.stack.length - 1))
    (speculativeSaveStaticFrame_capabilities context before
      (before.stack.length - 1)) member dynamic

/-- The actual rule-scoped MORK scheduler selects save from every physical
presentation of the source-derived boundary. -/
theorem physical_speculative_save_ruleScoped_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {stackTopPosition : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (speculativeSaveStaticFrame context state stackTopPosition) space) :
    cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (cFireRuleScopedSourceExecFact space compressedSaveDirective) := by
  unfold cRuleScopedSourceWorkQueueStep
  rw [physical_speculative_save_supported represented]
  rfl

/-- One source-derived physical save is a nonempty, one-transition MORK
segment whose target is classified by the OSLF generated from the actual
rule-scoped execution relation. -/
structure PhysicalSaveScheduledSegment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence)
    (staticFrame space result : List Atom) : Type where
  scannerReceipt : SaveByteReceipt context scannerBefore scannerAfter occurrence
  sourceStep : ActionStep before .save after
  representedBefore : PhysicalRunningBoundary context before ledger
    scannerBefore staticFrame space
  sourceOutput : PhysicalSaveOutputWitness context before after ledger
    scannerBefore scannerAfter space
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert space = some result
  nativeType :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (ruleScopedNativeListExecGSLT .leaveInert)).satisfies space
        (ruleScopedNativeListExactTargetNativeType .leaveInert result).pred
  trace : CRuleScopedTrace .leaveInert 1 space result
  traceSteps : trace.steps = 1
  resultListNodup : result.Nodup
  resultMorkNodup : MorkSupportNodup result

def physical_speculative_save_scheduled_segment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    {space : List Atom}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (sourceStep : ActionStep before .save after)
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1)) space) :
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    PhysicalSaveScheduledSegment context before after ledger scannerBefore
      scannerAfter occurrence
      (speculativeSaveStaticFrame context before
        (before.stack.length - 1))
      space result := by
  dsimp only
  have moved := physical_speculative_save_ruleScoped_step represented
  have preserved := physical_boundary_ruleScoped_step_nodup represented
    .leaveInert moved
  have sourceOutput := physical_save_output_witness ledger receipt sourceStep
    represented
  let executionTrace : CRuleScopedTrace .leaveInert 1 space
      (cFireRuleScopedSourceExecFact space compressedSaveDirective) :=
    .step moved (.refl)
  exact
    { scannerReceipt := receipt
      sourceStep := sourceStep
      representedBefore := represented
      sourceOutput := sourceOutput
      concreteStep := moved
      nativeType :=
        (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          .leaveInert space
          (cFireRuleScopedSourceExecFact space compressedSaveDirective)).2 moved
      trace := executionTrace
      traceSteps := by rfl
      resultListNodup := preserved.1
      resultMorkNodup := preserved.2 }

/-- The same scheduled transformed step inhabits the exact target native type
generated by OSLF from the reflective MM2 execution GSLT. -/
theorem speculativeSaveBoundarySpace_inhabits_exact_native_type
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
        (speculativeSaveBoundarySpace context state ledger scanner
          stackTopPosition)
        (reflectiveNativeListExactTargetNativeType .leaveInert
          (cFireReflectiveSourceExecFact
            (speculativeSaveBoundarySpace context state ledger scanner
              stackTopPosition) compressedSaveDirective)).pred := by
  exact
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert
      (speculativeSaveBoundarySpace context state ledger scanner
        stackTopPosition)
      (cFireReflectiveSourceExecFact
        (speculativeSaveBoundarySpace context state ledger scanner
          stackTopPosition) compressedSaveDirective)).2
      (speculativeSaveBoundarySpace_step context state ledger scanner
        stackTopPosition)

/-- The presentation-parametric matcher theorem applies unchanged after the
speculative compiler replaces the terminal carrier.  In particular every
successful save match republishes the transformed terminal, not the removed
base terminal. -/
theorem speculative_save_matcher_runtime_rules_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) {substitution : Subst}
    (rowMember : substitution ∈ saveMatcherRows
      (speculativeSaveBoundarySpace context before ledger scanner
        stackTopPosition)) :
    Subst.lookup substitution
        "compressed-prefix-rule" = some compressedPrefixRule ∧
      Subst.lookup substitution
        "compressed-terminal-rule" = some compressedSpeculativeTerminalRule ∧
      Subst.lookup substitution
        "compressed-proof-rule" = some compressedProofStepRule ∧
      Subst.lookup substitution
        "compressed-invalid-byte-rule" = some compressedInvalidByteRule ∧
      Subst.lookup substitution
        "compressed-question-rule" = some compressedQuestionRule ∧
      Subst.lookup substitution
        "compressed-question-open-fault-rule" =
          some compressedQuestionOpenFaultRule := by
  let staticFrame := speculativeSaveStaticFrame context before stackTopPosition
  let space := speculativeSaveBoundarySpace context before ledger scanner
    stackTopPosition
  have represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space :=
    canonical_represents_running_boundary context before ledger scanner
      staticFrame wellFormed
      (speculativeSaveStaticFrame_clean context before stackTopPosition)
  exact saveMatcherRow_runtime_rules_exact_of_resolved
    speculativeBaseExecutablePresentation represented
    (by simp [staticFrame, speculativeSaveStaticFrame])
    (speculativeSaveStaticFrame_capabilities context before stackTopPosition)
    compressedPrefixRule compressedSpeculativeTerminalRule
    compressedProofStepRule compressedInvalidByteRule compressedQuestionRule
    compressedQuestionOpenFaultRule rfl speculativeBase_resolves_terminal rfl
    rfl rfl rfl rowMember

/-- A real matcher row exists in the complete transformed save boundary.  Its
source stack and node observations come from the occurrence ledger; its six
runtime carriers come from the compiler-selected bundle above. -/
theorem speculative_source_save_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    ExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence)
      (speculativeSaveBoundarySpace context before ledger scannerBefore
        (before.stack.length - 1)) := by
  let staticFrame := speculativeSaveStaticFrame context before
    (before.stack.length - 1)
  let space := speculativeSaveBoundarySpace context before ledger scannerBefore
    (before.stack.length - 1)
  have represented : RepresentsRunningBoundary context before ledger
      scannerBefore staticFrame space :=
    canonical_represents_running_boundary context before ledger scannerBefore
      staticFrame wellFormed
      (speculativeSaveStaticFrame_clean context before
        (before.stack.length - 1))
  have included := source_save_canonical_read_included_for
    speculativeSaveRuntimeRuleBundle ledger represented stackTop nodeLookup
      occurrenceLookup
      (speculativeSaveStaticFrame_supportFor context before
        (before.stack.length - 1))
  exact
    (canonicalSaveMatchSpaceFor_exact_match receipt step
      speculativeSaveRuntimeRuleBundle (before.stack.length - 1)
      (displayedProofOccurrence nodeId node sourceOccurrence)).mono_read included

/-- The actual transformed firing publishes the exact semantic successor
observations witnessed by the source save action. -/
theorem speculative_source_save_fires_exact_rows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    machineRow context after ∈ result ∧
      scannerRow context scannerAfter ∈ result ∧
      heapProofRow context.proofOwner before.heap.length item ∈ result ∧
      saveReceiptRow context.proofOwner before.heap.length item ∈ result := by
  dsimp only
  exact save_fire_adds_source_rows context before after scannerBefore scannerAfter
    (displayedProofOccurrence nodeId node sourceOccurrence)
    (speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1))
    (speculative_source_save_exact_match wellFormed ledger receipt step
      stackTop nodeLookup occurrenceLookup)

/-- The compiler-produced save firing contains the complete canonical dynamic
successor reconstructed from the semantic action and its unchanged occurrence
ledger. -/
theorem speculative_source_save_contains_canonical_successor_rows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    ∀ row, row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ->
      row ∈ result := by
  dsimp only
  let staticFrame := speculativeSaveStaticFrame context before
    (before.stack.length - 1)
  let space := speculativeSaveBoundarySpace context before ledger scannerBefore
    (before.stack.length - 1)
  have represented : RepresentsRunningBoundary context before ledger
      scannerBefore staticFrame space :=
    canonical_represents_running_boundary context before ledger scannerBefore
      staticFrame wellFormed
      (speculativeSaveStaticFrame_clean context before
        (before.stack.length - 1))
  exact save_fire_contains_canonical_successor_rows wellFormed ledger
    proofPosition step stackTop nodeLookup occurrenceLookup represented
      (speculative_source_save_exact_match wellFormed ledger receipt step
        stackTop nodeLookup occurrenceLookup)

/-- Exact source/target dynamic-state boundary for the compiler-produced save
presentation.  The forward direction rules out all noncanonical dynamic
outputs; the reverse direction retains the complete semantic successor. -/
theorem speculative_source_save_dynamic_rows_iff_canonical_successor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (row : Atom) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    row ∈ result ∧ isDynamicRow row = true ↔
      row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter := by
  dsimp only
  let staticFrame := speculativeSaveStaticFrame context before
    (before.stack.length - 1)
  let space := speculativeSaveBoundarySpace context before ledger scannerBefore
    (before.stack.length - 1)
  have represented : RepresentsRunningBoundary context before ledger
      scannerBefore staticFrame space :=
    canonical_represents_running_boundary context before ledger scannerBefore
      staticFrame wellFormed
      (speculativeSaveStaticFrame_clean context before
        (before.stack.length - 1))
  exact save_fire_dynamic_rows_iff_canonical_successor
    speculativeBaseExecutablePresentation speculativeSaveRuntimeRuleAuthority
    ledger proofPosition receipt step stackTop nodeLookup occurrenceLookup
    represented
    (speculativeSaveStaticFrame_frontierAuthority context before
      (before.stack.length - 1))
    (speculativeSaveStaticFrame_capabilities context before
      (before.stack.length - 1))
    (speculative_source_save_exact_match wellFormed ledger receipt step
      stackTop nodeLookup occurrenceLookup) row

/-- The compiler-produced save consumes both obsolete dynamic controls; the
transformed presentation cannot reintroduce either one through another matcher
row. -/
theorem speculative_source_save_consumes_old_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    machineRow context before ∉ result ∧
      scannerRow context scannerBefore ∉ result := by
  dsimp only
  let staticFrame := speculativeSaveStaticFrame context before
    (before.stack.length - 1)
  let space := speculativeSaveBoundarySpace context before ledger scannerBefore
    (before.stack.length - 1)
  have represented : RepresentsRunningBoundary context before ledger
      scannerBefore staticFrame space :=
    canonical_represents_running_boundary context before ledger scannerBefore
      staticFrame wellFormed
      (speculativeSaveStaticFrame_clean context before
        (before.stack.length - 1))
  exact save_fire_consumes_old_controls receipt.phase_before represented
    (speculativeSaveStaticFrame_heapAuthority context before
      (before.stack.length - 1))
    (speculative_source_save_exact_match wellFormed ledger receipt step
      stackTop nodeLookup occurrenceLookup)

/-- One source-derived save is simultaneously a scanner step, the actual
scheduled transformed MM2 step, an inhabitant of the OSLF-generated exact
native target type, and a complete canonical-successor preservation step. -/
theorem speculative_source_save_oslf_successor_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.save] scannerAfter.phase)) ∧
      cReflectiveSourceWorkQueueStep .leaveInert space = some result ∧
      (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies space
        (reflectiveNativeListExactTargetNativeType .leaveInert result).pred ∧
      ∀ row,
        row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ->
          row ∈ result := by
  dsimp only
  refine ⟨receipt.sourceStep, ?_, ?_, ?_⟩
  · exact speculativeSaveBoundarySpace_step context before ledger scannerBefore
      (before.stack.length - 1)
  · exact speculativeSaveBoundarySpace_inhabits_exact_native_type context before
      ledger scannerBefore (before.stack.length - 1)
  · exact speculative_source_save_contains_canonical_successor_rows wellFormed
      ledger proofPosition receipt step stackTop nodeLookup occurrenceLookup

/-- Preservation-and-consumption projection of the transformed save boundary:
one source scanner step, one scheduled MM2 step, the exact OSLF-generated
native target type, complete canonical-successor preservation, and consumption
of both old controls. -/
theorem speculative_source_save_oslf_preserves_and_consumes
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.save] scannerAfter.phase)) ∧
      cReflectiveSourceWorkQueueStep .leaveInert space = some result ∧
      (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies space
        (reflectiveNativeListExactTargetNativeType .leaveInert result).pred ∧
      (∀ row,
        row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ->
          row ∈ result) ∧
      machineRow context before ∉ result ∧
      scannerRow context scannerBefore ∉ result := by
  dsimp only
  have preserved := speculative_source_save_oslf_successor_boundary wellFormed
    ledger proofPosition receipt step stackTop nodeLookup occurrenceLookup
  have consumed := speculative_source_save_consumes_old_controls wellFormed
    ledger receipt step stackTop nodeLookup occurrenceLookup
  exact ⟨preserved.1, preserved.2.1, preserved.2.2.1, preserved.2.2.2,
    consumed.1, consumed.2⟩

/-- Strongest transformed save square: source byte decoding, the actual
scheduled MM2 transition, its exact OSLF-generated native target type, and a
two-sided characterization of every dynamic row in the concrete result. -/
theorem speculative_source_save_oslf_exact_dynamic_successor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let space := speculativeSaveBoundarySpace context before ledger scannerBefore
      (before.stack.length - 1)
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.save] scannerAfter.phase)) ∧
      cReflectiveSourceWorkQueueStep .leaveInert space = some result ∧
      (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies space
        (reflectiveNativeListExactTargetNativeType .leaveInert result).pred ∧
      ∀ row, row ∈ result ∧ isDynamicRow row = true ↔
        row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter := by
  dsimp only
  refine ⟨receipt.sourceStep, ?_, ?_, ?_⟩
  · exact speculativeSaveBoundarySpace_step context before ledger scannerBefore
      (before.stack.length - 1)
  · exact speculativeSaveBoundarySpace_inhabits_exact_native_type context before
      ledger scannerBefore (before.stack.length - 1)
  · exact speculative_source_save_dynamic_rows_iff_canonical_successor
      wellFormed ledger proofPosition receipt step stackTop nodeLookup
        occurrenceLookup

section AxiomAudit

#print axioms executablePresentationOf
#print axioms speculativeBaseExecutableCaptureRows_authorized
#print axioms speculativeTargetStaticCarrierCoverage_eq_true
#print axioms speculative_target_static_rows_authorized
#print axioms speculative_terminal_capture_authorized
#print axioms speculative_direct_proof_capture_authorized
#print axioms source_terminal_capture_rejected_after_transform
#print axioms swapped_direct_handler_kind_rejected
#print axioms speculativeTargetStaticRowsCleanCheck_eq_true
#print axioms speculativeTargetStaticRows_clean
#print axioms speculativeSaveStaticFrame_capabilities
#print axioms speculativeSaveStaticFrame_heapAuthority
#print axioms speculativeSaveRuntimeCaptureCoverage_eq_true
#print axioms speculativeSaveRuntimeCaptureRows_mem_target
#print axioms speculativeSaveStaticFrame_supportFor
#print axioms speculativeSaveRuntimeRuleAuthority
#print axioms speculativeSaveRuntimeRuleBundle_payload_exec_shape
#print axioms speculativeSaveRuntimeRuleBundle_payload_key_ne_save_controls
#print axioms speculativeTargetStaticNoSupportedCheck_eq_true
#print axioms speculativeTargetStaticRows_no_supported
#print axioms canonicalBoundaryRows_all_dynamic
#print axioms canonicalBoundaryRows_no_supported
#print axioms speculativeSaveStaticFrame_supported
#print axioms speculativeSaveBoundarySpace_supported
#print axioms speculativeSaveBoundarySpace_step
#print axioms physical_speculative_save_supported
#print axioms physical_speculative_save_directive_mem
#print axioms physical_speculative_save_live_eq
#print axioms physical_speculative_save_read_perm
#print axioms physical_speculative_save_matcher_mem_iff
#print axioms physicalSaveMatcherRows_subset_saveMatcherRows
#print axioms compressedSaveDirective_sinks_variablesInherited
#print axioms physical_source_save_exact_match
#print axioms physical_exact_save_match_dynamic_additions
#print axioms physical_save_output_witness_dynamic_additions
#print axioms physical_save_output_witness
#print axioms physical_save_matcher_dynamic_rows_exact_of_frame
#print axioms physical_save_matcher_dynamic_rows_exact
#print axioms physical_save_matcher_predecessor_controls_exact_of_frame
#print axioms physical_save_matcher_self_instantiation_exact_of_frame
#print axioms physical_save_preserves_input_row_of_frame
#print axioms physical_save_result_exact_of_frame
#print axioms physical_save_consumes_old_controls_of_frame
#print axioms physical_save_successor_support_present_of_frame
#print axioms physical_save_successor_support_present
#print axioms physical_save_runtime_payload_support_present_of_frame
#print axioms physical_save_added_to_reflective
#print axioms physical_save_added_to_reflective_of_frame
#print axioms compressedSaveDirective_supportSet
#print axioms physical_save_added_dynamic_atom_exact
#print axioms physical_save_added_dynamic_atom_exact_of_frame
#print axioms physical_save_added_nondynamic_mem_frame_of_frame
#print axioms physical_save_dynamic_no_invention
#print axioms physical_save_dynamic_no_invention_of_frame
#print axioms physical_save_result_rows_within_successor_of_frame
#print axioms physical_speculative_save_ruleScoped_step
#print axioms physical_speculative_save_scheduled_segment
#print axioms speculativeSaveBoundarySpace_inhabits_exact_native_type
#print axioms speculative_save_matcher_runtime_rules_exact
#print axioms speculative_source_save_exact_match
#print axioms speculative_source_save_fires_exact_rows
#print axioms speculative_source_save_contains_canonical_successor_rows
#print axioms speculative_source_save_dynamic_rows_iff_canonical_successor
#print axioms speculative_source_save_oslf_successor_boundary
#print axioms speculative_source_save_consumes_old_controls
#print axioms speculative_source_save_oslf_preserves_and_consumes
#print axioms speculative_source_save_oslf_exact_dynamic_successor

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
