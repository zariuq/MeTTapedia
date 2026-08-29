import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Canonical generated frame for an arbitrary speculative proof hit

This module removes target-side scheduling and matcher assumptions from the
symbolic commuting theorem.  The assembled MM2 space is a pure function of
the direct-hit context and the represented proof occurrence; its exact
supported inventory and match are derived from that construction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private def directHeapProofPattern : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "compressed-index", .var "node-id"]

private def directNodePattern : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-id",
      .var "node-formula", .var "node-occurrence"]

private def directStackSuccessorPattern : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
      .var "stack-position", .var "next-stack-position"]

private def directOwnedRulePattern (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

private def directProbeSelfPattern : Atom :=
  .expression
    [.symbol "exec", speculativeDirectProofDirective.loc,
      .var "proof-step-input", .var "proof-step-output"]

private def directProofPatterns : List Atom :=
  [directProbeSelfPattern, directPendingTemplate, directLookupTemplate,
   directHeapProofPattern, directNodePattern, directMachineTemplate,
   directStackSuccessorPattern,
   directOwnedRulePattern "prefix" "compressed-prefix-rule",
   directOwnedRulePattern "terminal" "compressed-terminal-rule",
   directOwnedRulePattern "invalid-byte" "compressed-invalid-byte-rule",
   directOwnedRulePattern "question" "compressed-question-rule",
   directOwnedRulePattern "question-open-fault"
     "compressed-question-open-fault-rule"]

/-- Inspectable input law for the generated direct proof rule. -/
theorem speculative_direct_proof_input_exact :
    speculativeDirectProofDirective.rule.input =
      .compat (mkPattern directProofPatterns) := by
  decide +kernel

/-- Minimal positive matcher interface, parameterized by arbitrary target
data rather than by one closed fixture. -/
def canonicalDirectProofMatchSlice (context : DirectProofContext)
    (item : ProofOccurrence) : List Atom :=
  [speculativeDirectProofDirective.atom,
   context.pendingRow, context.lookupRow,
   heapProofRow context.proofOwner context.index item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   context.machineRow, context.stackSuccessorRow] ++
    directProofContinuationRows

def canonicalDirectProofSliceRows (context : DirectProofContext)
    (item : ProofOccurrence) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (canonicalDirectProofMatchSlice context item)
      speculativeDirectProofDirective.rule.input).map Prod.fst

private def directProbeSelfInput : Atom :=
  match speculativeDirectProofDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-direct-proof-input"

private def directProbeSelfOutput : Atom :=
  match speculativeDirectProofDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-direct-proof-output"

private def directProbeSelfSubst : Subst :=
  [("proof-step-output", directProbeSelfOutput),
   ("proof-step-input", directProbeSelfInput)]

private def directPendingSubst (context : DirectProofContext) : Subst :=
  [("terminal-digit", natAtom (CompressedIndexCode.ofNat context.index).terminalDigit),
   ("reverse-prefix",
      listAtom natAtom (CompressedIndexCode.ofNat context.index).reversePrefixDigits),
   ("remaining-bytes", context.remainingBytes),
   ("word-position", context.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ directProbeSelfSubst

private def directLookupSubst (context : DirectProofContext) : Subst :=
  [("speculative-cursor", (CompressedIndexCode.ofNat context.cursor).atom),
   ("compressed-index", (CompressedIndexCode.ofNat context.index).atom)] ++
    directPendingSubst context

private def directHeapSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("node-id", item.identity)] ++ directLookupSubst context

private def directNodeSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("node-occurrence", item.value.sourceOccurrence),
   ("node-formula", item.value.formula)] ++ directHeapSubst context item

private def directMachineSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("stack-position", (CompressedIndexCode.ofNat context.stackPosition).atom),
   ("node-next", (CompressedIndexCode.ofNat context.nodeNext).atom),
   ("heap-next", (CompressedIndexCode.ofNat context.heapNext).atom)] ++
    directNodeSubst context item

private def directSuccessorSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("next-stack-position",
      (CompressedIndexCode.ofNat context.nextStackPosition).atom)] ++
    directMachineSubst context item

private def directPrefixSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("compressed-prefix-rule", compressedPrefixRule)] ++
    directSuccessorSubst context item

private def directTerminalSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("compressed-terminal-rule",
      MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule)] ++
    directPrefixSubst context item

private def directInvalidByteSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("compressed-invalid-byte-rule", compressedInvalidByteRule)] ++
    directTerminalSubst context item

private def directQuestionSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("compressed-question-rule", compressedQuestionRule)] ++
    directInvalidByteSubst context item

private def directQuestionOpenFaultSubst (context : DirectProofContext)
    (item : ProofOccurrence) : Subst :=
  [("compressed-question-open-fault-rule", compressedQuestionOpenFaultRule)] ++
    directQuestionSubst context item

private theorem directProbeSelf_match :
    Conformance.Computable.cmatchAtom [] directProbeSelfPattern
      speculativeDirectProofDirective.atom = some directProbeSelfSubst := by
  decide +kernel

private theorem directPending_match (context : DirectProofContext) :
    Conformance.Computable.cmatchAtom directProbeSelfSubst
      directPendingTemplate context.pendingRow = some (directPendingSubst context) := by
  cases context
  simp [directProbeSelfSubst, directPendingSubst,
    DirectProofContext.pendingRow, directPendingTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup,
    CompressedIndexCode.atom, compressedIndexCodeAtom]

private theorem directLookup_match (context : DirectProofContext) :
    Conformance.Computable.cmatchAtom (directPendingSubst context)
      directLookupTemplate context.lookupRow = some (directLookupSubst context) := by
  cases context
  simp [directLookupSubst, directPendingSubst, directProbeSelfSubst,
    DirectProofContext.lookupRow, directLookupTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directHeap_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directLookupSubst context)
      directHeapProofPattern
      (heapProofRow context.proofOwner context.index item) =
        some (directHeapSubst context item) := by
  cases context
  cases item
  simp [directHeapSubst, directLookupSubst, directPendingSubst,
    directProbeSelfSubst, directHeapProofPattern, heapProofRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directNode_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directHeapSubst context item)
      directNodePattern
      (MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item) =
        some (directNodeSubst context item) := by
  cases context
  cases item with
  | mk identity value =>
      cases value
      simp [directNodeSubst, directHeapSubst, directLookupSubst,
        directPendingSubst, directProbeSelfSubst, directNodePattern,
        MM2CompressedProofHeapEncoding.nodeRow,
        Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directMachine_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directNodeSubst context item)
      directMachineTemplate context.machineRow =
        some (directMachineSubst context item) := by
  cases context
  cases item with
  | mk identity value =>
      cases value
      simp [directMachineSubst, directNodeSubst, directHeapSubst,
        directLookupSubst, directPendingSubst, directProbeSelfSubst,
        directMachineTemplate, DirectProofContext.machineRow,
        Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directSuccessor_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directMachineSubst context item)
      directStackSuccessorPattern context.stackSuccessorRow =
        some (directSuccessorSubst context item) := by
  cases context
  cases item with
  | mk identity value =>
      cases value
      simp [directSuccessorSubst, directMachineSubst, directNodeSubst,
        directHeapSubst, directLookupSubst, directPendingSubst,
        directProbeSelfSubst, directStackSuccessorPattern,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow,
        compressedStackOwner, Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directPrefix_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directSuccessorSubst context item)
      (directOwnedRulePattern "prefix" "compressed-prefix-rule")
      (compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule) =
        some (directPrefixSubst context item) := by
  simp [directPrefixSubst, directSuccessorSubst, directOwnedRulePattern,
    directMachineSubst, directNodeSubst, directHeapSubst, directLookupSubst,
    directPendingSubst, directProbeSelfSubst, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directTerminal_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directPrefixSubst context item)
      (directOwnedRulePattern "terminal" "compressed-terminal-rule")
      (compressedOwnedRuntimeRuleRow "terminal"
        MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule) =
          some (directTerminalSubst context item) := by
  simp [directTerminalSubst, directPrefixSubst, directSuccessorSubst,
    directMachineSubst, directNodeSubst, directHeapSubst, directLookupSubst,
    directPendingSubst, directProbeSelfSubst, directOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directInvalidByte_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directTerminalSubst context item)
      (directOwnedRulePattern "invalid-byte" "compressed-invalid-byte-rule")
      (compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule) =
        some (directInvalidByteSubst context item) := by
  simp [directInvalidByteSubst, directTerminalSubst, directPrefixSubst,
    directSuccessorSubst, directMachineSubst, directNodeSubst,
    directHeapSubst, directLookupSubst, directPendingSubst,
    directProbeSelfSubst, directOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directQuestion_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directInvalidByteSubst context item)
      (directOwnedRulePattern "question" "compressed-question-rule")
      (compressedOwnedRuntimeRuleRow "question" compressedQuestionRule) =
        some (directQuestionSubst context item) := by
  simp [directQuestionSubst, directInvalidByteSubst, directTerminalSubst,
    directPrefixSubst, directSuccessorSubst, directMachineSubst,
    directNodeSubst, directHeapSubst, directLookupSubst, directPendingSubst,
    directProbeSelfSubst, directOwnedRulePattern,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem directQuestionOpenFault_match (context : DirectProofContext)
    (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom (directQuestionSubst context item)
      (directOwnedRulePattern "question-open-fault"
        "compressed-question-open-fault-rule")
      (compressedOwnedRuntimeRuleRow "question-open-fault"
        compressedQuestionOpenFaultRule) =
          some (directQuestionOpenFaultSubst context item) := by
  simp [directQuestionOpenFaultSubst, directQuestionSubst,
    directInvalidByteSubst, directTerminalSubst, directPrefixSubst,
    directSuccessorSubst, directMachineSubst, directNodeSubst,
    directHeapSubst, directLookupSubst, directPendingSubst,
    directProbeSelfSubst, directOwnedRulePattern, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem cmatchPattern_go_cons_of_selected
    {space : List Atom} {pattern : Atom} {patterns : List Atom}
    {substitutionIn substitutionMid substitutionOut : Subst}
    {consumedIn consumedOut : List Atom} {concrete : Atom}
    (present : concrete ∈ space)
    (matched : Conformance.Computable.cmatchAtom substitutionIn pattern concrete =
      some substitutionMid)
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

private def canonicalDirectProofConsumed (context : DirectProofContext)
    (item : ProofOccurrence) : List Atom :=
  [compressedOwnedRuntimeRuleRow "question-open-fault"
      compressedQuestionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "terminal"
      MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule,
   compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   context.stackSuccessorRow, context.machineRow,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   heapProofRow context.proofOwner context.index item,
   context.lookupRow, context.pendingRow,
   speculativeDirectProofDirective.atom]

private theorem canonical_final_subst_in_slice
    (context : DirectProofContext) (item : ProofOccurrence) :
    directQuestionOpenFaultSubst context item ∈
      canonicalDirectProofSliceRows context item := by
  unfold canonicalDirectProofSliceRows
  rw [speculative_direct_proof_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(directQuestionOpenFaultSubst context item,
    canonicalDirectProofConsumed context item), ?_, rfl⟩
  unfold directProofPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := speculativeDirectProofDirective.atom)
  · simp [canonicalDirectProofMatchSlice]
  · exact directProbeSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.pendingRow)
  · simp [canonicalDirectProofMatchSlice]
  · exact directPending_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.lookupRow)
  · simp [canonicalDirectProofMatchSlice]
  · exact directLookup_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := heapProofRow context.proofOwner context.index item)
  · simp [canonicalDirectProofMatchSlice]
  · exact directHeap_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item)
  · simp [canonicalDirectProofMatchSlice]
  · exact directNode_match context item
  apply cmatchPattern_go_cons_of_selected (concrete := context.machineRow)
  · simp [canonicalDirectProofMatchSlice]
  · exact directMachine_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.stackSuccessorRow)
  · simp [canonicalDirectProofMatchSlice]
  · exact directSuccessor_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule)
  · simp [canonicalDirectProofMatchSlice, directProofContinuationRows]
  · exact directPrefix_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "terminal"
      MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule)
  · simp [canonicalDirectProofMatchSlice, directProofContinuationRows]
  · exact directTerminal_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "invalid-byte"
      compressedInvalidByteRule)
  · simp [canonicalDirectProofMatchSlice, directProofContinuationRows]
  · exact directInvalidByte_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question" compressedQuestionRule)
  · simp [canonicalDirectProofMatchSlice, directProofContinuationRows]
  · exact directQuestion_match context item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question-open-fault"
      compressedQuestionOpenFaultRule)
  · simp [canonicalDirectProofMatchSlice, directProofContinuationRows]
  · exact directQuestionOpenFault_match context item
  simp [Conformance.Computable.cmatchPattern.go,
    canonicalDirectProofConsumed]

private theorem canonical_final_subst_instantiates_frame
    (context : DirectProofContext) (item : ProofOccurrence) :
    instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directPendingTemplate = some context.pendingRow ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directLookupTemplate = some context.lookupRow ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directMachineTemplate = some context.machineRow ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directNextMachineTemplate = some context.nextMachineRow ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directStackCellTemplate =
        some (compressedStackRow context.proofOwner context.stackPosition item) ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directNormalStackCellTemplate =
        some (normalStackRow context.proofOwner context.stackPosition item) ∧
      instantiateTemplateAtom? (directQuestionOpenFaultSubst context item)
          directResumedScanTemplate = some context.resumedScanRow := by
  cases context
  cases item with
  | mk identity value =>
      cases value
      simp [directQuestionOpenFaultSubst, directQuestionSubst,
        directInvalidByteSubst, directTerminalSubst, directPrefixSubst,
        directSuccessorSubst, directMachineSubst, directNodeSubst,
        directHeapSubst, directLookupSubst, directPendingSubst,
        directProbeSelfSubst, instantiateTemplateAtom?, templateCovered,
        templatesCovered, applySubst, applySubst.applySubstList, Subst.lookup,
        directPendingTemplate, directLookupTemplate, directMachineTemplate,
        directNextMachineTemplate, directStackCellTemplate,
        directNormalStackCellTemplate, directResumedScanTemplate,
        DirectProofContext.pendingRow, DirectProofContext.lookupRow,
        DirectProofContext.machineRow, DirectProofContext.nextMachineRow,
        DirectProofContext.resumedScanRow, compressedStackRow, normalStackRow,
        CompressedIndexCode.atom, compressedIndexCodeAtom, listAtom, natAtom]

theorem canonical_slice_instantiates_frame
    (context : DirectProofContext) (item : ProofOccurrence) :
    ∃ substitution ∈ canonicalDirectProofSliceRows context item,
      instantiateTemplateAtom? substitution directPendingTemplate =
          some context.pendingRow ∧
        instantiateTemplateAtom? substitution directLookupTemplate =
          some context.lookupRow ∧
        instantiateTemplateAtom? substitution directMachineTemplate =
          some context.machineRow ∧
        instantiateTemplateAtom? substitution directNextMachineTemplate =
          some context.nextMachineRow ∧
        instantiateTemplateAtom? substitution directStackCellTemplate =
          some (compressedStackRow context.proofOwner context.stackPosition item) ∧
        instantiateTemplateAtom? substitution directNormalStackCellTemplate =
          some (normalStackRow context.proofOwner context.stackPosition item) ∧
        instantiateTemplateAtom? substitution directResumedScanTemplate =
          some context.resumedScanRow := by
  refine ⟨directQuestionOpenFaultSubst context item,
    canonical_final_subst_in_slice context item, ?_⟩
  exact canonical_final_subst_instantiates_frame context item

/-- The smallest assembled generated space on which all direct proof-hit
premises are internal facts rather than external side evidence. -/
def canonicalDirectProofSpace (context : DirectProofContext)
    (item : ProofOccurrence) : List Atom :=
  [compressedProofStepDirective.atom,
   compressedAssertionLaunchDirective.atom,
   compressedHeapLookupFaultDirective.atom,
   compressedHeapLookupAdvanceDirective.atom,
   speculativeDirectProofDirective.atom,
   speculativeDirectAssertionDirective.atom,
   context.pendingRow, context.lookupRow,
   heapProofRow context.proofOwner context.index item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
    context.machineRow, context.stackSuccessorRow] ++
    directProofContinuationRows

/-- The canonical assembled space retains the complete proof occurrence.
Changing only its source occurrence therefore changes the concrete target
program rather than collapsing two proof histories with equal formulas. -/
theorem canonicalDirectProofSpace_injective (context : DirectProofContext) :
    Function.Injective (canonicalDirectProofSpace context) := by
  intro left right spaceEqual
  have nodeEqual :
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner left =
        MM2CompressedProofHeapEncoding.nodeRow context.proofOwner right := by
    have atNode := congrArg (fun rows : List Atom => rows[9]?) spaceEqual
    simpa [canonicalDirectProofSpace] using atNode
  exact MM2CompressedProofHeapEncoding.nodeRow_injective
    context.proofOwner nodeEqual

/-- Negative control for proof-history collapse: equal identity and formula
do not erase distinct derivation occurrences at the canonical MM2 boundary. -/
theorem canonicalDirectProofSpace_changed_sourceOccurrence
    (context : DirectProofContext) (identity formula : Atom)
    (leftOccurrence rightOccurrence : Atom)
    (different : leftOccurrence ≠ rightOccurrence) :
    canonicalDirectProofSpace context
        ⟨identity, ⟨formula, leftOccurrence⟩⟩ ≠
      canonicalDirectProofSpace context
        ⟨identity, ⟨formula, rightOccurrence⟩⟩ := by
  intro spaceEqual
  have itemEqual := canonicalDirectProofSpace_injective context spaceEqual
  exact different (congrArg (fun item => item.value.sourceOccurrence) itemEqual)

theorem canonical_direct_proof_supported_exact
    (context : DirectProofContext) (item : ProofOccurrence) :
    cSupportedSourceExecFacts (canonicalDirectProofSpace context item) =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectProofDirective, speculativeDirectAssertionDirective] := by
  rfl

@[simp] theorem canonical_direct_proof_live_exact
    (context : DirectProofContext) (item : ProofOccurrence) :
    directProofLive (canonicalDirectProofSpace context item) =
      [compressedProofStepDirective.atom,
       compressedAssertionLaunchDirective.atom,
       compressedHeapLookupFaultDirective.atom,
       compressedHeapLookupAdvanceDirective.atom,
       speculativeDirectAssertionDirective.atom,
       context.pendingRow, context.lookupRow,
       heapProofRow context.proofOwner context.index item,
       MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
       context.machineRow, context.stackSuccessorRow] ++
        directProofContinuationRows := by
  rfl

theorem canonical_heap_row_in_live
    (context : DirectProofContext) (item : ProofOccurrence) :
    heapProofRow context.proofOwner context.index item ∈
      directProofLive (canonicalDirectProofSpace context item) := by
  rw [canonical_direct_proof_live_exact]
  simp

theorem canonical_node_row_in_live
    (context : DirectProofContext) (item : ProofOccurrence) :
    MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
      directProofLive (canonicalDirectProofSpace context item) := by
  rw [canonical_direct_proof_live_exact]
  simp

private theorem canonical_slice_in_full_read
    (context : DirectProofContext) (item : ProofOccurrence) :
    ∀ atom ∈ canonicalDirectProofMatchSlice context item,
      atom ∈ speculativeDirectProofDirective.atom ::
        directProofLive (canonicalDirectProofSpace context item) := by
  intro atom member
  rw [canonical_direct_proof_live_exact]
  simp only [canonicalDirectProofMatchSlice, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member ⊢
  aesop

private theorem canonical_slice_row_in_full
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (sliceRow : substitution ∈ canonicalDirectProofSliceRows context item) :
    substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item) := by
  unfold canonicalDirectProofSliceRows at sliceRow
  unfold directProofMatcherRows
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨sliceSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(sliceSubstitution, consumed), ?_, rfl⟩
  rw [speculative_direct_proof_input_exact] at matched ⊢
  exact Conformance.Computable.cmatchPattern_mono []
    (canonicalDirectProofMatchSlice context item)
    (speculativeDirectProofDirective.atom ::
      directProofLive (canonicalDirectProofSpace context item))
    (mkPattern directProofPatterns)
    (canonical_slice_in_full_read context item)
    sliceSubstitution consumed matched

theorem canonical_exact_direct_proof_match
    (context : DirectProofContext) (item : ProofOccurrence) :
    ExactDirectProofMatch context item
      (canonicalDirectProofSpace context item) := by
  rcases canonical_slice_instantiates_frame context item with
    ⟨substitution, sliceRow, pending, lookup, machine, nextMachine,
      compactStack, normalStack, resumed⟩
  exact ⟨substitution, canonical_slice_row_in_full context item sliceRow,
    pending, lookup, machine, nextMachine, compactStack, normalStack, resumed⟩

theorem canonical_direct_proof_request_frame
    {Other : Type} (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other)
    (control : before.control =
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request context.index)
    (found : before.heap[context.index]? = some (.occurrence item)) :
    DirectProofRequestFrame context item before
      (canonicalDirectProofSpace context item) where
  control := control
  found := found
  heapRow := canonical_heap_row_in_live context item
  nodeRow := canonical_node_row_in_live context item
  supported := canonical_direct_proof_supported_exact context item
  exactMatch := canonical_exact_direct_proof_match context item

/-- Arbitrary semantic proof hits commute with the generated canonical MM2
handler.  Only the source-owned request and heap lookup remain as premises. -/
theorem canonical_direct_proof_hit_commutes
    {Other : Type} (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other)
    (control : before.control =
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request context.index)
    (found : before.heap[context.index]? = some (.occurrence item)) :
    DirectProofHitCommutingSquare context item before
      (canonicalDirectProofSpace context item) :=
  direct_proof_hit_commutes_of_exact_frame context item before
    (canonicalDirectProofSpace context item)
    (canonical_direct_proof_request_frame context item before control found)

#print axioms canonical_direct_proof_supported_exact
#print axioms canonicalDirectProofSpace_injective
#print axioms canonicalDirectProofSpace_changed_sourceOccurrence
#print axioms canonical_heap_row_in_live
#print axioms canonical_node_row_in_live
#print axioms canonical_exact_direct_proof_match
#print axioms canonical_direct_proof_request_frame
#print axioms canonical_direct_proof_hit_commutes

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
