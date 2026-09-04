import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

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

def directHeapProofPattern : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "compressed-index", .var "node-id"]

def directNodePattern : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-id",
      .var "node-formula", .var "node-occurrence"]

def directStackSuccessorPattern : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
      .var "stack-position", .var "next-stack-position"]

def directOwnedRulePattern (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

def directProbeSelfPattern : Atom :=
  .expression
    [.symbol "exec", speculativeDirectProofDirective.loc,
      .var "proof-step-input", .var "proof-step-output"]

def directProofPatterns : List Atom :=
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

def directProbeSelfInput : Atom :=
  match speculativeDirectProofDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-direct-proof-input"

def directProbeSelfOutput : Atom :=
  match speculativeDirectProofDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-direct-proof-output"

/-- Authored continuation installed after a speculative direct proof hit.
The handler body is source-derived from the selected direct rule, while its
location returns to the ordinary proof-step scheduler slot. -/
def directProofReplayRule : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "08", .symbol "mm-compressed-proof-step"],
      directProbeSelfInput, directProbeSelfOutput]

theorem speculativeDirectProofDirective_atom_exact :
    speculativeDirectProofDirective.atom =
      .expression
        [.symbol "exec", speculativeDirectProofDirective.loc,
          directProbeSelfInput, directProbeSelfOutput] := by
  decide +kernel

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

private theorem supported_directive_atom_exec_shape
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    ∃ location input output,
      directive.atom =
        .expression [.symbol "exec", location, input, output] := by
  have atomEq := extractSupportedSourceExecFact_atom decoded
  unfold extractSupportedSourceExecFact at decoded
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at decoded
  | some raw =>
      have atomShape : ∃ location input output,
          atom = .expression [.symbol "exec", location, input, output] := by
        unfold extractRawExecFact at rawEq
        split at rawEq
        next location input output =>
          exact ⟨location, input, output, rfl⟩
        next => contradiction
      obtain ⟨location, input, output, rfl⟩ := atomShape
      exact ⟨location, input, output, atomEq⟩

private theorem cmatchAtom_fixed_head_supported_directive_ne
    (before : Subst) (head : String) (tail : List Atom)
    {atom : Atom} {directive : SourceExecFact}
    (distinct : head ≠ "exec")
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    Conformance.Computable.cmatchAtom before
        (.expression (.symbol head :: tail)) directive.atom = none := by
  obtain ⟨location, input, output, shape⟩ :=
    supported_directive_atom_exec_shape decoded
  rw [shape]
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "exec" tail [location, input, output] distinct

private theorem directPending_ne_speculativeDirectProof (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      speculativeDirectProofDirective.atom = none := by
  unfold directPendingTemplate
  exact cmatchAtom_fixed_head_supported_directive_ne
    (atom := MM2CompressedProofSpeculativeHeapLookup.compressedDirectProofRule)
    (directive := speculativeDirectProofDirective) before
    "mm-compressed-step-pending" _ (by decide)
    extract_speculativeDirectProofDirective_exact

private theorem directPending_ne_compressedProofStep (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      compressedProofStepDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol "mm-compressed-step-pending" :: _))
    compressedProofStepRule = none
  unfold compressedProofStepRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before "mm-compressed-step-pending" "exec" _ _ (by decide)

private theorem directPending_ne_compressedAssertionLaunch (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      compressedAssertionLaunchDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol "mm-compressed-step-pending" :: _))
    compressedAssertionLaunchRule = none
  unfold compressedAssertionLaunchRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before "mm-compressed-step-pending" "exec" _ _ (by decide)

private theorem directPending_ne_compressedHeapLookupFault (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      compressedHeapLookupFaultDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol "mm-compressed-step-pending" :: _))
    compressedHeapLookupFaultRule = none
  unfold compressedHeapLookupFaultRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before "mm-compressed-step-pending" "exec" _ _ (by decide)

private theorem directPending_ne_compressedHeapLookupAdvance (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      compressedHeapLookupAdvanceDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol "mm-compressed-step-pending" :: _))
    compressedHeapLookupAdvanceRule = none
  unfold compressedHeapLookupAdvanceRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before "mm-compressed-step-pending" "exec" _ _ (by decide)

private theorem directPending_ne_speculativeDirectAssertion (before : Subst) :
    Conformance.Computable.cmatchAtom before directPendingTemplate
      speculativeDirectAssertionDirective.atom = none := by
  unfold directPendingTemplate
  exact cmatchAtom_fixed_head_supported_directive_ne
    (atom := MM2CompressedProofSpeculativeHeapLookup.compressedDirectAssertionRule)
    (directive := speculativeDirectAssertionDirective) before
    "mm-compressed-step-pending" _ (by decide)
    extract_speculativeDirectAssertionDirective_exact

private theorem fixedHead_ne_speculativeDirectProof
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      speculativeDirectProofDirective.atom = none :=
  cmatchAtom_fixed_head_supported_directive_ne
    (atom := MM2CompressedProofSpeculativeHeapLookup.compressedDirectProofRule)
    (directive := speculativeDirectProofDirective) before head tail distinct
    extract_speculativeDirectProofDirective_exact

private theorem fixedHead_ne_compressedProofStep
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      compressedProofStepDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol head :: tail)) compressedProofStepRule = none
  unfold compressedProofStepRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "exec" tail _ distinct

private theorem fixedHead_ne_compressedAssertionLaunch
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      compressedAssertionLaunchDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol head :: tail)) compressedAssertionLaunchRule = none
  unfold compressedAssertionLaunchRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "exec" tail _ distinct

private theorem fixedHead_ne_compressedHeapLookupFault
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      compressedHeapLookupFaultDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol head :: tail)) compressedHeapLookupFaultRule = none
  unfold compressedHeapLookupFaultRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "exec" tail _ distinct

private theorem fixedHead_ne_compressedHeapLookupAdvance
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      compressedHeapLookupAdvanceDirective.atom = none := by
  change Conformance.Computable.cmatchAtom before
    (.expression (.symbol head :: tail)) compressedHeapLookupAdvanceRule = none
  unfold compressedHeapLookupAdvanceRule
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "exec" tail _ distinct

private theorem fixedHead_ne_speculativeDirectAssertion
    (before : Subst) (head : String) (tail : List Atom)
    (distinct : head ≠ "exec") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      speculativeDirectAssertionDirective.atom = none :=
  cmatchAtom_fixed_head_supported_directive_ne
    (atom := MM2CompressedProofSpeculativeHeapLookup.compressedDirectAssertionRule)
    (directive := speculativeDirectAssertionDirective) before head tail distinct
    extract_speculativeDirectAssertionDirective_exact

private theorem fixedHead_ne_ownedRuntimeRule
    (before : Subst) (head : String) (tail : List Atom)
    (kind : String) (rule : Atom)
    (distinct : head ≠ "mm-compressed-owned-runtime-rule") :
    Conformance.Computable.cmatchAtom before
      (.expression (.symbol head :: tail))
      (compressedOwnedRuntimeRuleRow kind rule) = none := by
  unfold compressedOwnedRuntimeRuleRow
  exact Conformance.Computable.cmatchAtom_expression_symbol_head_ne
    before head "mm-compressed-owned-runtime-rule" tail _ distinct

private def canonicalDirectDynamicRows (context : DirectProofContext)
    (item : ProofOccurrence) : List Atom :=
  [context.pendingRow, context.lookupRow,
   heapProofRow context.proofOwner context.index item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   context.machineRow, context.stackSuccessorRow]

private theorem canonical_matcher_factor_origin
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst} (factor : Atom)
    (factorMember : factor ∈ directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ speculativeDirectProofDirective.atom ::
          directProofLive (canonicalDirectProofSpace context item) ∧
        Conformance.Computable.cmatchAtom beforeFactor factor carrier =
          some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution factor = carrier := by
  unfold directProofMatcherRows at matcherMember
  rw [speculative_direct_proof_input_exact] at matcherMember
  exact
    Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
      (speculativeDirectProofDirective.atom ::
        directProofLive (canonicalDirectProofSpace context item))
      (mkPattern directProofPatterns) factor
      (by simpa [mkPattern] using factorMember) matcherMember

private theorem canonical_matcher_factor_covered
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst} (factor : Atom)
    (factorMember : factor ∈ directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    templateCovered substitution factor = true := by
  obtain ⟨beforeFactor, afterFactor, carrier, _carrierMember, matched,
      extension, _replay⟩ :=
    canonical_matcher_factor_origin context item factor factorMember matcherMember
  exact Conformance.Computable.templateCovered_of_lookupExtends extension factor
    (Conformance.Computable.cmatchAtom_templateCovered beforeFactor factor
      carrier afterFactor matched)

private theorem canonical_matcher_dynamic_factor_origin
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst} (head : String) (tail : List Atom)
    (notExec : head ≠ "exec")
    (notOwnedRuntime : head ≠ "mm-compressed-owned-runtime-rule")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    ∃ carrier ∈ canonicalDirectDynamicRows context item,
      applySubst substitution (.expression (.symbol head :: tail)) = carrier := by
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched,
      _extends, replay⟩ :=
    canonical_matcher_factor_origin context item
      (.expression (.symbol head :: tail)) factorMember matcherMember
  rw [canonical_direct_proof_live_exact] at carrierMember
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at carrierMember
  rcases carrierMember with rfl | fixed | continuation
  · rw [fixedHead_ne_speculativeDirectProof beforeFactor head tail notExec]
      at matched
    cases matched
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · rw [fixedHead_ne_compressedProofStep beforeFactor head tail notExec]
        at matched
      cases matched
    · rw [fixedHead_ne_compressedAssertionLaunch beforeFactor head tail notExec]
        at matched
      cases matched
    · rw [fixedHead_ne_compressedHeapLookupFault beforeFactor head tail notExec]
        at matched
      cases matched
    · rw [fixedHead_ne_compressedHeapLookupAdvance beforeFactor head tail notExec]
        at matched
      cases matched
    · rw [fixedHead_ne_speculativeDirectAssertion beforeFactor head tail notExec]
        at matched
      cases matched
    · exact ⟨context.pendingRow, by simp [canonicalDirectDynamicRows], replay⟩
    · exact ⟨context.lookupRow, by simp [canonicalDirectDynamicRows], replay⟩
    · exact ⟨heapProofRow context.proofOwner context.index item,
        by simp [canonicalDirectDynamicRows], replay⟩
    · exact ⟨MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
        by simp [canonicalDirectDynamicRows], replay⟩
    · exact ⟨context.machineRow, by simp [canonicalDirectDynamicRows], replay⟩
    · exact ⟨context.stackSuccessorRow,
        by simp [canonicalDirectDynamicRows], replay⟩
  · simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at continuation
    rcases continuation with rfl | rfl | rfl | rfl | rfl <;>
      rw [fixedHead_ne_ownedRuntimeRule beforeFactor head tail _ _
        notOwnedRuntime] at matched <;>
      cases matched

private theorem applySubst_expression_symbol_head_ne
    (substitution : Subst) (authoredHead candidateHead : String)
    (authoredTail candidateTail : List Atom)
    (distinct : authoredHead ≠ candidateHead) :
    applySubst substitution
        (.expression (.symbol authoredHead :: authoredTail)) ≠
      .expression (.symbol candidateHead :: candidateTail) := by
  simp [applySubst, applySubst.applySubstList, distinct]

/-- Every complete direct matcher obtains the pending request from the
source-derived request row, not from an unrelated row in the execution
frame. -/
theorem canonical_direct_pending_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directPendingTemplate = context.pendingRow := by
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched,
      _extends, replay⟩ :=
    canonical_matcher_factor_origin context item directPendingTemplate
      (by simp [directProofPatterns]) matcherMember
  rw [canonical_direct_proof_live_exact] at carrierMember
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at carrierMember
  rcases carrierMember with rfl | fixed | continuation
  · rw [directPending_ne_speculativeDirectProof beforeFactor] at matched
    cases matched
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · rw [directPending_ne_compressedProofStep beforeFactor] at matched
      cases matched
    · rw [directPending_ne_compressedAssertionLaunch beforeFactor] at matched
      cases matched
    · rw [directPending_ne_compressedHeapLookupFault beforeFactor] at matched
      cases matched
    · rw [directPending_ne_compressedHeapLookupAdvance beforeFactor] at matched
      cases matched
    · rw [directPending_ne_speculativeDirectAssertion beforeFactor] at matched
      cases matched
    · exact replay
    · unfold directPendingTemplate DirectProofContext.lookupRow at matched
      rw [Conformance.Computable.cmatchAtom_expression_symbol_head_ne
        beforeFactor "mm-compressed-step-pending" "mm-compressed-heap-lookup"
        _ _ (by decide)] at matched
      cases matched
    · unfold directPendingTemplate heapProofRow at matched
      rw [Conformance.Computable.cmatchAtom_expression_symbol_head_ne
        beforeFactor "mm-compressed-step-pending" "mm-compressed-heap-proof"
        _ _ (by decide)] at matched
      cases matched
    · unfold directPendingTemplate MM2CompressedProofHeapEncoding.nodeRow at matched
      rw [Conformance.Computable.cmatchAtom_expression_symbol_head_ne
        beforeFactor "mm-compressed-step-pending" "mm-compressed-node"
        _ _ (by decide)] at matched
      cases matched
    · simp [directPendingTemplate, DirectProofContext.machineRow,
        Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList] at matched
    · simp [directPendingTemplate, DirectProofContext.stackSuccessorRow,
        compressedIndexSuccessorRow, Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList] at matched
  · simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at continuation
    rcases continuation with rfl | rfl | rfl | rfl | rfl <;>
      simp [directPendingTemplate, compressedOwnedRuntimeRuleRow,
        Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList] at matched

/-- Every complete direct matcher obtains the lookup request from the exact
source-derived lookup row. -/
theorem canonical_direct_lookup_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directLookupTemplate = context.lookupRow := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    canonical_matcher_dynamic_factor_origin context item
      "mm-compressed-heap-lookup"
      [.var "scope-owner", .var "proof-owner", .var "word-position",
       .var "remaining-bytes", .var "compressed-index",
       .var "speculative-cursor"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directLookupTemplate]) matcherMember
  simp only [canonicalDirectDynamicRows, List.mem_cons, List.not_mem_nil,
    or_false] at carrierMember
  rcases carrierMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-lookup" "mm-compressed-step-pending" _ _
      (by decide) (by simpa [directLookupTemplate,
        DirectProofContext.pendingRow] using replay)
  · exact replay
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-lookup" "mm-compressed-heap-proof" _ _
      (by decide) (by simpa [directLookupTemplate, heapProofRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-lookup" "mm-compressed-node" _ _
      (by decide) (by simpa [directLookupTemplate,
        MM2CompressedProofHeapEncoding.nodeRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-lookup" "mm-compressed-machine" _ _
      (by decide) (by simpa [directLookupTemplate,
        DirectProofContext.machineRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-lookup" "mm-compressed-index-successor" _ _
      (by decide) (by simpa [directLookupTemplate,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
        using replay)

/-- Every complete direct matcher obtains the proof heap cell from the exact
source-derived heap row. -/
theorem canonical_direct_heap_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directHeapProofPattern =
      heapProofRow context.proofOwner context.index item := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    canonical_matcher_dynamic_factor_origin context item
      "mm-compressed-heap-proof"
      [.var "proof-owner", .var "compressed-index", .var "node-id"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directHeapProofPattern]) matcherMember
  simp only [canonicalDirectDynamicRows, List.mem_cons, List.not_mem_nil,
    or_false] at carrierMember
  rcases carrierMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-step-pending" _ _
      (by decide) (by simpa [directHeapProofPattern,
        DirectProofContext.pendingRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-heap-lookup" _ _
      (by decide) (by simpa [directHeapProofPattern,
        DirectProofContext.lookupRow] using replay)
  · exact replay
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-node" _ _
      (by decide) (by simpa [directHeapProofPattern,
        MM2CompressedProofHeapEncoding.nodeRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-machine" _ _
      (by decide) (by simpa [directHeapProofPattern,
        DirectProofContext.machineRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-index-successor" _ _
      (by decide) (by simpa [directHeapProofPattern,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
        using replay)

/-- Every complete direct matcher obtains the proof node, including its
source occurrence, from the exact source-derived node row. -/
theorem canonical_direct_node_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directNodePattern =
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    canonical_matcher_dynamic_factor_origin context item
      "mm-compressed-node"
      [.var "proof-owner", .var "node-id", .var "node-formula",
       .var "node-occurrence"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directNodePattern]) matcherMember
  simp only [canonicalDirectDynamicRows, List.mem_cons, List.not_mem_nil,
    or_false] at carrierMember
  rcases carrierMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-step-pending" _ _
      (by decide) (by simpa [directNodePattern,
        DirectProofContext.pendingRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-heap-lookup" _ _
      (by decide) (by simpa [directNodePattern,
        DirectProofContext.lookupRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-heap-proof" _ _
      (by decide) (by simpa [directNodePattern, heapProofRow] using replay)
  · exact replay
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-machine" _ _
      (by decide) (by simpa [directNodePattern,
        DirectProofContext.machineRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-index-successor" _ _
      (by decide) (by simpa [directNodePattern,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
        using replay)

/-- Every complete direct matcher obtains the machine frontiers from the
exact source-derived machine row. -/
theorem canonical_direct_machine_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directMachineTemplate = context.machineRow := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    canonical_matcher_dynamic_factor_origin context item
      "mm-compressed-machine"
      [.var "scope-owner", .var "proof-owner", .var "heap-next",
       .var "node-next", .var "stack-position"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directMachineTemplate]) matcherMember
  simp only [canonicalDirectDynamicRows, List.mem_cons, List.not_mem_nil,
    or_false] at carrierMember
  rcases carrierMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-machine" "mm-compressed-step-pending" _ _
      (by decide) (by simpa [directMachineTemplate,
        DirectProofContext.pendingRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-machine" "mm-compressed-heap-lookup" _ _
      (by decide) (by simpa [directMachineTemplate,
        DirectProofContext.lookupRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-machine" "mm-compressed-heap-proof" _ _
      (by decide) (by simpa [directMachineTemplate, heapProofRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-machine" "mm-compressed-node" _ _
      (by decide) (by simpa [directMachineTemplate,
        MM2CompressedProofHeapEncoding.nodeRow] using replay)
  · exact replay
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-machine" "mm-compressed-index-successor" _ _
      (by decide) (by simpa [directMachineTemplate,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
        using replay)

/-- Every complete direct matcher obtains the exact stack successor row. -/
theorem canonical_direct_successor_factor_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    applySubst substitution directStackSuccessorPattern =
      context.stackSuccessorRow := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    canonical_matcher_dynamic_factor_origin context item
      "mm-compressed-index-successor"
      [.expression
        [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
       .var "stack-position", .var "next-stack-position"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directStackSuccessorPattern]) matcherMember
  simp only [canonicalDirectDynamicRows, List.mem_cons, List.not_mem_nil,
    or_false] at carrierMember
  rcases carrierMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-index-successor" "mm-compressed-step-pending" _ _
      (by decide) (by simpa [directStackSuccessorPattern,
        DirectProofContext.pendingRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-index-successor" "mm-compressed-heap-lookup" _ _
      (by decide) (by simpa [directStackSuccessorPattern,
        DirectProofContext.lookupRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-index-successor" "mm-compressed-heap-proof" _ _
      (by decide) (by simpa [directStackSuccessorPattern, heapProofRow]
        using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-index-successor" "mm-compressed-node" _ _
      (by decide) (by simpa [directStackSuccessorPattern,
        MM2CompressedProofHeapEncoding.nodeRow] using replay)
  · exfalso
    exact applySubst_expression_symbol_head_ne substitution
      "mm-compressed-index-successor" "mm-compressed-machine" _ _
      (by decide) (by simpa [directStackSuccessorPattern,
        DirectProofContext.machineRow] using replay)
  · exact replay

/-- Representation-neutral assembly of the direct handler's successor machine
row from exact input-factor replay. -/
theorem direct_nextMachine_output_exact_of_factors
    (context : DirectProofContext) (substitution : Subst)
    (pendingExact : applySubst substitution directPendingTemplate =
      context.pendingRow)
    (machineExact : applySubst substitution directMachineTemplate =
      context.machineRow)
    (successorExact : applySubst substitution directStackSuccessorPattern =
      context.stackSuccessorRow)
    (machineCovered : templateCovered substitution directMachineTemplate = true)
    (successorCovered :
      templateCovered substitution directStackSuccessorPattern = true) :
    instantiateTemplateAtom? substitution directNextMachineTemplate =
      some context.nextMachineRow := by
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    simp [directPendingTemplate, directMachineTemplate,
      directStackSuccessorPattern, directNextMachineTemplate,
      DirectProofContext.pendingRow, DirectProofContext.machineRow,
      DirectProofContext.stackSuccessorRow, DirectProofContext.nextMachineRow,
      compressedIndexSuccessorRow, compressedStackOwner, applySubst,
      applySubst.applySubstList, Subst.lookup]
      at pendingExact machineExact successorExact ⊢
    aesop
  · simp [directMachineTemplate,
      directStackSuccessorPattern, directNextMachineTemplate,
      templateCovered, templatesCovered]
      at machineCovered successorCovered ⊢
    aesop

/-- Representation-neutral assembly of the compact stack successor. -/
theorem direct_compactStack_output_exact_of_factors
    (context : DirectProofContext) (item : ProofOccurrence)
    (substitution : Subst)
    (pendingExact : applySubst substitution directPendingTemplate =
      context.pendingRow)
    (heapExact : applySubst substitution directHeapProofPattern =
      heapProofRow context.proofOwner context.index item)
    (machineExact : applySubst substitution directMachineTemplate =
      context.machineRow)
    (heapCovered : templateCovered substitution directHeapProofPattern = true)
    (machineCovered : templateCovered substitution directMachineTemplate = true) :
    instantiateTemplateAtom? substitution directStackCellTemplate =
      some (compressedStackRow context.proofOwner context.stackPosition item) := by
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    cases item with
    | mk identity value =>
        simp [directPendingTemplate, directHeapProofPattern,
          directMachineTemplate, directStackCellTemplate,
          DirectProofContext.pendingRow, DirectProofContext.machineRow,
          heapProofRow, compressedStackRow, applySubst,
          applySubst.applySubstList, Subst.lookup]
          at pendingExact heapExact machineExact ⊢
        aesop
  · simp [directHeapProofPattern,
      directMachineTemplate, directStackCellTemplate, templateCovered,
      templatesCovered] at heapCovered machineCovered ⊢
    aesop

/-- Representation-neutral assembly of the normal-stack occurrence row. -/
theorem direct_normalStack_output_exact_of_factors
    (context : DirectProofContext) (item : ProofOccurrence)
    (substitution : Subst)
    (pendingExact : applySubst substitution directPendingTemplate =
      context.pendingRow)
    (nodeExact : applySubst substitution directNodePattern =
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item)
    (machineExact : applySubst substitution directMachineTemplate =
      context.machineRow)
    (nodeCovered : templateCovered substitution directNodePattern = true)
    (machineCovered : templateCovered substitution directMachineTemplate = true) :
    instantiateTemplateAtom? substitution directNormalStackCellTemplate =
      some (normalStackRow context.proofOwner context.stackPosition item) := by
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    cases item with
    | mk identity value =>
        cases value
        simp [directPendingTemplate, directNodePattern,
          directMachineTemplate, directNormalStackCellTemplate,
          DirectProofContext.pendingRow, DirectProofContext.machineRow,
          MM2CompressedProofHeapEncoding.nodeRow, normalStackRow, applySubst,
          applySubst.applySubstList, Subst.lookup]
          at pendingExact nodeExact machineExact ⊢
        aesop
  · simp [directNodePattern,
      directMachineTemplate, directNormalStackCellTemplate, templateCovered,
      templatesCovered] at nodeCovered machineCovered ⊢
    aesop

/-- Representation-neutral assembly of the resumed scanner row. -/
theorem direct_resumedScan_output_exact_of_factor
    (context : DirectProofContext) (substitution : Subst)
    (pendingExact : applySubst substitution directPendingTemplate =
      context.pendingRow)
    (pendingCovered : templateCovered substitution directPendingTemplate = true) :
    instantiateTemplateAtom? substitution directResumedScanTemplate =
      some context.resumedScanRow := by
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    simp [directPendingTemplate, directResumedScanTemplate,
      DirectProofContext.pendingRow, DirectProofContext.resumedScanRow,
      applySubst, applySubst.applySubstList, Subst.lookup] at pendingExact ⊢
    aesop
  · simp [directPendingTemplate, directResumedScanTemplate, templateCovered,
      templatesCovered] at pendingCovered ⊢
    aesop

/-- All variables of the next machine row are bound by the complete input,
and every complete match reconstructs the exact source-derived successor. -/
theorem canonical_direct_nextMachine_output_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    instantiateTemplateAtom? substitution directNextMachineTemplate =
      some context.nextMachineRow := by
  have pendingExact :=
    canonical_direct_pending_factor_exact context item matcherMember
  have machineExact :=
    canonical_direct_machine_factor_exact context item matcherMember
  have successorExact :=
    canonical_direct_successor_factor_exact context item matcherMember
  have pendingCovered := canonical_matcher_factor_covered context item
    directPendingTemplate (by simp [directProofPatterns]) matcherMember
  have machineCovered := canonical_matcher_factor_covered context item
    directMachineTemplate (by simp [directProofPatterns]) matcherMember
  have successorCovered := canonical_matcher_factor_covered context item
    directStackSuccessorPattern
      (by simp [directProofPatterns]) matcherMember
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    simp [directPendingTemplate, directMachineTemplate,
      directStackSuccessorPattern, directNextMachineTemplate,
      DirectProofContext.pendingRow, DirectProofContext.machineRow,
      DirectProofContext.stackSuccessorRow, DirectProofContext.nextMachineRow,
      compressedIndexSuccessorRow, compressedStackOwner, applySubst,
      applySubst.applySubstList, Subst.lookup]
      at pendingExact machineExact successorExact ⊢
    aesop
  · simp [directPendingTemplate, directMachineTemplate,
      directStackSuccessorPattern, directNextMachineTemplate,
      templateCovered, templatesCovered]
      at pendingCovered machineCovered successorCovered ⊢
    aesop

/-- The compact stack output is reconstructed from the matched owner,
machine frontier, and proof-heap identity. -/
theorem canonical_direct_compactStack_output_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    instantiateTemplateAtom? substitution directStackCellTemplate =
      some (compressedStackRow context.proofOwner
        context.stackPosition item) := by
  have pendingExact :=
    canonical_direct_pending_factor_exact context item matcherMember
  have heapExact :=
    canonical_direct_heap_factor_exact context item matcherMember
  have machineExact :=
    canonical_direct_machine_factor_exact context item matcherMember
  have pendingCovered := canonical_matcher_factor_covered context item
    directPendingTemplate (by simp [directProofPatterns]) matcherMember
  have heapCovered := canonical_matcher_factor_covered context item
    directHeapProofPattern
      (by simp [directProofPatterns]) matcherMember
  have machineCovered := canonical_matcher_factor_covered context item
    directMachineTemplate (by simp [directProofPatterns]) matcherMember
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    cases item with
    | mk identity value =>
        simp [directPendingTemplate, directHeapProofPattern,
          directMachineTemplate, directStackCellTemplate,
          DirectProofContext.pendingRow, DirectProofContext.machineRow,
          heapProofRow, compressedStackRow, applySubst,
          applySubst.applySubstList, Subst.lookup]
          at pendingExact heapExact machineExact ⊢
        aesop
  · simp [directPendingTemplate, directHeapProofPattern,
      directMachineTemplate, directStackCellTemplate, templateCovered,
      templatesCovered] at pendingCovered heapCovered machineCovered ⊢
    aesop

/-- The normal stack output retains the exact formula and source occurrence
from the matched node row. -/
theorem canonical_direct_normalStack_output_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    instantiateTemplateAtom? substitution directNormalStackCellTemplate =
      some (normalStackRow context.proofOwner context.stackPosition item) := by
  have pendingExact :=
    canonical_direct_pending_factor_exact context item matcherMember
  have nodeExact :=
    canonical_direct_node_factor_exact context item matcherMember
  have machineExact :=
    canonical_direct_machine_factor_exact context item matcherMember
  have pendingCovered := canonical_matcher_factor_covered context item
    directPendingTemplate (by simp [directProofPatterns]) matcherMember
  have nodeCovered := canonical_matcher_factor_covered context item
    directNodePattern (by simp [directProofPatterns]) matcherMember
  have machineCovered := canonical_matcher_factor_covered context item
    directMachineTemplate (by simp [directProofPatterns]) matcherMember
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    cases item with
    | mk identity value =>
        cases value
        simp [directPendingTemplate, directNodePattern,
          directMachineTemplate, directNormalStackCellTemplate,
          DirectProofContext.pendingRow, DirectProofContext.machineRow,
          MM2CompressedProofHeapEncoding.nodeRow, normalStackRow, applySubst,
          applySubst.applySubstList, Subst.lookup]
          at pendingExact nodeExact machineExact ⊢
        aesop
  · simp [directPendingTemplate, directNodePattern,
      directMachineTemplate, directNormalStackCellTemplate, templateCovered,
      templatesCovered] at pendingCovered nodeCovered machineCovered ⊢
    aesop

/-- The resumed scanner row is reconstructed entirely from the exact pending
request, so the source byte frontier cannot drift during a proof hit. -/
theorem canonical_direct_resumedScan_output_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (canonicalDirectProofSpace context item)) :
    instantiateTemplateAtom? substitution directResumedScanTemplate =
      some context.resumedScanRow := by
  have pendingExact :=
    canonical_direct_pending_factor_exact context item matcherMember
  have pendingCovered := canonical_matcher_factor_covered context item
    directPendingTemplate (by simp [directProofPatterns]) matcherMember
  unfold instantiateTemplateAtom?
  rw [if_pos]
  · cases context
    simp [directPendingTemplate, directResumedScanTemplate,
      DirectProofContext.pendingRow, DirectProofContext.resumedScanRow,
      applySubst, applySubst.applySubstList, Subst.lookup] at pendingExact ⊢
    aesop
  · simp [directPendingTemplate, directResumedScanTemplate, templateCovered,
      templatesCovered] at pendingCovered ⊢
    aesop

/-- Every matcher result on the canonical request emits the same four
source-derived dynamic outputs. -/
theorem canonical_direct_proof_matcher_exact
    (context : DirectProofContext) (item : ProofOccurrence) :
    ∀ substitution ∈ directProofMatcherRows
        (canonicalDirectProofSpace context item),
      instantiateTemplateAtom? substitution directNextMachineTemplate =
          some context.nextMachineRow ∧
        instantiateTemplateAtom? substitution directStackCellTemplate =
          some (compressedStackRow context.proofOwner
            context.stackPosition item) ∧
        instantiateTemplateAtom? substitution directNormalStackCellTemplate =
          some (normalStackRow context.proofOwner context.stackPosition item) ∧
        instantiateTemplateAtom? substitution directResumedScanTemplate =
          some context.resumedScanRow := by
  intro substitution matcherMember
  exact ⟨canonical_direct_nextMachine_output_exact context item matcherMember,
    canonical_direct_compactStack_output_exact context item matcherMember,
    canonical_direct_normalStack_output_exact context item matcherMember,
    canonical_direct_resumedScan_output_exact context item matcherMember⟩

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
#print axioms speculativeDirectProofDirective_atom_exact
#print axioms canonicalDirectProofSpace_injective
#print axioms canonicalDirectProofSpace_changed_sourceOccurrence
#print axioms canonical_direct_pending_factor_exact
#print axioms canonical_direct_lookup_factor_exact
#print axioms canonical_direct_heap_factor_exact
#print axioms canonical_direct_node_factor_exact
#print axioms canonical_direct_machine_factor_exact
#print axioms canonical_direct_successor_factor_exact
#print axioms canonical_direct_nextMachine_output_exact
#print axioms canonical_direct_compactStack_output_exact
#print axioms canonical_direct_normalStack_output_exact
#print axioms canonical_direct_resumedScan_output_exact
#print axioms canonical_direct_proof_matcher_exact
#print axioms canonical_heap_row_in_live
#print axioms canonical_node_row_in_live
#print axioms canonical_exact_direct_proof_match
#print axioms canonical_direct_proof_request_frame
#print axioms canonical_direct_proof_hit_commutes

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
