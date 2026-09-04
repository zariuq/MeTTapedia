import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame

/-!
# Exact matcher for the decorated speculative assertion launcher

The ordered presentation adds one captured normal-dispatch capability to the
compact assertion launcher before speculative lookup is compiled.  This file
matches that derived rule against the exact source-indexed assertion rows and
proves every consumed and emitted value, including the captured bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK

def decoratedDirectAssertionSliceRows
    (context : DirectAssertionContext) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (decoratedDirectAssertionMatchSlice context)
      decoratedDirectAssertionDirective.rule.input).map Prod.fst

private def decoratedAssertionSelfInput : Atom :=
  match decoratedDirectAssertionDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-decorated-assertion-input"

private def decoratedAssertionSelfOutput : Atom :=
  match decoratedDirectAssertionDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-decorated-assertion-output"

private def decoratedAssertionSelfSubst : Subst :=
  [("assertion-launch-output", decoratedAssertionSelfOutput),
   ("assertion-launch-input", decoratedAssertionSelfInput)]

private def decoratedAssertionPendingSubst
    (context : DirectAssertionContext) : Subst :=
  [("terminal-digit",
      natAtom (CompressedIndexCode.ofNat context.index).terminalDigit),
   ("reverse-prefix",
      listAtom natAtom
        (CompressedIndexCode.ofNat context.index).reversePrefixDigits),
   ("remaining-bytes", context.bytes),
   ("word-position", natAtom context.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ decoratedAssertionSelfSubst

private def decoratedAssertionLookupSubst
    (context : DirectAssertionContext) : Subst :=
  [("speculative-cursor", context.code context.cursor),
   ("compressed-index", context.code context.index)] ++
    decoratedAssertionPendingSubst context

private def decoratedAssertionHeapSubst
    (context : DirectAssertionContext) : Subst :=
  [("assertion-label", stringAtom context.assertionLabel),
   ("assertion-position", natAtom context.assertionPosition)] ++
    decoratedAssertionLookupSubst context

private def decoratedAssertionMachineSubst
    (context : DirectAssertionContext) : Subst :=
  [("stack-position", context.code context.stackPosition),
   ("node-next", context.code context.nodeNext),
   ("heap-next", context.code context.heapNext)] ++
    decoratedAssertionHeapSubst context

private def decoratedAssertionHeaderSubst
    (context : DirectAssertionContext) : Subst :=
  [("assertion-hypothesis-count", natAtom context.hypothesisCount)] ++
    decoratedAssertionMachineSubst context

private def decoratedAssertionRejoinSubst
    (context : DirectAssertionContext) : Subst :=
  [("compressed-assertion-rejoin-rule", compressedAssertionRejoinRule)] ++
    decoratedAssertionHeaderSubst context

def decoratedAssertionFinalSubst
    (context : DirectAssertionContext) : Subst :=
  [("normal-bridge-rule", compressedNormalDispatchBridgeRule)] ++
    decoratedAssertionRejoinSubst context

private theorem decoratedAssertionSelf_match :
    Conformance.Computable.cmatchAtom [] directAssertionSelfTemplate
      decoratedDirectAssertionDirective.atom =
        some decoratedAssertionSelfSubst := by
  decide +kernel

private theorem decoratedAssertionPending_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom decoratedAssertionSelfSubst
      directAssertionPendingTemplate context.pendingRow =
        some (decoratedAssertionPendingSubst context) := by
  cases context
  simp [decoratedAssertionPendingSubst, decoratedAssertionSelfSubst,
    DirectAssertionContext.pendingRow, DirectAssertionContext.bytes,
    DirectAssertionContext.code, directAssertionPendingTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup,
    CompressedIndexCode.atom, compressedIndexCodeAtom]

private theorem decoratedAssertionLookup_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionPendingSubst context)
      directAssertionLookupTemplate context.lookupRow =
        some (decoratedAssertionLookupSubst context) := by
  cases context
  simp [decoratedAssertionLookupSubst, decoratedAssertionPendingSubst,
    decoratedAssertionSelfSubst, DirectAssertionContext.lookupRow,
    DirectAssertionContext.bytes, DirectAssertionContext.code,
    directAssertionLookupTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem decoratedAssertionHeap_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionLookupSubst context)
      directAssertionHeapTemplate context.heapRow =
        some (decoratedAssertionHeapSubst context) := by
  cases context
  simp [decoratedAssertionHeapSubst, decoratedAssertionLookupSubst,
    decoratedAssertionPendingSubst, decoratedAssertionSelfSubst,
    DirectAssertionContext.heapRow, DirectAssertionContext.code,
    directAssertionHeapTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem decoratedAssertionMachine_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionHeapSubst context)
      directAssertionMachineTemplate context.machineRow =
        some (decoratedAssertionMachineSubst context) := by
  cases context
  simp [decoratedAssertionMachineSubst, decoratedAssertionHeapSubst,
    decoratedAssertionLookupSubst, decoratedAssertionPendingSubst,
    decoratedAssertionSelfSubst, DirectAssertionContext.machineRow,
    DirectAssertionContext.code, directAssertionMachineTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem decoratedAssertionHeader_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionMachineSubst context)
      directAssertionHeaderTemplate context.headerRow =
        some (decoratedAssertionHeaderSubst context) := by
  cases context
  simp [decoratedAssertionHeaderSubst, decoratedAssertionMachineSubst,
    decoratedAssertionHeapSubst, decoratedAssertionLookupSubst,
    decoratedAssertionPendingSubst, decoratedAssertionSelfSubst,
    DirectAssertionContext.headerRow, directAssertionHeaderTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem decoratedAssertionRejoin_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionHeaderSubst context)
      directAssertionRejoinCaptureTemplate context.rejoinCaptureRow =
        some (decoratedAssertionRejoinSubst context) := by
  cases context
  simp [decoratedAssertionRejoinSubst, decoratedAssertionHeaderSubst,
    decoratedAssertionMachineSubst, decoratedAssertionHeapSubst,
    decoratedAssertionLookupSubst, decoratedAssertionPendingSubst,
    decoratedAssertionSelfSubst, DirectAssertionContext.rejoinCaptureRow,
    directAssertionRejoinCaptureTemplate, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem decoratedAssertionBridge_match
    (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (decoratedAssertionRejoinSubst context)
      decoratedDirectAssertionBridgeCaptureTemplate
      decoratedDirectAssertionBridgeCaptureRow =
        some (decoratedAssertionFinalSubst context) := by
  cases context
  simp [decoratedAssertionFinalSubst, decoratedAssertionRejoinSubst,
    decoratedAssertionHeaderSubst, decoratedAssertionMachineSubst,
    decoratedAssertionHeapSubst, decoratedAssertionLookupSubst,
    decoratedAssertionPendingSubst, decoratedAssertionSelfSubst,
    decoratedDirectAssertionBridgeCaptureTemplate,
    decoratedDirectAssertionBridgeCaptureRow,
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

private def decoratedAssertionConsumed
    (context : DirectAssertionContext) : List Atom :=
  [decoratedDirectAssertionBridgeCaptureRow, context.rejoinCaptureRow,
   context.headerRow, context.machineRow, context.heapRow, context.lookupRow,
   context.pendingRow, decoratedDirectAssertionDirective.atom]

theorem decorated_assertion_final_subst_in_slice
    (context : DirectAssertionContext) :
    decoratedAssertionFinalSubst context ∈
      decoratedDirectAssertionSliceRows context := by
  unfold decoratedDirectAssertionSliceRows
  rw [decoratedDirectAssertionDirective_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(decoratedAssertionFinalSubst context,
    decoratedAssertionConsumed context), ?_, rfl⟩
  unfold decoratedDirectAssertionPatterns directAssertionPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := decoratedDirectAssertionDirective.atom)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.pendingRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionPending_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.lookupRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionLookup_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.heapRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionHeap_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.machineRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionMachine_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.headerRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionHeader_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.rejoinCaptureRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionRejoin_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := decoratedDirectAssertionBridgeCaptureRow)
  · simp [decoratedDirectAssertionMatchSlice, decoratedDirectAssertionDataSlice]
  · exact decoratedAssertionBridge_match context
  simp [Conformance.Computable.cmatchPattern.go,
    decoratedAssertionConsumed]

theorem decorated_assertion_final_subst_instantiates_outputs
    (context : DirectAssertionContext) :
    instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionPendingTemplate = some context.pendingRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionLookupTemplate = some context.lookupRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionMachineTemplate = some context.machineRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionContextTemplate = some context.assertionContextRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionNormalControlTemplate = some context.normalControlRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionNormalLabelTemplate = some context.normalLabelRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          directAssertionReloadTemplate = some context.reloadRow ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule ∧
      instantiateTemplateAtom? (decoratedAssertionFinalSubst context)
          (.var "normal-bridge-rule") =
        some compressedNormalDispatchBridgeRule := by
  cases context
  simp [decoratedAssertionFinalSubst, decoratedAssertionRejoinSubst,
    decoratedAssertionHeaderSubst, decoratedAssertionMachineSubst,
    decoratedAssertionHeapSubst, decoratedAssertionLookupSubst,
    decoratedAssertionPendingSubst, decoratedAssertionSelfSubst,
    instantiateTemplateAtom?, templateCovered, templatesCovered, applySubst,
    applySubst.applySubstList, Subst.lookup, directAssertionPendingTemplate,
    directAssertionLookupTemplate, directAssertionMachineTemplate,
    directAssertionContextTemplate, directAssertionPCTemplate,
    directAssertionNextPCTemplate, directAssertionNormalControlTemplate,
    directAssertionNormalLabelTemplate, directAssertionReloadTemplate,
    DirectAssertionContext.pendingRow, DirectAssertionContext.lookupRow,
    DirectAssertionContext.machineRow,
    DirectAssertionContext.assertionContextRow,
    DirectAssertionContext.normalControlRow,
    DirectAssertionContext.normalLabelRow, DirectAssertionContext.reloadRow,
    DirectAssertionContext.pc, DirectAssertionContext.nextPC,
    DirectAssertionContext.bytes, DirectAssertionContext.code,
    CompressedIndexCode.atom, compressedIndexCodeAtom, natAtom]

/-- Exact positive matcher for the compiler-produced ordered assertion rule.
Every output capability is recovered from a concrete presentation row. -/
theorem decorated_assertion_slice_instantiates_launch
    (context : DirectAssertionContext) :
  ∃ substitution ∈ decoratedDirectAssertionSliceRows context,
    instantiateTemplateAtom? substitution directAssertionPendingTemplate =
        some context.pendingRow ∧
      instantiateTemplateAtom? substitution directAssertionLookupTemplate =
        some context.lookupRow ∧
      instantiateTemplateAtom? substitution directAssertionMachineTemplate =
        some context.machineRow ∧
      instantiateTemplateAtom? substitution directAssertionContextTemplate =
        some context.assertionContextRow ∧
      instantiateTemplateAtom? substitution
          directAssertionNormalControlTemplate = some context.normalControlRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalLabelTemplate =
        some context.normalLabelRow ∧
      instantiateTemplateAtom? substitution directAssertionReloadTemplate =
        some context.reloadRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule ∧
      instantiateTemplateAtom? substitution (.var "normal-bridge-rule") =
        some compressedNormalDispatchBridgeRule := by
  exact ⟨decoratedAssertionFinalSubst context,
    decorated_assertion_final_subst_in_slice context,
    decorated_assertion_final_subst_instantiates_outputs context⟩

#print axioms decorated_assertion_final_subst_in_slice
#print axioms decorated_assertion_final_subst_instantiates_outputs
#print axioms decorated_assertion_slice_instantiates_launch

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionMatch
