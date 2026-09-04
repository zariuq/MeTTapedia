import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Continuous compressed assertion adapter

This module isolates the source-indexed boundary between compressed heap
lookup and the shared normal assertion verifier.  The launch half consumes a
source-derived assertion heap entry and publishes the exact normal control,
label occurrence, and rejoin context.  The later rejoin half will consume the
normal verifier's exact result and restore the common compressed public
boundary.

The normal assertion calculation remains an independently verified segment;
the adapter neither repeats that calculation nor treats an asserted result as
an input witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem applySubst_groundAtom (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) :
    applySubst substitution atom = atom := by
  match atom with
  | .var name => simp [isGroundAtom] at ground
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression atoms =>
      simp only [applySubst]
      have listGround : isGroundAtom.isGroundList atoms = true := by
        simpa only [isGroundAtom] using ground
      exact congrArg Atom.expression
        (applySubstList_ground substitution atoms listGround)
where
  applySubstList_ground (substitution : Subst) (atoms : List Atom)
      (ground : isGroundAtom.isGroundList atoms = true) :
      applySubst.applySubstList substitution atoms = atoms := by
    match atoms with
    | [] => rfl
    | atom :: atoms =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [applySubst.applySubstList]
        congr 1
        · exact applySubst_groundAtom substitution atom ground.1
        · exact applySubstList_ground substitution atoms ground.2

private theorem templateCovered_groundAtom (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) :
    templateCovered substitution atom = true := by
  match atom with
  | .var name => simp [isGroundAtom] at ground
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression atoms =>
      simp only [templateCovered]
      have listGround : isGroundAtom.isGroundList atoms = true := by
        simpa only [isGroundAtom] using ground
      exact templatesCovered_ground substitution atoms listGround
where
  templatesCovered_ground (substitution : Subst) (atoms : List Atom)
      (ground : isGroundAtom.isGroundList atoms = true) :
      templatesCovered substitution atoms = true := by
    match atoms with
    | [] => rfl
    | atom :: atoms =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [templatesCovered, Bool.and_eq_true]
        exact ⟨templateCovered_groundAtom substitution atom ground.1,
          templatesCovered_ground substitution atoms ground.2⟩

@[simp] private theorem applySubst_stringAtom
    (substitution : Subst) (value : String) :
    applySubst substitution (stringAtom value) = stringAtom value :=
  applySubst_groundAtom substitution (stringAtom value)
    (isGroundAtom_stringAtom value)

@[simp] private theorem templateCovered_stringAtom
    (substitution : Subst) (value : String) :
    templateCovered substitution (stringAtom value) = true :=
  templateCovered_groundAtom substitution (stringAtom value)
    (isGroundAtom_stringAtom value)

/-! ## Exact generated assertion-launch surface -/

def directAssertionSelfTemplate : Atom :=
  .expression
    [.symbol "exec", speculativeDirectAssertionDirective.loc,
      .var "assertion-launch-input", .var "assertion-launch-output"]

def directAssertionPendingTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]

def directAssertionLookupTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "speculative-cursor"]

def directAssertionHeapTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", .var "proof-owner",
      .var "compressed-index", .var "assertion-position",
      .var "assertion-label"]

def directAssertionMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

def directAssertionHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-header", .var "scope-owner",
      .var "assertion-position", .var "assertion-label",
      .var "assertion-hypothesis-count"]

def directAssertionRejoinCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol "assertion-rejoin",
      .var "compressed-assertion-rejoin-rule"]

def directAssertionPCTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", .var "word-position",
      .var "remaining-bytes", .var "compressed-index"]

def directAssertionNextPCTemplate : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", directAssertionPCTemplate]

def directAssertionContextTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      directAssertionPCTemplate, directAssertionNextPCTemplate,
      .var "assertion-label", .var "heap-next", .var "node-next"]

def directAssertionNormalControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope-owner", .var "proof-owner",
      directAssertionPCTemplate, .var "stack-position"]

def directAssertionNormalLabelTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      .var "proof-owner", directAssertionPCTemplate,
      directAssertionNextPCTemplate, .var "assertion-label"]

def directAssertionReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-compressed-normal-dispatch", .var "proof-owner"]

def directAssertionPatterns : List Atom :=
  [directAssertionSelfTemplate, directAssertionPendingTemplate,
   directAssertionLookupTemplate, directAssertionHeapTemplate,
   directAssertionMachineTemplate, directAssertionHeaderTemplate,
   directAssertionRejoinCaptureTemplate]

def directAssertionSinks : List Sink :=
  [.remove directAssertionPendingTemplate,
   .remove directAssertionLookupTemplate,
   .remove directAssertionMachineTemplate,
   .add directAssertionContextTemplate,
   .add directAssertionNormalControlTemplate,
   .add directAssertionNormalLabelTemplate,
   .add directAssertionReloadTemplate,
   .add (.var "compressed-assertion-rejoin-rule")]

theorem speculative_direct_assertion_input_exact :
    speculativeDirectAssertionDirective.rule.input =
      .compat (mkPattern directAssertionPatterns) := by
  decide +kernel

theorem speculative_direct_assertion_sinks_exact :
    speculativeDirectAssertionDirective.rule.tmpl.sinks =
      directAssertionSinks := by
  decide +kernel

/-! ## Source-indexed launch context -/

structure DirectAssertionContext where
  scopeOwner : Atom
  proofOwner : Atom
  wordPosition : Nat
  remainingBytes : List UInt8
  index : Nat
  cursor : Nat
  heapNext : Nat
  nodeNext : Nat
  stackPosition : Nat
  assertionPosition : Nat
  assertionLabel : String
  hypothesisCount : Nat

namespace DirectAssertionContext

def code (_context : DirectAssertionContext) (value : Nat) : Atom :=
  (CompressedIndexCode.ofNat value).atom

def bytes (context : DirectAssertionContext) : Atom :=
  listAtom natAtom (context.remainingBytes.map UInt8.toNat)

def pendingRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", context.scopeOwner,
      context.proofOwner, natAtom context.wordPosition, context.bytes,
      context.code context.index]

def lookupRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", context.scopeOwner,
      context.proofOwner, natAtom context.wordPosition, context.bytes,
      context.code context.index, context.code context.cursor]

def heapRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", context.proofOwner,
      context.code context.index, natAtom context.assertionPosition,
      stringAtom context.assertionLabel]

def machineRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", context.scopeOwner, context.proofOwner,
      context.code context.heapNext, context.code context.nodeNext,
      context.code context.stackPosition]

def headerRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-assertion-header", context.scopeOwner,
      natAtom context.assertionPosition, stringAtom context.assertionLabel,
      natAtom context.hypothesisCount]

def rejoinCaptureRow (_context : DirectAssertionContext) : Atom :=
  compressedOwnedRuntimeRuleRow "assertion-rejoin"
    compressedAssertionRejoinRule

def pc (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", natAtom context.wordPosition,
      context.bytes, context.code context.index]

def nextPC (context : DirectAssertionContext) : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", context.pc]

def assertionContextRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", context.scopeOwner,
      context.proofOwner, natAtom context.wordPosition, context.bytes,
      context.pc, context.nextPC, stringAtom context.assertionLabel,
      context.code context.heapNext, context.code context.nodeNext]

def normalControlRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-normal-control", context.scopeOwner, context.proofOwner,
      context.pc, context.code context.stackPosition]

def normalLabelRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      context.proofOwner, context.pc, context.nextPC,
      stringAtom context.assertionLabel]

def reloadRow (context : DirectAssertionContext) : Atom :=
  .expression
    [.symbol "mm-reload-compressed-normal-dispatch", context.proofOwner]

def launchRows (context : DirectAssertionContext) : List Atom :=
  [context.assertionContextRow, context.normalControlRow,
   context.normalLabelRow, context.reloadRow,
   compressedAssertionRejoinRule]

end DirectAssertionContext

/-! ## Canonical symbolic matcher -/

def directAssertionMatchSlice (context : DirectAssertionContext) : List Atom :=
  [speculativeDirectAssertionDirective.atom, context.pendingRow,
   context.lookupRow, context.heapRow, context.machineRow,
   context.headerRow, context.rejoinCaptureRow]

def directAssertionSliceRows (context : DirectAssertionContext) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (directAssertionMatchSlice context)
      speculativeDirectAssertionDirective.rule.input).map Prod.fst

private def directAssertionSelfInput : Atom :=
  match speculativeDirectAssertionDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-direct-assertion-input"

private def directAssertionSelfOutput : Atom :=
  match speculativeDirectAssertionDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-direct-assertion-output"

private def assertionSelfSubst : Subst :=
  [("assertion-launch-output", directAssertionSelfOutput),
   ("assertion-launch-input", directAssertionSelfInput)]

private def assertionPendingSubst (context : DirectAssertionContext) : Subst :=
  [("terminal-digit",
      natAtom (CompressedIndexCode.ofNat context.index).terminalDigit),
   ("reverse-prefix",
      listAtom natAtom
        (CompressedIndexCode.ofNat context.index).reversePrefixDigits),
   ("remaining-bytes", context.bytes),
   ("word-position", natAtom context.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ assertionSelfSubst

private def assertionLookupSubst (context : DirectAssertionContext) : Subst :=
  [("speculative-cursor", context.code context.cursor),
   ("compressed-index", context.code context.index)] ++
    assertionPendingSubst context

private def assertionHeapSubst (context : DirectAssertionContext) : Subst :=
  [("assertion-label", stringAtom context.assertionLabel),
   ("assertion-position", natAtom context.assertionPosition)] ++
    assertionLookupSubst context

private def assertionMachineSubst (context : DirectAssertionContext) : Subst :=
  [("stack-position", context.code context.stackPosition),
   ("node-next", context.code context.nodeNext),
   ("heap-next", context.code context.heapNext)] ++
    assertionHeapSubst context

private def assertionHeaderSubst (context : DirectAssertionContext) : Subst :=
  [("assertion-hypothesis-count", natAtom context.hypothesisCount)] ++
    assertionMachineSubst context

private def assertionFinalSubst (context : DirectAssertionContext) : Subst :=
  [("compressed-assertion-rejoin-rule", compressedAssertionRejoinRule)] ++
    assertionHeaderSubst context

private theorem assertionSelf_match :
    Conformance.Computable.cmatchAtom [] directAssertionSelfTemplate
      speculativeDirectAssertionDirective.atom = some assertionSelfSubst := by
  decide +kernel

private theorem assertionPending_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom assertionSelfSubst
      directAssertionPendingTemplate context.pendingRow =
        some (assertionPendingSubst context) := by
  cases context
  simp [assertionPendingSubst, assertionSelfSubst,
    DirectAssertionContext.pendingRow, DirectAssertionContext.bytes,
    DirectAssertionContext.code, directAssertionPendingTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup,
    CompressedIndexCode.atom, compressedIndexCodeAtom]

private theorem assertionLookup_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (assertionPendingSubst context)
      directAssertionLookupTemplate context.lookupRow =
        some (assertionLookupSubst context) := by
  cases context
  simp [assertionLookupSubst, assertionPendingSubst, assertionSelfSubst,
    DirectAssertionContext.lookupRow, DirectAssertionContext.bytes,
    DirectAssertionContext.code, directAssertionLookupTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem assertionHeap_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (assertionLookupSubst context)
      directAssertionHeapTemplate context.heapRow =
        some (assertionHeapSubst context) := by
  cases context
  simp [assertionHeapSubst, assertionLookupSubst, assertionPendingSubst,
    assertionSelfSubst, DirectAssertionContext.heapRow,
    DirectAssertionContext.code, directAssertionHeapTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem assertionMachine_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (assertionHeapSubst context)
      directAssertionMachineTemplate context.machineRow =
        some (assertionMachineSubst context) := by
  cases context
  simp [assertionMachineSubst, assertionHeapSubst, assertionLookupSubst,
    assertionPendingSubst, assertionSelfSubst,
    DirectAssertionContext.machineRow, DirectAssertionContext.code,
    directAssertionMachineTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem assertionHeader_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (assertionMachineSubst context)
      directAssertionHeaderTemplate context.headerRow =
        some (assertionHeaderSubst context) := by
  cases context
  simp [assertionHeaderSubst, assertionMachineSubst, assertionHeapSubst,
    assertionLookupSubst, assertionPendingSubst, assertionSelfSubst,
    DirectAssertionContext.headerRow, directAssertionHeaderTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem assertionRejoin_match (context : DirectAssertionContext) :
    Conformance.Computable.cmatchAtom (assertionHeaderSubst context)
      directAssertionRejoinCaptureTemplate context.rejoinCaptureRow =
        some (assertionFinalSubst context) := by
  cases context
  simp [assertionFinalSubst, assertionHeaderSubst, assertionMachineSubst,
    assertionHeapSubst, assertionLookupSubst, assertionPendingSubst,
    assertionSelfSubst, DirectAssertionContext.rejoinCaptureRow,
    directAssertionRejoinCaptureTemplate, compressedOwnedRuntimeRuleRow,
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

private def canonicalAssertionConsumed
    (context : DirectAssertionContext) : List Atom :=
  [context.rejoinCaptureRow, context.headerRow, context.machineRow,
   context.heapRow, context.lookupRow, context.pendingRow,
   speculativeDirectAssertionDirective.atom]

private theorem assertion_final_subst_in_slice
    (context : DirectAssertionContext) :
    assertionFinalSubst context ∈ directAssertionSliceRows context := by
  unfold directAssertionSliceRows
  rw [speculative_direct_assertion_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(assertionFinalSubst context,
    canonicalAssertionConsumed context), ?_, rfl⟩
  unfold directAssertionPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := speculativeDirectAssertionDirective.atom)
  · simp [directAssertionMatchSlice]
  · exact assertionSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.pendingRow)
  · simp [directAssertionMatchSlice]
  · exact assertionPending_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.lookupRow)
  · simp [directAssertionMatchSlice]
  · exact assertionLookup_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.heapRow)
  · simp [directAssertionMatchSlice]
  · exact assertionHeap_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.machineRow)
  · simp [directAssertionMatchSlice]
  · exact assertionMachine_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.headerRow)
  · simp [directAssertionMatchSlice]
  · exact assertionHeader_match context
  apply cmatchPattern_go_cons_of_selected (concrete := context.rejoinCaptureRow)
  · simp [directAssertionMatchSlice]
  · exact assertionRejoin_match context
  simp [Conformance.Computable.cmatchPattern.go,
    canonicalAssertionConsumed]

private theorem assertion_final_subst_instantiates_outputs
    (context : DirectAssertionContext) :
    instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionPendingTemplate = some context.pendingRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionLookupTemplate = some context.lookupRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionMachineTemplate = some context.machineRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionContextTemplate = some context.assertionContextRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionNormalControlTemplate = some context.normalControlRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionNormalLabelTemplate = some context.normalLabelRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          directAssertionReloadTemplate = some context.reloadRow ∧
      instantiateTemplateAtom? (assertionFinalSubst context)
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  cases context
  simp [assertionFinalSubst, assertionHeaderSubst, assertionMachineSubst,
    assertionHeapSubst, assertionLookupSubst, assertionPendingSubst,
    assertionSelfSubst, instantiateTemplateAtom?, templateCovered,
    templatesCovered, applySubst, applySubst.applySubstList, Subst.lookup,
    directAssertionPendingTemplate, directAssertionLookupTemplate,
    directAssertionMachineTemplate, directAssertionContextTemplate,
    directAssertionPCTemplate, directAssertionNextPCTemplate,
    directAssertionNormalControlTemplate, directAssertionNormalLabelTemplate,
    directAssertionReloadTemplate, DirectAssertionContext.pendingRow,
    DirectAssertionContext.lookupRow, DirectAssertionContext.machineRow,
    DirectAssertionContext.assertionContextRow,
    DirectAssertionContext.normalControlRow,
    DirectAssertionContext.normalLabelRow, DirectAssertionContext.reloadRow,
    DirectAssertionContext.pc, DirectAssertionContext.nextPC,
    DirectAssertionContext.bytes, DirectAssertionContext.code,
    CompressedIndexCode.atom, compressedIndexCodeAtom, natAtom]

/-- The independently constructed matcher assignment recovers every consumed
control and every output of the generated assertion-launch surface. -/
theorem canonical_assertion_slice_instantiates_launch
    (context : DirectAssertionContext) :
  ∃ substitution ∈ directAssertionSliceRows context,
    instantiateTemplateAtom? substitution directAssertionPendingTemplate =
        some context.pendingRow ∧
      instantiateTemplateAtom? substitution directAssertionLookupTemplate =
        some context.lookupRow ∧
      instantiateTemplateAtom? substitution directAssertionMachineTemplate =
        some context.machineRow ∧
      instantiateTemplateAtom? substitution directAssertionContextTemplate =
        some context.assertionContextRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalControlTemplate =
        some context.normalControlRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalLabelTemplate =
        some context.normalLabelRow ∧
      instantiateTemplateAtom? substitution directAssertionReloadTemplate =
        some context.reloadRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  exact ⟨assertionFinalSubst context,
    assertion_final_subst_in_slice context,
    assertion_final_subst_instantiates_outputs context⟩

section AxiomAudit

#print axioms speculative_direct_assertion_input_exact
#print axioms speculative_direct_assertion_sinks_exact
#print axioms canonical_assertion_slice_instantiates_launch

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
