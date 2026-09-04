import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Symbolic compressed-assertion rejoin

The normal assertion machine returns one formula at an occurrence-indexed
normal stack cell.  This module matches that boundary symbolically and proves
that the authored rejoin directive publishes the corresponding compact node
without evaluating a closed verifier program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private theorem groundAtom_cmatchAtom_self
    (substitution : Subst) (atom : Atom)
    (ground : isGroundAtom atom = true) :
    Conformance.Computable.cmatchAtom substitution atom atom =
      some substitution := by
  match atom with
  | .var name => simp [isGroundAtom] at ground
  | .symbol _ => simp [Conformance.Computable.cmatchAtom]
  | .grounded _ => simp [Conformance.Computable.cmatchAtom]
  | .expression atoms =>
      simp only [Conformance.Computable.cmatchAtom]
      have listGround : isGroundAtom.isGroundList atoms = true := by
        simpa only [isGroundAtom] using ground
      exact groundList_cmatchAtomList_self substitution atoms listGround
where
  groundList_cmatchAtomList_self
      (substitution : Subst) (atoms : List Atom)
      (ground : isGroundAtom.isGroundList atoms = true) :
      Conformance.Computable.cmatchAtomList substitution atoms atoms =
        some substitution := by
    match atoms with
    | [] => simp [Conformance.Computable.cmatchAtomList]
    | atom :: atoms =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [Conformance.Computable.cmatchAtomList]
        rw [groundAtom_cmatchAtom_self substitution atom ground.1]
        exact groundList_cmatchAtomList_self substitution atoms ground.2

@[simp] private theorem stringAtom_cmatchAtom_self
    (substitution : Subst) (value : String) :
    Conformance.Computable.cmatchAtom substitution (stringAtom value)
      (stringAtom value) = some substitution :=
  groundAtom_cmatchAtom_self substitution (stringAtom value)
    (isGroundAtom_stringAtom value)

/-! ## Exact authored rule interface -/

def rejoinSelfTemplate : Atom :=
  .expression
    [.symbol "exec", compressedAssertionRejoinDirective.loc,
      .var "assertion-rejoin-input", .var "assertion-rejoin-output"]

def rejoinPCTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", .var "word-position",
      .var "remaining-bytes", .var "compressed-index"]

def rejoinNextPCTemplate : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", rejoinPCTemplate]

def rejoinContextTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      rejoinPCTemplate, rejoinNextPCTemplate, .var "assertion-label",
      .var "heap-next", .var "node-next"]

def rejoinReturnedControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope-owner", .var "proof-owner",
      rejoinNextPCTemplate, .var "next-stack-position"]

def rejoinOccurrenceTemplate : Atom :=
  compressedAssertionOccurrenceSurface rejoinPCTemplate
    (.var "assertion-label")

def rejoinReturnedStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof-owner", .var "stack-base",
      .var "result-formula", rejoinOccurrenceTemplate]

def rejoinNormalStackSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof-owner", .var "stack-base",
      .var "next-stack-position"]

def rejoinNodeSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-node-owner", .var "proof-owner"],
      .var "node-next", .var "next-node"]

def rejoinNormalLabelTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      .var "proof-owner", rejoinPCTemplate, rejoinNextPCTemplate,
      .var "assertion-label"]

def rejoinResumeCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol "assertion-resume",
      .var "compressed-assertion-resume-rule"]

def rejoinReturnedMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "next-node",
      .var "next-stack-position"]

def rejoinResultNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-next",
      .var "result-formula", rejoinOccurrenceTemplate]

def rejoinResultStackTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-base", .var "node-next"]

def rejoinResumeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-resume", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes"]

def rejoinPatterns : List Atom :=
  [rejoinSelfTemplate, rejoinContextTemplate,
   rejoinReturnedControlTemplate, rejoinReturnedStackTemplate,
   rejoinNormalStackSuccessorTemplate, rejoinNodeSuccessorTemplate,
   rejoinNormalLabelTemplate, rejoinResumeCaptureTemplate]

def rejoinSinks : List Sink :=
  [.remove rejoinContextTemplate,
   .remove rejoinReturnedControlTemplate,
   .remove rejoinNormalLabelTemplate,
   .add rejoinReturnedMachineTemplate,
   .add rejoinResultNodeTemplate,
   .add rejoinResultStackTemplate,
   .add rejoinResumeTemplate,
   .add (.var "compressed-assertion-resume-rule")]

theorem compressedAssertionRejoin_input_exact :
    compressedAssertionRejoinDirective.rule.input =
      .compat (mkPattern rejoinPatterns) := by
  rfl

theorem compressedAssertionRejoin_sinks_exact :
    compressedAssertionRejoinDirective.rule.tmpl.sinks = rejoinSinks := by
  rfl

/-! ## Source-indexed rejoin context -/

structure RejoinContext where
  scopeOwner : Atom
  proofOwner : Atom
  wordPosition : Nat
  remainingBytes : List UInt8
  index : Nat
  heapNext : Nat
  nodeNext : Nat
  stackBase : Nat
  assertionLabel : String
  resultFormula : Atom

namespace RejoinContext

def code (_context : RejoinContext) (value : Nat) : Atom :=
  (CompressedIndexCode.ofNat value).atom

def bytes (context : RejoinContext) : Atom :=
  listAtom natAtom (context.remainingBytes.map UInt8.toNat)

def pc (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", natAtom context.wordPosition,
      context.bytes, context.code context.index]

def nextPC (context : RejoinContext) : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", context.pc]

def occurrence (context : RejoinContext) : Atom :=
  compressedAssertionOccurrenceSurface context.pc
    (stringAtom context.assertionLabel)

def contextRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", context.scopeOwner,
      context.proofOwner, natAtom context.wordPosition, context.bytes,
      context.pc, context.nextPC, stringAtom context.assertionLabel,
      context.code context.heapNext, context.code context.nodeNext]

def returnedControlRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-normal-control", context.scopeOwner, context.proofOwner,
      context.nextPC, context.code (context.stackBase + 1)]

def returnedStackRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-stack-cell", context.proofOwner,
      context.code context.stackBase, context.resultFormula,
      context.occurrence]

def normalStackSuccessorRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-index-successor", context.proofOwner,
      context.code context.stackBase,
      context.code (context.stackBase + 1)]

def nodeSuccessorRow (context : RejoinContext) : Atom :=
  compressedIndexSuccessorRow (compressedNodeOwner context.proofOwner)
    (context.code context.nodeNext) (context.code (context.nodeNext + 1))

def normalLabelRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      context.proofOwner, context.pc, context.nextPC,
      stringAtom context.assertionLabel]

def resumeCaptureRow (_context : RejoinContext) : Atom :=
  compressedOwnedRuntimeRuleRow "assertion-resume"
    compressedAssertionResumeRule

def returnedMachineRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", context.scopeOwner,
      context.proofOwner, context.code context.heapNext,
      context.code (context.nodeNext + 1),
      context.code (context.stackBase + 1)]

def resultNodeRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-node", context.proofOwner,
      context.code context.nodeNext, context.resultFormula,
      context.occurrence]

def resultStackRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", context.proofOwner,
      context.code context.stackBase, context.code context.nodeNext]

def resumeRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-resume", context.scopeOwner,
      context.proofOwner, natAtom context.wordPosition, context.bytes]

def matchSlice (context : RejoinContext) : List Atom :=
  [compressedAssertionRejoinDirective.atom, context.contextRow,
   context.returnedControlRow, context.returnedStackRow,
   context.normalStackSuccessorRow, context.nodeSuccessorRow,
   context.normalLabelRow, context.resumeCaptureRow]

def rows (context : RejoinContext) : List Subst :=
  (Conformance.Computable.cmatchInputSpec [] context.matchSlice
      compressedAssertionRejoinDirective.rule.input).map Prod.fst

def outputRows (context : RejoinContext) : List Atom :=
  [context.returnedMachineRow, context.resultNodeRow,
   context.resultStackRow, context.resumeRow,
   compressedAssertionResumeRule]

end RejoinContext

/-! ## Exact symbolic matcher -/

private def rejoinSelfInput : Atom :=
  match compressedAssertionRejoinDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-rejoin-input"

private def rejoinSelfOutput : Atom :=
  match compressedAssertionRejoinDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-rejoin-output"

private def rejoinSelfSubst : Subst :=
  [("assertion-rejoin-output", rejoinSelfOutput),
   ("assertion-rejoin-input", rejoinSelfInput)]

private def rejoinContextSubst (context : RejoinContext) : Subst :=
  [("node-next", context.code context.nodeNext),
   ("heap-next", context.code context.heapNext),
   ("assertion-label", stringAtom context.assertionLabel),
   ("compressed-index", context.code context.index),
   ("remaining-bytes", context.bytes),
   ("word-position", natAtom context.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ rejoinSelfSubst

private def rejoinControlSubst (context : RejoinContext) : Subst :=
  [("next-stack-position", context.code (context.stackBase + 1))] ++
    rejoinContextSubst context

private def rejoinStackSubst (context : RejoinContext) : Subst :=
  [("result-formula", context.resultFormula),
   ("stack-base", context.code context.stackBase)] ++
    rejoinControlSubst context

private def rejoinNodeSubst (context : RejoinContext) : Subst :=
  [("next-node", context.code (context.nodeNext + 1))] ++
    rejoinStackSubst context

private def rejoinFinalSubst (context : RejoinContext) : Subst :=
  [("compressed-assertion-resume-rule", compressedAssertionResumeRule)] ++
    rejoinNodeSubst context

private theorem rejoinSelf_match :
    Conformance.Computable.cmatchAtom [] rejoinSelfTemplate
      compressedAssertionRejoinDirective.atom = some rejoinSelfSubst := by
  decide +kernel

private theorem rejoinContext_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom rejoinSelfSubst rejoinContextTemplate
      context.contextRow = some (rejoinContextSubst context) := by
  cases context
  simp [rejoinContextSubst, rejoinSelfSubst, RejoinContext.contextRow,
    RejoinContext.pc, RejoinContext.nextPC, RejoinContext.bytes,
    RejoinContext.code, rejoinContextTemplate, rejoinPCTemplate,
    rejoinNextPCTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinControl_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinContextSubst context)
      rejoinReturnedControlTemplate context.returnedControlRow =
        some (rejoinControlSubst context) := by
  cases context
  simp [rejoinControlSubst, rejoinContextSubst, rejoinSelfSubst,
    RejoinContext.returnedControlRow, RejoinContext.pc,
    RejoinContext.nextPC, RejoinContext.bytes, RejoinContext.code,
    rejoinReturnedControlTemplate, rejoinPCTemplate, rejoinNextPCTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinStack_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinControlSubst context)
      rejoinReturnedStackTemplate context.returnedStackRow =
        some (rejoinStackSubst context) := by
  cases context
  simp [rejoinStackSubst, rejoinControlSubst, rejoinContextSubst,
    rejoinSelfSubst, RejoinContext.returnedStackRow,
    RejoinContext.occurrence, RejoinContext.pc, RejoinContext.bytes,
    RejoinContext.code, rejoinReturnedStackTemplate,
    rejoinOccurrenceTemplate, rejoinPCTemplate,
    compressedAssertionOccurrenceSurface,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinNormalSuccessor_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinStackSubst context)
      rejoinNormalStackSuccessorTemplate context.normalStackSuccessorRow =
        some (rejoinStackSubst context) := by
  cases context
  simp [rejoinStackSubst, rejoinControlSubst, rejoinContextSubst,
    rejoinSelfSubst, RejoinContext.normalStackSuccessorRow,
    RejoinContext.code, rejoinNormalStackSuccessorTemplate,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinNodeSuccessor_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinStackSubst context)
      rejoinNodeSuccessorTemplate context.nodeSuccessorRow =
        some (rejoinNodeSubst context) := by
  cases context
  simp [rejoinNodeSubst, rejoinStackSubst, rejoinControlSubst,
    rejoinContextSubst, rejoinSelfSubst, RejoinContext.nodeSuccessorRow,
    RejoinContext.code, rejoinNodeSuccessorTemplate,
    compressedIndexSuccessorRow, compressedNodeOwner,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinLabel_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinNodeSubst context)
      rejoinNormalLabelTemplate context.normalLabelRow =
        some (rejoinNodeSubst context) := by
  cases context
  simp [rejoinNodeSubst, rejoinStackSubst, rejoinControlSubst,
    rejoinContextSubst, rejoinSelfSubst, RejoinContext.normalLabelRow,
    RejoinContext.pc, RejoinContext.nextPC, RejoinContext.bytes,
    RejoinContext.code, rejoinNormalLabelTemplate, rejoinPCTemplate,
    rejoinNextPCTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem rejoinResume_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (rejoinNodeSubst context)
      rejoinResumeCaptureTemplate context.resumeCaptureRow =
        some (rejoinFinalSubst context) := by
  cases context
  simp [rejoinFinalSubst, rejoinNodeSubst, rejoinStackSubst,
    rejoinControlSubst, rejoinContextSubst, rejoinSelfSubst,
    RejoinContext.resumeCaptureRow, rejoinResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow,
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

private def canonicalRejoinConsumed (context : RejoinContext) : List Atom :=
  [context.resumeCaptureRow, context.normalLabelRow,
   context.nodeSuccessorRow, context.normalStackSuccessorRow,
   context.returnedStackRow, context.returnedControlRow,
   context.contextRow, compressedAssertionRejoinDirective.atom]

private theorem rejoin_final_subst_in_rows (context : RejoinContext) :
    rejoinFinalSubst context ∈ context.rows := by
  unfold RejoinContext.rows
  rw [compressedAssertionRejoin_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(rejoinFinalSubst context, canonicalRejoinConsumed context), ?_, rfl⟩
  unfold rejoinPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedAssertionRejoinDirective.atom)
  · simp [RejoinContext.matchSlice]
  · exact rejoinSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.contextRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinContext_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.returnedControlRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinControl_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.returnedStackRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinStack_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.normalStackSuccessorRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinNormalSuccessor_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.nodeSuccessorRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinNodeSuccessor_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.normalLabelRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinLabel_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.resumeCaptureRow)
  · simp [RejoinContext.matchSlice]
  · exact rejoinResume_match context
  simp [Conformance.Computable.cmatchPattern.go, canonicalRejoinConsumed]

private theorem rejoin_final_subst_instantiates_outputs
    (context : RejoinContext) :
    instantiateTemplateAtom? (rejoinFinalSubst context)
          rejoinReturnedMachineTemplate = some context.returnedMachineRow ∧
      instantiateTemplateAtom? (rejoinFinalSubst context)
          rejoinResultNodeTemplate = some context.resultNodeRow ∧
      instantiateTemplateAtom? (rejoinFinalSubst context)
          rejoinResultStackTemplate = some context.resultStackRow ∧
      instantiateTemplateAtom? (rejoinFinalSubst context)
          rejoinResumeTemplate = some context.resumeRow ∧
      instantiateTemplateAtom? (rejoinFinalSubst context)
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule := by
  cases context
  simp [rejoinFinalSubst, rejoinNodeSubst, rejoinStackSubst,
    rejoinControlSubst, rejoinContextSubst, rejoinSelfSubst,
    instantiateTemplateAtom?, templateCovered, templatesCovered,
    applySubst, applySubst.applySubstList, Subst.lookup,
    rejoinReturnedMachineTemplate, rejoinResultNodeTemplate,
    rejoinResultStackTemplate, rejoinResumeTemplate,
    rejoinOccurrenceTemplate, rejoinPCTemplate,
    RejoinContext.returnedMachineRow, RejoinContext.resultNodeRow,
    RejoinContext.resultStackRow, RejoinContext.resumeRow,
    RejoinContext.occurrence, RejoinContext.pc, RejoinContext.bytes,
    RejoinContext.code, compressedAssertionOccurrenceSurface,
    CompressedIndexCode.atom, compressedIndexCodeAtom, natAtom]

/-- One source-derived substitution witnesses the complete rejoin output. -/
theorem canonical_rejoin_slice_instantiates_outputs
    (context : RejoinContext) :
  ∃ substitution ∈ context.rows,
    instantiateTemplateAtom? substitution rejoinReturnedMachineTemplate =
        some context.returnedMachineRow ∧
      instantiateTemplateAtom? substitution rejoinResultNodeTemplate =
        some context.resultNodeRow ∧
      instantiateTemplateAtom? substitution rejoinResultStackTemplate =
        some context.resultStackRow ∧
      instantiateTemplateAtom? substitution rejoinResumeTemplate =
        some context.resumeRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule := by
  exact ⟨rejoinFinalSubst context, rejoin_final_subst_in_rows context,
    rejoin_final_subst_instantiates_outputs context⟩

/-! ## Complete reflective firing boundary -/

/-- Exact matcher evidence for one assertion rejoin in an arbitrary larger
execution space.  The witness is produced by the actual reflective matcher;
the proposition does not carry a reconstructed target state. -/
def ExactCompressedAssertionRejoin (context : RejoinContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input).map Prod.fst,
    instantiateTemplateAtom? substitution rejoinReturnedMachineTemplate =
        some context.returnedMachineRow ∧
      instantiateTemplateAtom? substitution rejoinResultNodeTemplate =
        some context.resultNodeRow ∧
      instantiateTemplateAtom? substitution rejoinResultStackTemplate =
        some context.resultStackRow ∧
      instantiateTemplateAtom? substitution rejoinResumeTemplate =
        some context.resumeRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule

/-- Any live frame containing the exact source-derived rejoin rows supplies
the same matcher witness as the canonical slice.  This is the frame seam used
to connect an actual normal-result firing to the compact continuation. -/
theorem exact_compressed_assertion_rejoin_of_live_rows
    (context : RejoinContext) (space : List Atom)
    (contextRow : context.contextRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (returnedControl : context.returnedControlRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (returnedStack : context.returnedStackRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (normalSuccessor : context.normalStackSuccessorRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (nodeSuccessor : context.nodeSuccessorRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (normalLabel : context.normalLabelRow ∈
      space.erase compressedAssertionRejoinDirective.atom)
    (resumeCapture : context.resumeCaptureRow ∈
      space.erase compressedAssertionRejoinDirective.atom) :
    ExactCompressedAssertionRejoin context space := by
  refine ⟨rejoinFinalSubst context, ?_,
    rejoin_final_subst_instantiates_outputs context⟩
  rw [compressedAssertionRejoin_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(rejoinFinalSubst context, canonicalRejoinConsumed context), ?_, rfl⟩
  unfold rejoinPatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedAssertionRejoinDirective.atom)
  · simp
  · exact rejoinSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.contextRow)
  · exact List.mem_cons_of_mem _ contextRow
  · exact rejoinContext_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.returnedControlRow)
  · exact List.mem_cons_of_mem _ returnedControl
  · exact rejoinControl_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.returnedStackRow)
  · exact List.mem_cons_of_mem _ returnedStack
  · exact rejoinStack_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.normalStackSuccessorRow)
  · exact List.mem_cons_of_mem _ normalSuccessor
  · exact rejoinNormalSuccessor_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.nodeSuccessorRow)
  · exact List.mem_cons_of_mem _ nodeSuccessor
  · exact rejoinNodeSuccessor_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.normalLabelRow)
  · exact List.mem_cons_of_mem _ normalLabel
  · exact rejoinLabel_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.resumeCaptureRow)
  · exact List.mem_cons_of_mem _ resumeCapture
  · exact rejoinResume_match context
  simp [Conformance.Computable.cmatchPattern.go, canonicalRejoinConsumed]

private theorem canonical_rejoin_full_read (context : RejoinContext) :
    compressedAssertionRejoinDirective.atom ::
        context.matchSlice.erase compressedAssertionRejoinDirective.atom =
      context.matchSlice := by
  unfold RejoinContext.matchSlice
  rw [List.erase_cons_head]

/-- The canonical source-indexed rejoin slice supplies exact matcher evidence
for the actual reflective executor. -/
theorem canonical_exact_compressed_assertion_rejoin
    (context : RejoinContext) :
    ExactCompressedAssertionRejoin context context.matchSlice := by
  rcases canonical_rejoin_slice_instantiates_outputs context with
    ⟨substitution, rowMember, outputs⟩
  refine ⟨substitution, ?_, outputs⟩
  rw [canonical_rejoin_full_read]
  exact rowMember

private theorem rejoinSinks_machine_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate] ++
      .add rejoinReturnedMachineTemplate ::
        [.add rejoinResultNodeTemplate,
         .add rejoinResultStackTemplate,
         .add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_node_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate] ++
      .add rejoinResultNodeTemplate ::
        [.add rejoinResultStackTemplate,
         .add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_stack_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate] ++
      .add rejoinResultStackTemplate ::
        [.add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_resume_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate] ++
      .add rejoinResumeTemplate ::
        [.add (.var "compressed-assertion-resume-rule")] := by
  rfl

/-- Every exact rejoin match publishes the complete compact successor
interface through one actual reflective MM2 firing. -/
theorem compressed_assertion_rejoin_fire_adds_output_rows
    (context : RejoinContext) (space : List Atom)
    (matched : ExactCompressedAssertionRejoin context space) :
    ∀ row ∈ context.outputRows,
      row ∈ cFireReflectiveSourceExecFact space
        compressedAssertionRejoinDirective := by
  intro row member
  rcases matched with
    ⟨substitution, rowMember, returnedMachine, resultNode, resultStack,
      resume, resumeRule⟩
  simp only [RejoinContext.outputRows, List.mem_cons, List.not_mem_nil,
    or_false] at member
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedAssertionRejoin_sinks_exact]
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [rejoinSinks_machine_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember returnedMachine (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [rejoinSinks_node_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember resultNode (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [rejoinSinks_stack_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember resultStack (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [rejoinSinks_resume_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember resume (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact ⟨_, rfl⟩)
  · exact mem_cApplyReflectiveSinkBatch_append_add_of_row _ _
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate,
       .add rejoinResumeTemplate]
      (.var "compressed-assertion-resume-rule")
      compressedAssertionResumeRule substitution rowMember resumeRule

/-- Rejoin keeps the normal stack view used by later synchronized assertion
steps. -/
theorem compressed_assertion_rejoin_fire_preserves_returned_stack
    (context : RejoinContext) (space : List Atom)
    (present : context.returnedStackRow ∈
      space.erase compressedAssertionRejoinDirective.atom) :
    context.returnedStackRow ∈
      cFireReflectiveSourceExecFact space
        compressedAssertionRejoinDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  apply compressedAssertionRejoin_preserves_normal_stack_row
  exact present

/-- Rejoin preserves every existing expression whose head differs from its
three consumed interface rows. -/
theorem compressed_assertion_rejoin_fire_preserves_expression_head
    (space : List Atom) (candidateHead : String) (candidateTail : List Atom)
    (notContext : "mm-compressed-assertion-context" ≠ candidateHead)
    (notControl : "mm-normal-control" ≠ candidateHead)
    (notLabel : "mm-linked-row" ≠ candidateHead)
    (present : .expression (.symbol candidateHead :: candidateTail) ∈
      space.erase compressedAssertionRejoinDirective.atom) :
    .expression (.symbol candidateHead :: candidateTail) ∈
      cFireReflectiveSourceExecFact space
        compressedAssertionRejoinDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedAssertionRejoin_sinks_exact]
  apply mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
  · intro sink member
    simp only [rejoinSinks, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨rejoinContextTemplate, rfl, by
        intro substitution _rowMember
        exact instantiateTemplateAtom?_expression_symbol_head_ne substitution
          "mm-compressed-assertion-context" candidateHead _ _ notContext⟩
    · exact Or.inr ⟨rejoinReturnedControlTemplate, rfl, by
        intro substitution _rowMember
        exact instantiateTemplateAtom?_expression_symbol_head_ne substitution
          "mm-normal-control" candidateHead _ _ notControl⟩
    · exact Or.inr ⟨rejoinNormalLabelTemplate, rfl, by
        intro substitution _rowMember
        exact instantiateTemplateAtom?_expression_symbol_head_ne substitution
          "mm-linked-row" candidateHead _ _ notLabel⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  · exact present

/-- The canonical rejoin slice performs the full concrete compact handoff. -/
theorem canonical_rejoin_fire_adds_output_rows
    (context : RejoinContext) :
    ∀ row ∈ context.outputRows,
      row ∈ cFireReflectiveSourceExecFact context.matchSlice
        compressedAssertionRejoinDirective :=
  compressed_assertion_rejoin_fire_adds_output_rows context context.matchSlice
    (canonical_exact_compressed_assertion_rejoin context)

/-- The canonical rejoin slice retains the returned normal stack row. -/
theorem canonical_rejoin_fire_preserves_returned_stack
    (context : RejoinContext) :
    context.returnedStackRow ∈
      cFireReflectiveSourceExecFact context.matchSlice
        compressedAssertionRejoinDirective := by
  apply compressed_assertion_rejoin_fire_preserves_returned_stack
  unfold RejoinContext.matchSlice
  rw [List.erase_cons_head]
  simp

section AxiomAudit

#print axioms compressedAssertionRejoin_input_exact
#print axioms compressedAssertionRejoin_sinks_exact
#print axioms canonical_rejoin_slice_instantiates_outputs
#print axioms canonical_exact_compressed_assertion_rejoin
#print axioms exact_compressed_assertion_rejoin_of_live_rows
#print axioms compressed_assertion_rejoin_fire_adds_output_rows
#print axioms compressed_assertion_rejoin_fire_preserves_returned_stack
#print axioms compressed_assertion_rejoin_fire_preserves_expression_head
#print axioms canonical_rejoin_fire_adds_output_rows
#print axioms canonical_rejoin_fire_preserves_returned_stack

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
