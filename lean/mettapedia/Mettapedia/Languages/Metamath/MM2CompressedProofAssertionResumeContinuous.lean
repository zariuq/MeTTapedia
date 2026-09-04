import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Continuous compressed-assertion resume

After the shared normal assertion machine returns and the compact state is
rejoined, this transition reinstalls the incremental scanner.  The matcher is
proved against the exact verifier-owned capture rows, then transported into an
arbitrary larger execution frame.  No scanner rule is taken from proof data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Exact public resume interface -/

def assertionResumeSelfTemplate : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "34",
      .symbol "mm-compressed-assertion-resume"],
      .var "assertion-resume-input", .var "assertion-resume-output"]

def assertionResumeRequestTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-resume", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes"]

def assertionResumedScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .symbol "mm-compressed-just-completed-step", listAtom natAtom []]

def assertionResumeCaptureTemplate (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

def assertionResumePatterns : List Atom :=
  [assertionResumeSelfTemplate, assertionResumeRequestTemplate,
   assertionResumeCaptureTemplate "prefix" "compressed-prefix-rule",
   assertionResumeCaptureTemplate "terminal" "compressed-terminal-rule",
   assertionResumeCaptureTemplate "proof" "compressed-proof-rule",
   assertionResumeCaptureTemplate "assertion-launch"
     "compressed-assertion-launch-rule",
   assertionResumeCaptureTemplate "save" "compressed-save-rule",
   assertionResumeCaptureTemplate "word-advance"
     "compressed-word-advance-rule",
   assertionResumeCaptureTemplate "accept" "compressed-accept-rule",
   assertionResumeCaptureTemplate "incomplete" "compressed-incomplete-rule",
   assertionResumeCaptureTemplate "invalid-byte"
     "compressed-invalid-byte-rule",
   assertionResumeCaptureTemplate "question" "compressed-question-rule",
   assertionResumeCaptureTemplate "question-open-fault"
     "compressed-question-open-fault-rule",
   assertionResumeCaptureTemplate "save-fault" "compressed-save-fault-rule"]

def assertionResumeOutputTemplates : List Atom :=
  [assertionResumedScanTemplate,
   .var "compressed-prefix-rule",
   .var "compressed-terminal-rule",
   .var "compressed-proof-rule",
   .var "compressed-assertion-launch-rule",
   .var "compressed-save-rule",
   .var "compressed-word-advance-rule",
   .var "compressed-accept-rule",
   .var "compressed-incomplete-rule",
   .var "compressed-invalid-byte-rule",
   .var "compressed-question-rule",
   .var "compressed-question-open-fault-rule",
   .var "compressed-save-fault-rule"]

def assertionResumeSinks : List Sink :=
  .remove assertionResumeRequestTemplate ::
    assertionResumeOutputTemplates.map Sink.add

theorem compressedAssertionResume_input_exact :
    compressedAssertionResumeDirective.rule.input =
      .compat (mkPattern assertionResumePatterns) := by
  decide +kernel

theorem compressedAssertionResume_sinks_exact :
    compressedAssertionResumeDirective.rule.tmpl.sinks =
      assertionResumeSinks := by
  decide +kernel

/-! ## Source-indexed resume carrier -/

def requiredResumeCaptureRows (_context : RejoinContext) : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "assertion-launch"
     compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "save" compressedSaveRule,
   compressedOwnedRuntimeRuleRow "word-advance" compressedWordAdvanceRule,
   compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule,
   compressedOwnedRuntimeRuleRow "incomplete" compressedIncompleteRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     compressedQuestionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "save-fault" compressedSaveFaultRule]

def resumeMatchSlice (context : RejoinContext) : List Atom :=
  compressedAssertionResumeDirective.atom ::
    context.resumeRow :: requiredResumeCaptureRows context

def resumedScanRow (context : RejoinContext) : Atom :=
  .expression
    [.symbol "mm-compressed-scan", context.scopeOwner, context.proofOwner,
      natAtom context.wordPosition, context.bytes,
      .symbol "mm-compressed-just-completed-step", listAtom natAtom []]

def resumeOutputRows (context : RejoinContext) : List Atom :=
  [resumedScanRow context,
   compressedPrefixRule,
   compressedTerminalRule,
   compressedProofStepRule,
   compressedAssertionLaunchRule,
   compressedSaveRule,
   compressedWordAdvanceRule,
   compressedAcceptRule,
   compressedIncompleteRule,
   compressedInvalidByteRule,
   compressedQuestionRule,
   compressedQuestionOpenFaultRule,
   compressedSaveFaultRule]

/-! ## Presentation-relative runtime inventory -/

/-- Resume input reconstructed from a selected verifier runtime inventory. -/
def resumeMatchSliceFor (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : List Atom :=
  compressedAssertionResumeDirective.atom :: context.resumeRow ::
    rules.captureRows

/-- Resume output reconstructed from the same selected verifier runtime
inventory.  This is the representation-preserving form used after a verifier
transformation changes a continuation payload. -/
def resumeOutputRowsFor (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : List Atom :=
  resumedScanRow context :: rules.payloadRows

@[simp] theorem resumeMatchSliceFor_base
    (context : RejoinContext) :
    resumeMatchSliceFor baseScannerRuntimeRuleBundle context =
      resumeMatchSlice context := by
  rfl

@[simp] theorem resumeOutputRowsFor_base
    (context : RejoinContext) :
    resumeOutputRowsFor baseScannerRuntimeRuleBundle context =
      resumeOutputRows context := by
  rfl

/-- The transformed resume path retains the compiler-selected terminal rule
instead of reverting to the base terminal continuation. -/
theorem speculative_terminal_mem_resume_output
    (context : RejoinContext) :
    MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule ∈
      resumeOutputRowsFor speculativeScannerRuntimeRuleBundle context := by
  simp [resumeOutputRowsFor, ScannerRuntimeRuleBundle.payloadRows,
    speculativeScannerRuntimeRuleBundle]

/-- Negative control: the retired base terminal is absent from the
transformed resume inventory. -/
theorem base_terminal_not_mem_speculative_resume_output
    (context : RejoinContext) :
    compressedTerminalRule ∉
      resumeOutputRowsFor speculativeScannerRuntimeRuleBundle context := by
  intro member
  simp only [resumeOutputRowsFor, List.mem_cons] at member
  rcases member with equal | payloadMember
  · simp [resumedScanRow, compressedTerminalRule] at equal
  · exact base_terminal_not_mem_speculative_payload payloadMember

def resumeRowsFor (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (resumeMatchSliceFor rules context)
      compressedAssertionResumeDirective.rule.input).map Prod.fst

def resumeRows (context : RejoinContext) : List Subst :=
  resumeRowsFor baseScannerRuntimeRuleBundle context

/-! ## Exact symbolic matcher -/

private def resumeSelfInput : Atom :=
  match compressedAssertionResumeDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-resume-input"

private def resumeSelfOutput : Atom :=
  match compressedAssertionResumeDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-resume-output"

private def resumeSelfSubst : Subst :=
  [("assertion-resume-output", resumeSelfOutput),
   ("assertion-resume-input", resumeSelfInput)]

private def resumeRequestSubst (context : RejoinContext) : Subst :=
  [("remaining-bytes", context.bytes),
   ("word-position", natAtom context.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ resumeSelfSubst

private def resumePrefixSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-prefix-rule", rules.saveCore.prefixRule) ::
    resumeRequestSubst context

private def resumeTerminalSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-terminal-rule", rules.saveCore.terminalRule) ::
    resumePrefixSubst rules context

private def resumeProofSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-proof-rule", rules.saveCore.proofRule) ::
    resumeTerminalSubst rules context

private def resumeLaunchSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-assertion-launch-rule", rules.assertionLaunchRule) ::
    resumeProofSubst rules context

private def resumeSaveSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-save-rule", rules.saveRule) :: resumeLaunchSubst rules context

private def resumeWordAdvanceSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-word-advance-rule", rules.wordAdvanceRule) ::
    resumeSaveSubst rules context

private def resumeAcceptSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-accept-rule", rules.acceptRule) ::
    resumeWordAdvanceSubst rules context

private def resumeIncompleteSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-incomplete-rule", rules.incompleteRule) ::
    resumeAcceptSubst rules context

private def resumeInvalidByteSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-invalid-byte-rule", rules.saveCore.invalidByteRule) ::
    resumeIncompleteSubst rules context

private def resumeQuestionSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-question-rule", rules.saveCore.questionRule) ::
    resumeInvalidByteSubst rules context

private def resumeQuestionOpenFaultSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-question-open-fault-rule",
      rules.saveCore.questionOpenFaultRule) ::
    resumeQuestionSubst rules context

private def resumeFinalSubst (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : Subst :=
  ("compressed-save-fault-rule", rules.saveFaultRule) ::
    resumeQuestionOpenFaultSubst rules context

private theorem resumeSelf_match :
    Conformance.Computable.cmatchAtom [] assertionResumeSelfTemplate
      compressedAssertionResumeDirective.atom = some resumeSelfSubst := by
  decide +kernel

private theorem resumeRequest_match (context : RejoinContext) :
    Conformance.Computable.cmatchAtom resumeSelfSubst
      assertionResumeRequestTemplate context.resumeRow =
        some (resumeRequestSubst context) := by
  cases context
  simp [resumeRequestSubst, resumeSelfSubst,
    assertionResumeRequestTemplate, RejoinContext.resumeRow,
    RejoinContext.bytes, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumePrefix_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeRequestSubst context)
      (assertionResumeCaptureTemplate "prefix" "compressed-prefix-rule")
      (compressedOwnedRuntimeRuleRow "prefix" rules.saveCore.prefixRule) =
        some (resumePrefixSubst rules context) := by
  cases context
  cases rules
  simp [resumePrefixSubst, resumeRequestSubst, resumeSelfSubst,
    assertionResumeCaptureTemplate, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeTerminal_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumePrefixSubst rules context)
      (assertionResumeCaptureTemplate "terminal" "compressed-terminal-rule")
      (compressedOwnedRuntimeRuleRow "terminal"
        rules.saveCore.terminalRule) =
        some (resumeTerminalSubst rules context) := by
  cases context
  cases rules
  simp [resumeTerminalSubst, resumePrefixSubst, resumeRequestSubst,
    resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeProof_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeTerminalSubst rules context)
      (assertionResumeCaptureTemplate "proof" "compressed-proof-rule")
      (compressedOwnedRuntimeRuleRow "proof" rules.saveCore.proofRule) =
        some (resumeProofSubst rules context) := by
  cases context
  cases rules
  simp [resumeProofSubst, resumeTerminalSubst, resumePrefixSubst,
    resumeRequestSubst, resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeLaunch_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeProofSubst rules context)
      (assertionResumeCaptureTemplate "assertion-launch"
        "compressed-assertion-launch-rule")
      (compressedOwnedRuntimeRuleRow "assertion-launch"
        rules.assertionLaunchRule) = some (resumeLaunchSubst rules context) := by
  cases context
  cases rules
  simp [resumeLaunchSubst, resumeProofSubst, resumeTerminalSubst,
    resumePrefixSubst, resumeRequestSubst, resumeSelfSubst,
    assertionResumeCaptureTemplate, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeSave_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeLaunchSubst rules context)
      (assertionResumeCaptureTemplate "save" "compressed-save-rule")
      (compressedOwnedRuntimeRuleRow "save" rules.saveRule) =
        some (resumeSaveSubst rules context) := by
  cases context
  cases rules
  simp [resumeSaveSubst, resumeLaunchSubst, resumeProofSubst,
    resumeTerminalSubst, resumePrefixSubst, resumeRequestSubst,
    resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeWordAdvance_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeSaveSubst rules context)
      (assertionResumeCaptureTemplate "word-advance"
        "compressed-word-advance-rule")
      (compressedOwnedRuntimeRuleRow "word-advance"
        rules.wordAdvanceRule) =
        some (resumeWordAdvanceSubst rules context) := by
  cases context
  cases rules
  simp [resumeWordAdvanceSubst, resumeSaveSubst, resumeLaunchSubst,
    resumeProofSubst, resumeTerminalSubst, resumePrefixSubst,
    resumeRequestSubst, resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeAccept_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom
      (resumeWordAdvanceSubst rules context)
      (assertionResumeCaptureTemplate "accept" "compressed-accept-rule")
      (compressedOwnedRuntimeRuleRow "accept" rules.acceptRule) =
        some (resumeAcceptSubst rules context) := by
  cases context
  cases rules
  simp [resumeAcceptSubst, resumeWordAdvanceSubst, resumeSaveSubst,
    resumeLaunchSubst, resumeProofSubst, resumeTerminalSubst,
    resumePrefixSubst, resumeRequestSubst, resumeSelfSubst,
    assertionResumeCaptureTemplate, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeIncomplete_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeAcceptSubst rules context)
      (assertionResumeCaptureTemplate "incomplete"
        "compressed-incomplete-rule")
      (compressedOwnedRuntimeRuleRow "incomplete" rules.incompleteRule) =
        some (resumeIncompleteSubst rules context) := by
  cases context
  cases rules
  simp [resumeIncompleteSubst, resumeAcceptSubst, resumeWordAdvanceSubst,
    resumeSaveSubst, resumeLaunchSubst, resumeProofSubst,
    resumeTerminalSubst, resumePrefixSubst, resumeRequestSubst,
    resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeInvalidByte_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeIncompleteSubst rules context)
      (assertionResumeCaptureTemplate "invalid-byte"
        "compressed-invalid-byte-rule")
      (compressedOwnedRuntimeRuleRow "invalid-byte"
        rules.saveCore.invalidByteRule) =
        some (resumeInvalidByteSubst rules context) := by
  cases context
  cases rules
  simp [resumeInvalidByteSubst, resumeIncompleteSubst, resumeAcceptSubst,
    resumeWordAdvanceSubst, resumeSaveSubst, resumeLaunchSubst,
    resumeProofSubst, resumeTerminalSubst, resumePrefixSubst,
    resumeRequestSubst, resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeQuestion_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeInvalidByteSubst rules context)
      (assertionResumeCaptureTemplate "question" "compressed-question-rule")
      (compressedOwnedRuntimeRuleRow "question"
        rules.saveCore.questionRule) =
        some (resumeQuestionSubst rules context) := by
  cases context
  cases rules
  simp [resumeQuestionSubst, resumeInvalidByteSubst,
    resumeIncompleteSubst, resumeAcceptSubst, resumeWordAdvanceSubst,
    resumeSaveSubst, resumeLaunchSubst, resumeProofSubst,
    resumeTerminalSubst, resumePrefixSubst, resumeRequestSubst,
    resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeQuestionOpenFault_match
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext) :
    Conformance.Computable.cmatchAtom (resumeQuestionSubst rules context)
      (assertionResumeCaptureTemplate "question-open-fault"
        "compressed-question-open-fault-rule")
      (compressedOwnedRuntimeRuleRow "question-open-fault"
        rules.saveCore.questionOpenFaultRule) =
          some (resumeQuestionOpenFaultSubst rules context) := by
  cases context
  cases rules
  simp [resumeQuestionOpenFaultSubst, resumeQuestionSubst,
    resumeInvalidByteSubst, resumeIncompleteSubst, resumeAcceptSubst,
    resumeWordAdvanceSubst, resumeSaveSubst, resumeLaunchSubst,
    resumeProofSubst, resumeTerminalSubst, resumePrefixSubst,
    resumeRequestSubst, resumeSelfSubst, assertionResumeCaptureTemplate,
    compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem resumeSaveFault_match (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) :
    Conformance.Computable.cmatchAtom
      (resumeQuestionOpenFaultSubst rules context)
      (assertionResumeCaptureTemplate "save-fault"
        "compressed-save-fault-rule")
      (compressedOwnedRuntimeRuleRow "save-fault" rules.saveFaultRule) =
        some (resumeFinalSubst rules context) := by
  cases context
  cases rules
  simp [resumeFinalSubst, resumeQuestionOpenFaultSubst,
    resumeQuestionSubst, resumeInvalidByteSubst, resumeIncompleteSubst,
    resumeAcceptSubst, resumeWordAdvanceSubst, resumeSaveSubst,
    resumeLaunchSubst, resumeProofSubst, resumeTerminalSubst,
    resumePrefixSubst, resumeRequestSubst, resumeSelfSubst,
    assertionResumeCaptureTemplate, compressedOwnedRuntimeRuleRow,
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

private def canonicalResumeConsumed (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext) : List Atom :=
  rules.captureRows.reverse ++
    [context.resumeRow, compressedAssertionResumeDirective.atom]

private theorem resume_final_subst_in_rows
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext) :
    resumeFinalSubst rules context ∈ resumeRowsFor rules context := by
  unfold resumeRowsFor
  rw [compressedAssertionResume_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(resumeFinalSubst rules context,
    canonicalResumeConsumed rules context), ?_, rfl⟩
  unfold assertionResumePatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedAssertionResumeDirective.atom)
  · simp [resumeMatchSliceFor]
  · exact resumeSelf_match
  apply cmatchPattern_go_cons_of_selected (concrete := context.resumeRow)
  · simp [resumeMatchSliceFor]
  · exact resumeRequest_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "prefix"
      rules.saveCore.prefixRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumePrefix_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "terminal"
      rules.saveCore.terminalRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeTerminal_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "proof"
      rules.saveCore.proofRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeProof_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "assertion-launch"
      rules.assertionLaunchRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeLaunch_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "save" rules.saveRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeSave_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "word-advance"
      rules.wordAdvanceRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeWordAdvance_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "accept" rules.acceptRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeAccept_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "incomplete"
      rules.incompleteRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeIncomplete_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "invalid-byte"
      rules.saveCore.invalidByteRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeInvalidByte_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question"
      rules.saveCore.questionRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeQuestion_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question-open-fault"
      rules.saveCore.questionOpenFaultRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeQuestionOpenFault_match rules context
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "save-fault"
      rules.saveFaultRule)
  · simp [resumeMatchSliceFor, ScannerRuntimeRuleBundle.captureRows]
  · exact resumeSaveFault_match rules context
  simp [Conformance.Computable.cmatchPattern.go, canonicalResumeConsumed,
    ScannerRuntimeRuleBundle.captureRows]

private theorem resume_final_subst_instantiates_outputs
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext) :
    List.Forall₂
      (fun authored concrete =>
        instantiateTemplateAtom? (resumeFinalSubst rules context) authored =
          some concrete)
      assertionResumeOutputTemplates (resumeOutputRowsFor rules context) := by
  cases context
  cases rules with
  | mk saveCore assertionLaunchRule saveRule wordAdvanceRule acceptRule
      incompleteRule saveFaultRule =>
      cases saveCore
      simp [assertionResumeOutputTemplates, resumeOutputRowsFor,
        ScannerRuntimeRuleBundle.payloadRows, resumedScanRow,
        assertionResumedScanTemplate, RejoinContext.bytes,
        resumeFinalSubst, resumeQuestionOpenFaultSubst,
        resumeQuestionSubst, resumeInvalidByteSubst,
        resumeIncompleteSubst, resumeAcceptSubst,
        resumeWordAdvanceSubst, resumeSaveSubst, resumeLaunchSubst,
        resumeProofSubst, resumeTerminalSubst, resumePrefixSubst,
        resumeRequestSubst, resumeSelfSubst, resumeSelfInput,
        resumeSelfOutput, instantiateTemplateAtom?,
        templateCovered, templatesCovered, applySubst,
        applySubst.applySubstList, Subst.lookup, listAtom]

private theorem canonical_resume_full_read
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext) :
    compressedAssertionResumeDirective.atom ::
        (resumeMatchSliceFor rules context).erase
          compressedAssertionResumeDirective.atom =
      resumeMatchSliceFor rules context := by
  unfold resumeMatchSliceFor
  rw [List.erase_cons_head]

/-- Presentation-relative exact matcher evidence for one assertion-resume step
in a larger frame.  Both capture rows and output payloads come from the same
runtime inventory. -/
def ExactCompressedAssertionResumeFor (rules : ScannerRuntimeRuleBundle)
    (context : RejoinContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (compressedAssertionResumeDirective.atom ::
          space.erase compressedAssertionResumeDirective.atom)
        compressedAssertionResumeDirective.rule.input).map Prod.fst,
    List.Forall₂
      (fun authored concrete =>
        instantiateTemplateAtom? substitution authored = some concrete)
      assertionResumeOutputTemplates (resumeOutputRowsFor rules context)

/-- Base-verifier specialization retained for existing clients. -/
def ExactCompressedAssertionResume (context : RejoinContext)
    (space : List Atom) : Prop :=
  ExactCompressedAssertionResumeFor baseScannerRuntimeRuleBundle context space

theorem canonical_exact_compressed_assertion_resume_for
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext) :
    ExactCompressedAssertionResumeFor rules context
      (resumeMatchSliceFor rules context) := by
  refine ⟨resumeFinalSubst rules context, ?_,
    resume_final_subst_instantiates_outputs rules context⟩
  rw [canonical_resume_full_read]
  change resumeFinalSubst rules context ∈ resumeRowsFor rules context
  exact resume_final_subst_in_rows rules context

theorem canonical_exact_compressed_assertion_resume
    (context : RejoinContext) :
    ExactCompressedAssertionResume context (resumeMatchSlice context) := by
  exact canonical_exact_compressed_assertion_resume_for
    baseScannerRuntimeRuleBundle context

/-- A larger frame containing every canonical resume row admits the same
source-derived matcher substitution. -/
theorem exact_compressed_assertion_resume_for_of_live_rows
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom)
    (included : ∀ row ∈ resumeMatchSliceFor rules context,
      row ∈ compressedAssertionResumeDirective.atom ::
        space.erase compressedAssertionResumeDirective.atom) :
    ExactCompressedAssertionResumeFor rules context space := by
  refine ⟨resumeFinalSubst rules context, ?_,
    resume_final_subst_instantiates_outputs rules context⟩
  rw [compressedAssertionResume_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec, List.mem_map]
  have canonicalMember :
      ∃ consumed,
        (resumeFinalSubst rules context, consumed) ∈
          Conformance.Computable.cmatchPattern []
            (resumeMatchSliceFor rules context)
            (mkPattern assertionResumePatterns) := by
    have member := resume_final_subst_in_rows rules context
    unfold resumeRowsFor at member
    rw [compressedAssertionResume_input_exact] at member
    simp only [Conformance.Computable.cmatchInputSpec, List.mem_map] at member
    rcases member with ⟨⟨same, consumed⟩, matched, equal⟩
    simp only at equal
    subst same
    exact ⟨consumed, matched⟩
  rcases canonicalMember with ⟨consumed, matched⟩
  refine ⟨(resumeFinalSubst rules context, consumed), ?_, rfl⟩
  exact Conformance.Computable.cmatchPattern_mono []
    (resumeMatchSliceFor rules context)
    (compressedAssertionResumeDirective.atom ::
      space.erase compressedAssertionResumeDirective.atom)
    (mkPattern assertionResumePatterns) included _ _ matched

theorem exact_compressed_assertion_resume_of_live_rows
    (context : RejoinContext) (space : List Atom)
    (included : ∀ row ∈ resumeMatchSlice context,
      row ∈ compressedAssertionResumeDirective.atom ::
        space.erase compressedAssertionResumeDirective.atom) :
    ExactCompressedAssertionResume context space := by
  exact exact_compressed_assertion_resume_for_of_live_rows
    baseScannerRuntimeRuleBundle context space included

/-! ## Actual reflective publication -/

/-- Every exact resume match publishes the scanner state and the complete
source-authenticated scanner rule inventory through the actual sink batch. -/
theorem compressed_assertion_resume_fire_adds_output_rows_for
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom)
    (matched : ExactCompressedAssertionResumeFor rules context space) :
    ∀ row ∈ resumeOutputRowsFor rules context,
      row ∈ cFireReflectiveSourceExecFact space
        compressedAssertionResumeDirective := by
  intro row member
  rcases matched with ⟨substitution, rowMember, outputs⟩
  simp only [assertionResumeOutputTemplates, resumeOutputRowsFor,
    ScannerRuntimeRuleBundle.payloadRows, List.forall₂_cons] at outputs
  rcases outputs with
    ⟨hScan, hPrefix, hTerminal, hProof, hLaunch, hSave, hWordAdvance,
      hAccept, hIncomplete, hInvalidByte, hQuestion, hQuestionOpenFault,
      hSaveFault, _outputsNil⟩
  simp only [resumeOutputRowsFor, ScannerRuntimeRuleBundle.payloadRows,
    List.mem_cons, List.not_mem_nil,
    or_false] at member
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedAssertionResume_sinks_exact]
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate]
        assertionResumedScanTemplate (resumedScanRow context)
        (assertionResumeOutputTemplates.tail.map Sink.add)
        substitution rowMember hScan (by
          intro sink sinkMember
          simp only [List.mem_map] at sinkMember
          rcases sinkMember with ⟨authored, _member, rfl⟩
          exact ⟨authored, rfl⟩))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate]
        (.var "compressed-prefix-rule") rules.saveCore.prefixRule
        [.add (.var "compressed-terminal-rule"),
         .add (.var "compressed-proof-rule"),
         .add (.var "compressed-assertion-launch-rule"),
         .add (.var "compressed-save-rule"),
         .add (.var "compressed-word-advance-rule"),
         .add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hPrefix (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule")]
        (.var "compressed-terminal-rule") rules.saveCore.terminalRule
        [.add (.var "compressed-proof-rule"),
         .add (.var "compressed-assertion-launch-rule"),
         .add (.var "compressed-save-rule"),
         .add (.var "compressed-word-advance-rule"),
         .add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hTerminal (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule")]
        (.var "compressed-proof-rule") rules.saveCore.proofRule
        [.add (.var "compressed-assertion-launch-rule"),
         .add (.var "compressed-save-rule"),
         .add (.var "compressed-word-advance-rule"),
         .add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hProof (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule")]
        (.var "compressed-assertion-launch-rule")
        rules.assertionLaunchRule
        [.add (.var "compressed-save-rule"),
         .add (.var "compressed-word-advance-rule"),
         .add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hLaunch (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule")]
        (.var "compressed-save-rule") rules.saveRule
        [.add (.var "compressed-word-advance-rule"),
         .add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hSave (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule")]
        (.var "compressed-word-advance-rule") rules.wordAdvanceRule
        [.add (.var "compressed-accept-rule"),
         .add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hWordAdvance (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule")]
        (.var "compressed-accept-rule") rules.acceptRule
        [.add (.var "compressed-incomplete-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hAccept (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule"),
          .add (.var "compressed-accept-rule")]
        (.var "compressed-incomplete-rule") rules.incompleteRule
        [.add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hIncomplete (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule"),
          .add (.var "compressed-accept-rule"),
          .add (.var "compressed-incomplete-rule")]
        (.var "compressed-invalid-byte-rule") rules.saveCore.invalidByteRule
        [.add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hInvalidByte (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule"),
          .add (.var "compressed-accept-rule"),
          .add (.var "compressed-incomplete-rule"),
          .add (.var "compressed-invalid-byte-rule")]
        (.var "compressed-question-rule") rules.saveCore.questionRule
        [.add (.var "compressed-question-open-fault-rule"),
         .add (.var "compressed-save-fault-rule")]
        substitution rowMember hQuestion (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule"),
          .add (.var "compressed-accept-rule"),
          .add (.var "compressed-incomplete-rule"),
          .add (.var "compressed-invalid-byte-rule"),
          .add (.var "compressed-question-rule")]
        (.var "compressed-question-open-fault-rule")
        rules.saveCore.questionOpenFaultRule
        [.add (.var "compressed-save-fault-rule")]
        substitution rowMember hQuestionOpenFault (by simp))
  · simpa [assertionResumeSinks, assertionResumeOutputTemplates] using
      (mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        _ _ [.remove assertionResumeRequestTemplate,
          .add assertionResumedScanTemplate,
          .add (.var "compressed-prefix-rule"),
          .add (.var "compressed-terminal-rule"),
          .add (.var "compressed-proof-rule"),
          .add (.var "compressed-assertion-launch-rule"),
          .add (.var "compressed-save-rule"),
          .add (.var "compressed-word-advance-rule"),
          .add (.var "compressed-accept-rule"),
          .add (.var "compressed-incomplete-rule"),
          .add (.var "compressed-invalid-byte-rule"),
          .add (.var "compressed-question-rule"),
          .add (.var "compressed-question-open-fault-rule")]
        (.var "compressed-save-fault-rule") rules.saveFaultRule []
        substitution rowMember hSaveFault (by simp))

theorem compressed_assertion_resume_fire_adds_output_rows
    (context : RejoinContext) (space : List Atom)
    (matched : ExactCompressedAssertionResume context space) :
    ∀ row ∈ resumeOutputRows context,
      row ∈ cFireReflectiveSourceExecFact space
        compressedAssertionResumeDirective := by
  exact compressed_assertion_resume_fire_adds_output_rows_for
    baseScannerRuntimeRuleBundle context space matched

/-- Resume preserves every existing expression other than its consumed request.
This carries the returned machine, node, compact stack, and normal stack into
the restored scanner boundary. -/
theorem compressed_assertion_resume_fire_preserves_expression_head
    (space : List Atom) (candidateHead : String) (candidateTail : List Atom)
    (notRequest : "mm-compressed-assertion-resume" ≠ candidateHead)
    (present : .expression (.symbol candidateHead :: candidateTail) ∈
      space.erase compressedAssertionResumeDirective.atom) :
    .expression (.symbol candidateHead :: candidateTail) ∈
      cFireReflectiveSourceExecFact space
        compressedAssertionResumeDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedAssertionResume_sinks_exact]
  apply mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
  · intro sink member
    simp only [assertionResumeSinks, assertionResumeOutputTemplates,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
    · exact Or.inr ⟨assertionResumeRequestTemplate, rfl, by
        intro substitution _rowMember
        exact instantiateTemplateAtom?_expression_symbol_head_ne substitution
          "mm-compressed-assertion-resume" candidateHead _ _ notRequest⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact present

section AxiomAudit

#print axioms compressedAssertionResume_input_exact
#print axioms compressedAssertionResume_sinks_exact
#print axioms speculative_terminal_mem_resume_output
#print axioms base_terminal_not_mem_speculative_resume_output
#print axioms canonical_exact_compressed_assertion_resume_for
#print axioms canonical_exact_compressed_assertion_resume
#print axioms exact_compressed_assertion_resume_for_of_live_rows
#print axioms exact_compressed_assertion_resume_of_live_rows
#print axioms compressed_assertion_resume_fire_adds_output_rows_for
#print axioms compressed_assertion_resume_fire_adds_output_rows
#print axioms compressed_assertion_resume_fire_preserves_expression_head

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
