import Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
import Mettapedia.Languages.Metamath.MM2SourceActionPlan

/-!
# Ordered execution of proof-neutral Metamath source actions in MM2

This module consumes the inert, occurrence-indexed action plans derived from
the authored source fold.  An immediate plan starts only beside the exact
current source statement.  Its actions are consumed in order, and the source
dispatcher is restored only after the declared action count is exhausted.

The rules below establish the generated-input route.  They do not yet make a
hostile hand-authored MM2 action plan authoritative; verifier-side derivation
checking remains a separate admission obligation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2SourceActionExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

private def sourceActionStartLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-action-start"]

private def sourceActionAddLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-action-add"]

private def sourceActionRemoveLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-action-remove"]

private def sourceNormalProofActivateLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-normal-proof-activate"]

private def sourceActionFinishLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-action-finish"]

private def sourceVerifierReloadLocation : Atom :=
  .expression [.symbol "35", .symbol "mm-source-verifier-reload"]

private def normalComparePrepareLocation : Atom :=
  .expression [.symbol "32", .symbol "mm-normal-compare-prepare"]

private def normalRejectLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-normal-reject"]

private def sourceTheoremRejectLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-source-theorem-proof-rejection"]

private def sourceActionCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output"]

private def sourceImmediateActionPlanTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-plan", .var "source", .var "position",
      .var "next-position", .var "statement",
      .symbol "mm-source-action-immediate", .var "action-count"]

private def sourceActionRunningTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-running", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output",
      .var "action-position", .var "action-count"]

private def sourceActionStartRunningTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-running", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output", natAtom 0,
      .var "action-count"]

private def sourceActionOwnerTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-owner", .var "source", .var "position"]

private def sourceActionAddTemplate : Atom :=
  .expression [.symbol "mm-source-action-add", .var "action-row"]

private def sourceActionRemoveTemplate : Atom :=
  .expression [.symbol "mm-source-action-remove", .var "action-row"]

private def sourceActionAddLinkedTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "source-action",
      sourceActionOwnerTemplate, .var "action-position",
      .var "next-action-position", sourceActionAddTemplate]

private def sourceActionRemoveLinkedTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "source-action",
      sourceActionOwnerTemplate, .var "action-position",
      .var "next-action-position", sourceActionRemoveTemplate]

private def sourceActionNextRunningTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-running", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output",
      .var "next-action-position", .var "action-count"]

private def sourceNextControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def sourceStatementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source",
      .var "position", .var "statement"]

private def sourceVerifierReloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def sourceActionStartSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionStartLocation,
      .var "action-start-input", .var "action-start-output"]

private def sourceActionStartPatternAtoms : List Atom :=
  [sourceActionStartSelfTemplate, sourceActionCurrentTemplate,
   sourceImmediateActionPlanTemplate]

private def sourceActionStartInput : Atom :=
  .expression (.symbol "," :: sourceActionStartPatternAtoms)

private def sourceActionStartSinks : List Sink :=
  [.add sourceActionStartSelfTemplate,
   .remove sourceActionCurrentTemplate,
   .remove sourceImmediateActionPlanTemplate,
   .add sourceActionStartRunningTemplate]

private def sourceActionStartOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionStartSelfTemplate],
      .expression [.symbol "-", sourceActionCurrentTemplate],
      .expression [.symbol "-", sourceImmediateActionPlanTemplate],
      .expression [.symbol "+", sourceActionStartRunningTemplate]]

def sourceActionStartRule : Atom :=
  .expression
    [.symbol "exec", sourceActionStartLocation,
      sourceActionStartInput, sourceActionStartOutput]

def sourceActionStartDirective : SourceExecFact where
  atom := sourceActionStartRule
  loc := sourceActionStartLocation
  rule :=
    { priority := 2
      name := "mm-source-action-start"
      input := .compat (mkPattern sourceActionStartPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceActionStartSinks }

theorem extract_sourceActionStartRule_exact :
    extractSupportedSourceExecFact sourceActionStartRule =
      some sourceActionStartDirective := by
  rfl

private def sourceActionAddSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionAddLocation,
      .var "action-add-input", .var "action-add-output"]

private def sourceActionAddPatternAtoms : List Atom :=
  [sourceActionAddSelfTemplate, sourceActionRunningTemplate,
   sourceActionAddLinkedTemplate]

private def sourceActionAddInput : Atom :=
  .expression (.symbol "," :: sourceActionAddPatternAtoms)

private def sourceActionAddSinks : List Sink :=
  [.add sourceActionAddSelfTemplate,
   .remove sourceActionRunningTemplate,
   .remove sourceActionAddLinkedTemplate,
   .add (.var "action-row"),
   .add sourceActionNextRunningTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceActionAddOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionAddSelfTemplate],
      .expression [.symbol "-", sourceActionRunningTemplate],
      .expression [.symbol "-", sourceActionAddLinkedTemplate],
      .expression [.symbol "+", .var "action-row"],
      .expression [.symbol "+", sourceActionNextRunningTemplate],
      .expression [.symbol "+", sourceVerifierReloadTriggerTemplate]]

def sourceActionAddRule : Atom :=
  .expression
    [.symbol "exec", sourceActionAddLocation,
      sourceActionAddInput, sourceActionAddOutput]

def sourceActionAddDirective : SourceExecFact where
  atom := sourceActionAddRule
  loc := sourceActionAddLocation
  rule :=
    { priority := 3
      name := "mm-source-action-add"
      input := .compat (mkPattern sourceActionAddPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceActionAddSinks }

theorem extract_sourceActionAddRule_exact :
    extractSupportedSourceExecFact sourceActionAddRule =
      some sourceActionAddDirective := by
  rfl

private def sourceActionRemoveSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionRemoveLocation,
      .var "action-remove-input", .var "action-remove-output"]

private def sourceActionRemovePatternAtoms : List Atom :=
  [sourceActionRemoveSelfTemplate, sourceActionRunningTemplate,
   sourceActionRemoveLinkedTemplate, .var "action-row"]

private def sourceActionRemoveInput : Atom :=
  .expression (.symbol "," :: sourceActionRemovePatternAtoms)

private def sourceActionRemoveSinks : List Sink :=
  [.add sourceActionRemoveSelfTemplate,
   .remove sourceActionRunningTemplate,
   .remove sourceActionRemoveLinkedTemplate,
   .remove (.var "action-row"),
   .add sourceActionNextRunningTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceActionRemoveOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionRemoveSelfTemplate],
      .expression [.symbol "-", sourceActionRunningTemplate],
      .expression [.symbol "-", sourceActionRemoveLinkedTemplate],
      .expression [.symbol "-", .var "action-row"],
      .expression [.symbol "+", sourceActionNextRunningTemplate],
      .expression [.symbol "+", sourceVerifierReloadTriggerTemplate]]

def sourceActionRemoveRule : Atom :=
  .expression
    [.symbol "exec", sourceActionRemoveLocation,
      sourceActionRemoveInput, sourceActionRemoveOutput]

def sourceActionRemoveDirective : SourceExecFact where
  atom := sourceActionRemoveRule
  loc := sourceActionRemoveLocation
  rule :=
    { priority := 3
      name := "mm-source-action-remove"
      input := .compat (mkPattern sourceActionRemovePatternAtoms)
      guards := []
      tmpl := mkTemplate sourceActionRemoveSinks }

theorem extract_sourceActionRemoveRule_exact :
    extractSupportedSourceExecFact sourceActionRemoveRule =
      some sourceActionRemoveDirective := by
  rfl

private def sourceActionFinishSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionFinishLocation,
      .var "action-finish-input", .var "action-finish-output"]

private def sourceActionFinishedRunningTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-running", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output",
      .var "action-count", .var "action-count"]

private def sourceActionFinishPatternAtoms : List Atom :=
  [sourceActionFinishSelfTemplate, sourceActionFinishedRunningTemplate]

private def sourceActionFinishInput : Atom :=
  .expression (.symbol "," :: sourceActionFinishPatternAtoms)

private def sourceActionFinishSinks : List Sink :=
  [.add sourceActionFinishSelfTemplate,
   .remove sourceActionFinishedRunningTemplate,
   .add sourceNextControlTemplate,
   .add sourceStatementAppliedTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceActionFinishOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionFinishSelfTemplate],
      .expression [.symbol "-", sourceActionFinishedRunningTemplate],
      .expression [.symbol "+", sourceNextControlTemplate],
      .expression [.symbol "+", sourceStatementAppliedTemplate],
      .expression [.symbol "+", sourceVerifierReloadTriggerTemplate]]

def sourceActionFinishRule : Atom :=
  .expression
    [.symbol "exec", sourceActionFinishLocation,
      sourceActionFinishInput, sourceActionFinishOutput]

def sourceActionFinishDirective : SourceExecFact where
  atom := sourceActionFinishRule
  loc := sourceActionFinishLocation
  rule :=
    { priority := 4
      name := "mm-source-action-finish"
      input := .compat (mkPattern sourceActionFinishPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceActionFinishSinks }

theorem extract_sourceActionFinishRule_exact :
    extractSupportedSourceExecFact sourceActionFinishRule =
      some sourceActionFinishDirective := by
  rfl

/-! ## Proof activation at the ordered theorem occurrence -/

/-- Proof syntax remains ordinary inert data, but its initial control row is
wrapped until ordered source dispatch reaches the theorem occurrence.  The
compressed form is also withheld, although its executor is outside the
current normal-proof tranche. -/
def deferProofControlRow : Atom → Atom
  | row@(.expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner, _, _]) =>
      .expression
        [.symbol "mm-source-proof-control-prepared", scopeOwner,
          proofOwner, row]
  | row@(.expression
      [.symbol "mm-compressed-control", scopeOwner, proofOwner, _, _]) =>
      .expression
        [.symbol "mm-source-proof-control-prepared", scopeOwner,
          proofOwner, row]
  | row => row

def deferProofControls (rows : List Atom) : List Atom :=
  rows.map deferProofControlRow

private def sourceTheoremProofRequestTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", .var "source",
      .var "position", .var "next-position", .var "statement"]

private def sourceNormalInitialControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "source",
      .expression
        [.symbol "mm-source-proof-owner", .var "source", .var "position"],
      natAtom 0, natAtom 0]

private def sourcePreparedNormalControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-proof-control-prepared", .var "source",
      .expression
        [.symbol "mm-source-proof-owner", .var "source", .var "position"],
      sourceNormalInitialControlTemplate]

private def sourceNormalDispatchReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-normal-dispatch",
      .expression
        [.symbol "mm-source-proof-owner", .var "source", .var "position"]]

private def sourceNormalProofActivateSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceNormalProofActivateLocation,
      .var "proof-activate-input", .var "proof-activate-output"]

private def sourceNormalProofActivatePatternAtoms : List Atom :=
  [sourceNormalProofActivateSelfTemplate, sourceTheoremProofRequestTemplate,
   sourcePreparedNormalControlTemplate]

private def sourceNormalProofActivateInput : Atom :=
  .expression (.symbol "," :: sourceNormalProofActivatePatternAtoms)

private def sourceNormalProofActivateSinks : List Sink :=
  [.add sourceNormalProofActivateSelfTemplate,
   .remove sourceTheoremProofRequestTemplate,
   .remove sourcePreparedNormalControlTemplate,
   .add sourceNormalInitialControlTemplate,
   .add sourceNormalDispatchReloadTriggerTemplate]

private def sourceNormalProofActivateOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceNormalProofActivateSelfTemplate],
      .expression [.symbol "-", sourceTheoremProofRequestTemplate],
      .expression [.symbol "-", sourcePreparedNormalControlTemplate],
      .expression [.symbol "+", sourceNormalInitialControlTemplate],
      .expression [.symbol "+", sourceNormalDispatchReloadTriggerTemplate]]

def sourceNormalProofActivateRule : Atom :=
  .expression
    [.symbol "exec", sourceNormalProofActivateLocation,
      sourceNormalProofActivateInput, sourceNormalProofActivateOutput]

def sourceNormalProofActivateDirective : SourceExecFact where
  atom := sourceNormalProofActivateRule
  loc := sourceNormalProofActivateLocation
  rule :=
    { priority := 3
      name := "mm-source-normal-proof-activate"
      input := .compat (mkPattern sourceNormalProofActivatePatternAtoms)
      guards := []
      tmpl := mkTemplate sourceNormalProofActivateSinks }

theorem extract_sourceNormalProofActivateRule_exact :
    extractSupportedSourceExecFact sourceNormalProofActivateRule =
      some sourceNormalProofActivateDirective := by
  rfl

/-! ## Constructive wrong-conclusion rejection -/

private def normalComparePrepareSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalComparePrepareLocation,
      .var "normal-compare-input", .var "normal-compare-output"]

private def normalCompareControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "end", .var "top"]

private def normalCompareEndTemplate : Atom :=
  .expression [.symbol "mm-proof-end", .var "proof", .var "end"]

private def normalCompareProofTemplate : Atom :=
  .expression
    [.symbol "mm-proof", .var "scope", .var "proof", .symbol "normal",
      .var "theorem-label", .var "expected"]

private def normalCompareSingletonStackTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof", natAtom 0, .var "top"]

private def normalCompareActualStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", natAtom 0,
      .var "actual", .var "occurrence"]

private def normalExpectedCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof",
      .var "expected"]

private def normalActualCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof",
      .var "actual"]

private def normalComparePreparePatternAtoms : List Atom :=
  [normalComparePrepareSelfTemplate, normalCompareControlTemplate,
   normalCompareEndTemplate, normalCompareProofTemplate,
   normalCompareSingletonStackTemplate, normalCompareActualStackTemplate]

private def normalComparePrepareInput : Atom :=
  .expression (.symbol "," :: normalComparePreparePatternAtoms)

private def normalComparePrepareSinks : List Sink :=
  [.add normalExpectedCandidateTemplate, .add normalActualCandidateTemplate]

private def normalComparePrepareOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", normalExpectedCandidateTemplate],
      .expression [.symbol "+", normalActualCandidateTemplate]]

def normalComparePrepareRule : Atom :=
  .expression
    [.symbol "exec", normalComparePrepareLocation,
      normalComparePrepareInput, normalComparePrepareOutput]

def normalComparePrepareDirective : SourceExecFact where
  atom := normalComparePrepareRule
  loc := normalComparePrepareLocation
  rule :=
    { priority := 32
      name := "mm-normal-compare-prepare"
      input := .compat (mkPattern normalComparePreparePatternAtoms)
      guards := []
      tmpl := mkTemplate normalComparePrepareSinks }

theorem extract_normalComparePrepareRule_exact :
    extractSupportedSourceExecFact normalComparePrepareRule =
      some normalComparePrepareDirective := by
  rfl

private def normalRejectSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalRejectLocation,
      .var "normal-reject-input", .var "normal-reject-output"]

private def normalRejectControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "end", .var "top"]

private def normalRejectProofTemplate : Atom :=
  .expression
    [.symbol "mm-proof", .var "scope", .var "proof", .symbol "normal",
      .var "theorem-label", .var "expected"]

private def normalRejectEndTemplate : Atom :=
  .expression [.symbol "mm-proof-end", .var "proof", .var "end"]

private def normalRejectSingletonStackTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof", natAtom 0, .var "top"]

private def normalRejectActualStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", natAtom 0,
      .var "actual", .var "occurrence"]

private def normalRejectExpectedStackTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof",
      .var "expected"]

private def normalRejectActualCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof",
      .var "actual"]

private def normalRejectFactors : List SourceFactor :=
  [.btm normalRejectSelfTemplate,
   .btm normalRejectControlTemplate,
   .btm normalRejectEndTemplate,
   .btm normalRejectProofTemplate,
   .btm normalRejectSingletonStackTemplate,
   .btm normalRejectActualStackTemplate,
   .neqConstraint normalRejectExpectedStackTemplate
      normalRejectActualCandidateTemplate]

private def normalRejectInput : Atom :=
  .expression
    [.symbol "I",
      .expression [.symbol "BTM", normalRejectSelfTemplate],
      .expression [.symbol "BTM", normalRejectControlTemplate],
      .expression [.symbol "BTM", normalRejectEndTemplate],
      .expression [.symbol "BTM", normalRejectProofTemplate],
      .expression [.symbol "BTM", normalRejectSingletonStackTemplate],
      .expression [.symbol "BTM", normalRejectActualStackTemplate],
      .expression
        [.symbol "!=", normalRejectExpectedStackTemplate,
          normalRejectActualCandidateTemplate]]

/-- A normal proof that ends with one stack cell carrying the wrong formula
has a concrete mismatch witness.  The source-position continuation below is
the authoritative source-level rejection boundary. -/
def normalRejectedAtom (scope proof theoremLabel expected actual occurrence :
    Atom) : Atom :=
  .expression
    [.symbol "mm-rejected", scope, proof, theoremLabel,
      .symbol "wrong-conclusion", expected, actual, occurrence]

private def normalRejectedTemplate : Atom :=
  normalRejectedAtom (.var "scope") (.var "proof")
    (.var "theorem-label") (.var "expected") (.var "actual")
    (.var "occurrence")

private def normalRejectSinks : List Sink :=
  [.remove normalRejectControlTemplate, .add normalRejectedTemplate]

private def normalRejectOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalRejectControlTemplate],
      .expression [.symbol "+", normalRejectedTemplate]]

def normalRejectRule : Atom :=
  .expression
    [.symbol "exec", normalRejectLocation,
      normalRejectInput, normalRejectOutput]

def normalRejectDirective : SourceExecFact where
  atom := normalRejectRule
  loc := normalRejectLocation
  rule :=
    { priority := 33
      name := "mm-normal-reject"
      input := .explicit normalRejectFactors
      guards := []
      tmpl := mkTemplate normalRejectSinks }

theorem extract_normalRejectRule_exact :
    extractSupportedSourceExecFact normalRejectRule =
      some normalRejectDirective := by
  rfl

private def normalCompareExpectedCanary : Atom :=
  .expression [.symbol "candidate", .symbol "expected"]

private def normalCompareActualCanary : Atom :=
  .expression [.symbol "candidate", .symbol "actual"]

/-- Equal final formulas collapse to one set element, so exclusion leaves no
second candidate that could witness rejection. -/
theorem equal_final_formula_has_no_rejection_witness :
    cmatchSourceFactor [] [normalCompareExpectedCanary]
        (.neqConstraint normalCompareExpectedCanary
          normalCompareExpectedCanary) = [] := by
  rfl

/-- Distinct expected and actual formulas remain as two set elements, and the
actual candidate survives exclusion of the expected candidate. -/
theorem unequal_final_formula_has_rejection_witness :
    cmatchSourceFactor []
        [normalCompareExpectedCanary, normalCompareActualCanary]
        (.neqConstraint normalCompareExpectedCanary
          normalCompareActualCanary) =
      [([], normalCompareActualCanary)] := by
  rfl

private def sourceTheoremRejectSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceTheoremRejectLocation,
      .var "source-reject-input", .var "source-reject-output"]

private def sourceTheoremRejectStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem", .var "theorem-site",
      .var "source-theorem-label", .var "theorem-typecode",
      .var "theorem-body", .var "theorem-proof",
      .var "theorem-separator", .var "theorem-terminator"]

private def sourceTheoremRejectPendingTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-pending", .var "source",
      .var "position", .var "next-position",
      sourceTheoremRejectStatementTemplate,
      .var "theorem-dispatch-input", .var "theorem-dispatch-output"]

private def sourceTheoremRejectContextTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-context", .var "source",
      .var "position", .var "proof-owner", .var "proof-theorem-label",
      .var "expected"]

private def sourceTheoremRejectWireTemplate : Atom :=
  normalRejectedAtom (.var "source") (.var "proof-owner")
    (.var "proof-theorem-label") (.var "expected") (.var "actual")
    (.var "proof-occurrence")

private def sourceTheoremRejectPreparedHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-assertion-header", .var "source",
      .var "position", .var "proof-owner", .var "assertion-header"]

private def sourceTheoremRejectExpectedCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof-owner",
      .var "expected"]

private def sourceTheoremRejectActualCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-final-formula-candidate", .var "proof-owner",
      .var "actual"]

private def sourceTheoremRejectedTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-rejected", .var "source",
      .var "position", sourceTheoremRejectStatementTemplate,
      .symbol "wrong-conclusion", .var "expected", .var "actual",
      .var "proof-occurrence"]

private def sourceTheoremRejectPatternAtoms : List Atom :=
  [sourceTheoremRejectSelfTemplate, sourceTheoremRejectPendingTemplate,
   sourceTheoremRejectContextTemplate, sourceTheoremRejectWireTemplate,
   sourceTheoremRejectPreparedHeaderTemplate,
   sourceTheoremRejectExpectedCandidateTemplate,
   sourceTheoremRejectActualCandidateTemplate]

private def sourceTheoremRejectInput : Atom :=
  .expression (.symbol "," :: sourceTheoremRejectPatternAtoms)

private def sourceTheoremRejectSinks : List Sink :=
  [.add sourceTheoremRejectSelfTemplate,
   .remove sourceTheoremRejectPendingTemplate,
   .remove sourceTheoremRejectContextTemplate,
   .remove sourceTheoremRejectWireTemplate,
   .remove sourceTheoremRejectPreparedHeaderTemplate,
   .remove sourceTheoremRejectExpectedCandidateTemplate,
   .remove sourceTheoremRejectActualCandidateTemplate,
   .add sourceTheoremRejectedTemplate]

private def sourceTheoremRejectOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceTheoremRejectSelfTemplate],
      .expression [.symbol "-", sourceTheoremRejectPendingTemplate],
      .expression [.symbol "-", sourceTheoremRejectContextTemplate],
      .expression [.symbol "-", sourceTheoremRejectWireTemplate],
      .expression [.symbol "-", sourceTheoremRejectPreparedHeaderTemplate],
      .expression [.symbol "-", sourceTheoremRejectExpectedCandidateTemplate],
      .expression [.symbol "-", sourceTheoremRejectActualCandidateTemplate],
      .expression [.symbol "+", sourceTheoremRejectedTemplate]]

def sourceTheoremRejectRule : Atom :=
  .expression
    [.symbol "exec", sourceTheoremRejectLocation,
      sourceTheoremRejectInput, sourceTheoremRejectOutput]

def sourceTheoremRejectDirective : SourceExecFact where
  atom := sourceTheoremRejectRule
  loc := sourceTheoremRejectLocation
  rule :=
    { priority := 33
      name := "mm-source-theorem-proof-rejection"
      input := .compat (mkPattern sourceTheoremRejectPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceTheoremRejectSinks }

theorem extract_sourceTheoremRejectRule_exact :
    extractSupportedSourceExecFact sourceTheoremRejectRule =
      some sourceTheoremRejectDirective := by
  rfl

/-! ## Verifier-owned rule reinstallation -/

/-- Source scheduling consumes even an `exec` whose pattern does not match.
These are exactly the database-independent rules needed again at the next
source occurrence. -/
private def sourceVerifierReloadableBaseRules : List Atom :=
  [sourceEventDispatchRule, sourceTheoremStartRule,
   sourceTheoremSuccessRule, sourceTheoremRejectRule,
   sourceTheoremCommitRule,
   sourceActionStartRule, sourceActionAddRule, sourceActionRemoveRule,
   sourceActionFinishRule, sourceNormalProofActivateRule,
   normalDispatchReloadRule]

def sourceVerifierRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-verifier-rule", rule]

private def sourceVerifierReloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-verifier-rule", .var "reload-rule"]

private def sourceVerifierReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceVerifierReloadLocation,
      .var "source-reload-input", .var "source-reload-output"]

private def sourceVerifierReloadPatternAtoms : List Atom :=
  [sourceVerifierReloadSelfTemplate, sourceVerifierReloadTriggerTemplate,
   sourceVerifierReloadRuleTemplate]

private def sourceVerifierReloadInput : Atom :=
  .expression (.symbol "," :: sourceVerifierReloadPatternAtoms)

private def sourceVerifierReloadSinks : List Sink :=
  [.add sourceVerifierReloadSelfTemplate,
   .remove sourceVerifierReloadTriggerTemplate,
   .add (.var "reload-rule")]

private def sourceVerifierReloadOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceVerifierReloadSelfTemplate],
      .expression [.symbol "-", sourceVerifierReloadTriggerTemplate],
      .expression [.symbol "+", .var "reload-rule"]]

def sourceVerifierReloadRule : Atom :=
  .expression
    [.symbol "exec", sourceVerifierReloadLocation,
      sourceVerifierReloadInput, sourceVerifierReloadOutput]

def sourceVerifierReloadDirective : SourceExecFact where
  atom := sourceVerifierReloadRule
  loc := sourceVerifierReloadLocation
  rule :=
    { priority := 35
      name := "mm-source-verifier-reload"
      input := .compat (mkPattern sourceVerifierReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceVerifierReloadSinks }

theorem extract_sourceVerifierReloadRule_exact :
    extractSupportedSourceExecFact sourceVerifierReloadRule =
      some sourceVerifierReloadDirective := by
  rfl

def sourceVerifierReloadableRules : List Atom :=
  sourceVerifierReloadableBaseRules ++
    [sourceVerifierReloadRule]

def sourceVerifierRuleRows : List Atom :=
  sourceVerifierReloadableRules.map sourceVerifierRuleRow

/-- The current normal dispatcher relation omits its terminal observer even
though MM2 may consume that observer before an assertion macro-step finishes.
The extension retains the existing accept rule as verifier-owned inert code
so the existing normal reloader can restore it with the other proof rules. -/
def normalTerminalReloadRows : List Atom :=
  [normalDispatchRuleRow normalComparePrepareRule,
   normalDispatchRuleRow normalAcceptRule,
   normalDispatchRuleRow normalRejectRule,
   normalDispatchRuleRow sourceTheoremRejectRule]

def orderedSourceActionRules : List Atom :=
  [sourceActionStartRule, sourceActionAddRule, sourceActionRemoveRule,
   sourceActionFinishRule, sourceNormalProofActivateRule,
   sourceVerifierReloadRule]

def orderedSourceActionDirectives : List SourceExecFact :=
  [sourceActionStartDirective, sourceActionAddDirective,
   sourceActionRemoveDirective, sourceActionFinishDirective,
   sourceNormalProofActivateDirective, sourceVerifierReloadDirective]

def sourceVerdictRules : List Atom :=
  [normalComparePrepareRule, normalRejectRule, sourceTheoremRejectRule]

def sourceActionVerifierExtensionProgram : List Atom :=
  normalTerminalReloadRows ++ sourceVerifierRuleRows ++
    orderedSourceActionRules ++ sourceVerdictRules

theorem orderedSourceActionRules_extract_exact :
    orderedSourceActionRules.filterMap extractSupportedSourceExecFact =
      orderedSourceActionDirectives := by
  rfl

end Mettapedia.Languages.Metamath.MM2SourceActionExecution

#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.orderedSourceActionRules_extract_exact
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.extract_normalComparePrepareRule_exact
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.extract_normalRejectRule_exact
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.extract_sourceTheoremRejectRule_exact
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.equal_final_formula_has_no_rejection_witness
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionExecution.unequal_final_formula_has_rejection_witness
