import Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
import Mettapedia.Languages.Metamath.MM2SourceActionPlan

/-!
# Ordered execution of proof-neutral Metamath source actions in MM2

This module consumes the inert, occurrence-indexed action plans derived from
the authored source fold.  An immediate plan starts only beside the exact
current source statement.  A proof-gated plan starts only from the exact
release occurrence produced after proof success.  In both cases actions are
consumed in order.  Source order advances only after the declared action count
is exhausted; the proof-gated finish also publishes theorem admission.

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
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private def atomHasHeadSymbol (name : String) : Atom → Bool
  | .expression (.symbol head :: _) => head == name
  | _ => false

private def execInputRequiresHead (name : String) : Atom → Bool
  | .expression
      [.symbol "exec", _, .expression (.symbol "," :: premises), _] =>
      premises.any (atomHasHeadSymbol name)
  | _ => false

/-- The finite generic-normal-rule inventory consumed by the ordered source
extension.  The inventory carries existing rules; it does not re-author their
semantics or grant authority to caller-supplied MM2 data. -/
structure NormalProofRuleInventory where
  dvPairBegin : Atom
  dvLeftConst : Atom
  dvLeftVariable : Atom
  dvRightConst : Atom
  dvRightVariable : Atom
  dvRightNil : Atom
  dvLeftNil : Atom
  dvComplete : Atom
  dispatchReload : Atom
  dispatchRuleRow : Atom → Atom
  accept : Atom
  assertionStart : Atom
  assertionBegin : Atom
  hypothesisStep : Atom
  assertionStartRequiresHeader :
    execInputRequiresHead "mm-assertion-header" assertionStart = true
  assertionBeginRequiresHeader :
    execInputRequiresHead "mm-assertion-header" assertionBegin = true
  hypothesisStepDoesNotRequireHeader :
    execInputRequiresHead "mm-assertion-header" hypothesisStep = false

private def sourceActionStartLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-action-start"]

private def sourceAfterProofActionStartLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-action-after-proof-start"]

private def sourceActionAddLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-action-add"]

private def sourceActionRemoveLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-action-remove"]

private def sourceNormalProofActivateLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-normal-proof-activate"]

private def sourceActionFinishLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-action-finish"]

private def sourceAfterProofActionFinishLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-action-after-proof-finish"]

private def sourceVerifierReloadLocation : Atom :=
  .expression [.symbol "35", .symbol "mm-source-verifier-reload"]

private def normalComparePrepareLocation : Atom :=
  .expression [.symbol "32", .symbol "mm-normal-compare-prepare"]

private def normalRejectLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-normal-reject"]

private def sourceTheoremRejectLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-source-theorem-proof-rejection"]

private def normalDVSameVariableFaultLocation : Atom :=
  .expression [.symbol "18", .symbol "mm-normal-dv-same-variable-fault"]

private def normalDVFailureReloadLocation : Atom :=
  .expression [.symbol "21", .symbol "mm-normal-dv-failure-reload"]

private def sourceTheoremFaultRejectLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-source-theorem-proof-fault"]

private def normalFloatingTypecodePrepareLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-normal-floating-typecode-prepare"]

private def normalFloatingTypecodeEqualLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-normal-floating-typecode-equal"]

private def normalFloatingTypecodeFaultLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-normal-floating-typecode-fault"]

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

/-- The finite successor relation emitted from the admitted action plan.  The
same `next-action-position` variable occurs in the linked row, so MM2 can only
advance along an explicitly supplied successor edge. -/
private def sourceActionSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", sourceActionOwnerTemplate,
      .var "action-position", .var "next-action-position"]

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

/-! ## Proof-gated source-state delta release -/

private def sourceAfterProofReleaseTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-action-release", .var "source",
      .var "position", .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output",
      .var "proof-occurrence"]

private def sourceAfterProofActionPlanTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-plan", .var "source", .var "position",
      .var "next-position", .var "statement",
      .symbol "mm-source-action-after-proof", .var "action-count"]

private def sourceAfterProofAdmissionPendingTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-admission-pending", .var "source",
      .var "position", .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output",
      .var "proof-occurrence"]

private def sourceAfterProofActionStartSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceAfterProofActionStartLocation,
      .var "after-proof-start-input", .var "after-proof-start-output"]

private def sourceAfterProofActionStartPatternAtoms : List Atom :=
  [sourceAfterProofActionStartSelfTemplate, sourceAfterProofReleaseTemplate,
   sourceAfterProofActionPlanTemplate]

private def sourceAfterProofActionStartInput : Atom :=
  .expression (.symbol "," :: sourceAfterProofActionStartPatternAtoms)

private def sourceAfterProofActionStartSinks : List Sink :=
  [.add sourceAfterProofActionStartSelfTemplate,
   .remove sourceAfterProofReleaseTemplate,
   .remove sourceAfterProofActionPlanTemplate,
   .add sourceActionStartRunningTemplate,
   .add sourceAfterProofAdmissionPendingTemplate]

private def sourceAfterProofActionStartOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceAfterProofActionStartSelfTemplate],
      .expression [.symbol "-", sourceAfterProofReleaseTemplate],
      .expression [.symbol "-", sourceAfterProofActionPlanTemplate],
      .expression [.symbol "+", sourceActionStartRunningTemplate],
      .expression [.symbol "+", sourceAfterProofAdmissionPendingTemplate]]

/-- Start the exact theorem-state delta only after conditional admission has
produced the matching proof-success release occurrence. -/
def sourceAfterProofActionStartRule : Atom :=
  .expression
    [.symbol "exec", sourceAfterProofActionStartLocation,
      sourceAfterProofActionStartInput, sourceAfterProofActionStartOutput]

def sourceAfterProofActionStartDirective : SourceExecFact where
  atom := sourceAfterProofActionStartRule
  loc := sourceAfterProofActionStartLocation
  rule :=
    { priority := 2
      name := "mm-source-action-after-proof-start"
      input := .compat (mkPattern sourceAfterProofActionStartPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceAfterProofActionStartSinks }

theorem extract_sourceAfterProofActionStartRule_exact :
    extractSupportedSourceExecFact sourceAfterProofActionStartRule =
      some sourceAfterProofActionStartDirective := by
  rfl

private def sourceAfterProofCanaryRelease (owner : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-action-release", owner, natAtom 5, natAtom 6,
      .symbol "statement", .symbol "dispatch-input",
      .symbol "dispatch-output", .symbol "proof-occurrence"]

private def sourceAfterProofCanaryPlan (owner : Atom) : Atom :=
  .expression
    [.symbol "mm-source-action-plan", owner, natAtom 5, natAtom 6,
      .symbol "statement", .symbol "mm-source-action-after-proof", natAtom 1]

private def sourceAfterProofCanaryOwner : Atom := .symbol "source"

/-- Positive control: the exact release occurrence and proof-gated plan start
one ordered action run. -/
theorem sourceAfterProofActionStart_accepts_exact_release_canary :
    (cmatchPattern []
      [sourceAfterProofActionStartRule,
       sourceAfterProofCanaryRelease sourceAfterProofCanaryOwner,
       sourceAfterProofCanaryPlan sourceAfterProofCanaryOwner]
      (mkPattern sourceAfterProofActionStartPatternAtoms)).isEmpty = false := by
  decide +kernel

/-- Negative control: prepared proof-gated rows cannot start before proof
success has produced their release occurrence. -/
theorem sourceAfterProofActionStart_rejects_unreleased_canary :
    cmatchPattern []
      [sourceAfterProofActionStartRule,
       sourceAfterProofCanaryPlan sourceAfterProofCanaryOwner]
      (mkPattern sourceAfterProofActionStartPatternAtoms) = [] := by
  decide +kernel

/-- Negative control: a release occurrence owned by another source cannot
authorize this plan. -/
theorem sourceAfterProofActionStart_rejects_foreign_release_canary :
    cmatchPattern []
      [sourceAfterProofActionStartRule,
       sourceAfterProofCanaryRelease (.symbol "foreign-source"),
       sourceAfterProofCanaryPlan sourceAfterProofCanaryOwner]
      (mkPattern sourceAfterProofActionStartPatternAtoms) = [] := by
  decide +kernel

private def sourceActionAddSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionAddLocation,
      .var "action-add-input", .var "action-add-output"]

private def sourceActionAddPatternAtoms : List Atom :=
  [sourceActionAddSelfTemplate, sourceActionRunningTemplate,
   sourceActionSuccessorTemplate, sourceActionAddLinkedTemplate]

private def sourceActionAddInput : Atom :=
  .expression (.symbol "," :: sourceActionAddPatternAtoms)

private def sourceActionAddSinks : List Sink :=
  [.add sourceActionAddSelfTemplate,
   .remove sourceActionRunningTemplate,
   .remove sourceActionSuccessorTemplate,
   .remove sourceActionAddLinkedTemplate,
   .add (.var "action-row"),
   .add sourceActionNextRunningTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceActionAddOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionAddSelfTemplate],
      .expression [.symbol "-", sourceActionRunningTemplate],
      .expression [.symbol "-", sourceActionSuccessorTemplate],
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

private def sourceActionAddCanarySource : Atom := .symbol "source"

private def sourceActionAddCanaryPosition : Nat := 5

private def sourceActionAddCanaryPayload : Atom :=
  .expression [.symbol "mm-const", .symbol "payload"]

private def sourceActionAddCanaryRunning : Atom :=
  .expression
    [.symbol "mm-source-action-running", sourceActionAddCanarySource,
      natAtom sourceActionAddCanaryPosition,
      natAtom (sourceActionAddCanaryPosition + 1), .symbol "statement",
      .symbol "dispatch-input", .symbol "dispatch-output", natAtom 0,
      natAtom 2]

private def sourceActionAddCanarySuccessor : Atom :=
  .expression
    [.symbol "mm-index-successor",
      sourceActionOwner sourceActionAddCanarySource
        sourceActionAddCanaryPosition,
      natAtom 0, natAtom 1]

private def sourceActionAddCanaryLinked (nextPosition : Nat) : Atom :=
  linkedRow "source-action"
    (sourceActionOwner sourceActionAddCanarySource
      sourceActionAddCanaryPosition)
    0 nextPosition
    (.expression
      [.symbol "mm-source-action-add", sourceActionAddCanaryPayload])

private def sourceActionAddCanaryAtoms (nextPosition : Nat) : List Atom :=
  [sourceActionAddRule, sourceActionAddCanaryRunning,
   sourceActionAddCanarySuccessor,
   sourceActionAddCanaryLinked nextPosition]

/-- Positive control: a canonical linked action and its exact successor row
jointly satisfy the executable add pattern. -/
theorem sourceActionAddPattern_accepts_successor_canary :
    (cmatchPattern [] (sourceActionAddCanaryAtoms 1)
      (mkPattern sourceActionAddPatternAtoms)).isEmpty = false := by
  decide +kernel

/-- Negative control: a linked row that jumps over the emitted successor
cannot satisfy the executable add pattern. -/
theorem sourceActionAddPattern_rejects_jump_canary :
    cmatchPattern [] (sourceActionAddCanaryAtoms 2)
      (mkPattern sourceActionAddPatternAtoms) = [] := by
  decide +kernel

private def sourceActionRemoveSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionRemoveLocation,
      .var "action-remove-input", .var "action-remove-output"]

private def sourceActionRemovePatternAtoms : List Atom :=
  [sourceActionRemoveSelfTemplate, sourceActionRunningTemplate,
   sourceActionSuccessorTemplate, sourceActionRemoveLinkedTemplate,
   .var "action-row"]

private def sourceActionRemoveInput : Atom :=
  .expression (.symbol "," :: sourceActionRemovePatternAtoms)

private def sourceActionRemoveSinks : List Sink :=
  [.add sourceActionRemoveSelfTemplate,
   .remove sourceActionRunningTemplate,
   .remove sourceActionSuccessorTemplate,
   .remove sourceActionRemoveLinkedTemplate,
   .remove (.var "action-row"),
   .add sourceActionNextRunningTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceActionRemoveOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceActionRemoveSelfTemplate],
      .expression [.symbol "-", sourceActionRunningTemplate],
      .expression [.symbol "-", sourceActionSuccessorTemplate],
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

/-- Both state-mutating action transitions require the explicit finite
successor relation; a linked row alone cannot advance the action cursor. -/
theorem sourceActionMutationRules_require_successor :
    [sourceActionAddRule, sourceActionRemoveRule].all
      (execInputRequiresHead "mm-index-successor") = true := by
  decide +kernel

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

private def sourceAfterProofActionFinishSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceAfterProofActionFinishLocation,
      .var "after-proof-finish-input", .var "after-proof-finish-output"]

private def sourceAfterProofAdmittedTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-admitted", .var "source",
      .var "position", .var "statement", .var "proof-occurrence"]

private def sourceAfterProofActionFinishPatternAtoms : List Atom :=
  [sourceAfterProofActionFinishSelfTemplate,
   sourceActionFinishedRunningTemplate,
   sourceAfterProofAdmissionPendingTemplate]

private def sourceAfterProofActionFinishInput : Atom :=
  .expression (.symbol "," :: sourceAfterProofActionFinishPatternAtoms)

private def sourceAfterProofActionFinishSinks : List Sink :=
  [.add sourceAfterProofActionFinishSelfTemplate,
   .remove sourceActionFinishedRunningTemplate,
   .remove sourceAfterProofAdmissionPendingTemplate,
   .add sourceAfterProofAdmittedTemplate,
   .add sourceNextControlTemplate,
   .add sourceStatementAppliedTemplate,
   .add sourceVerifierReloadTriggerTemplate]

private def sourceAfterProofActionFinishOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceAfterProofActionFinishSelfTemplate],
      .expression [.symbol "-", sourceActionFinishedRunningTemplate],
      .expression [.symbol "-", sourceAfterProofAdmissionPendingTemplate],
      .expression [.symbol "+", sourceAfterProofAdmittedTemplate],
      .expression [.symbol "+", sourceNextControlTemplate],
      .expression [.symbol "+", sourceStatementAppliedTemplate],
      .expression [.symbol "+", sourceVerifierReloadTriggerTemplate]]

/-- Complete a proof-gated source-state delta.  This is the only continuation
in the action layer that turns its private pending occurrence into theorem
admission, and it advances source order in the same step. -/
def sourceAfterProofActionFinishRule : Atom :=
  .expression
    [.symbol "exec", sourceAfterProofActionFinishLocation,
      sourceAfterProofActionFinishInput, sourceAfterProofActionFinishOutput]

def sourceAfterProofActionFinishDirective : SourceExecFact where
  atom := sourceAfterProofActionFinishRule
  loc := sourceAfterProofActionFinishLocation
  rule :=
    { priority := 3
      name := "mm-source-action-after-proof-finish"
      input := .compat (mkPattern sourceAfterProofActionFinishPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceAfterProofActionFinishSinks }

theorem extract_sourceAfterProofActionFinishRule_exact :
    extractSupportedSourceExecFact sourceAfterProofActionFinishRule =
      some sourceAfterProofActionFinishDirective := by
  rfl

private def sourceAfterProofCanaryFinishedRunning : Atom :=
  .expression
    [.symbol "mm-source-action-running", sourceAfterProofCanaryOwner,
      natAtom 5, natAtom 6, .symbol "statement", .symbol "dispatch-input",
      .symbol "dispatch-output", natAtom 1, natAtom 1]

private def sourceAfterProofCanaryAdmissionPending : Atom :=
  .expression
    [.symbol "mm-source-theorem-admission-pending",
      sourceAfterProofCanaryOwner, natAtom 5, natAtom 6,
      .symbol "statement", .symbol "dispatch-input",
      .symbol "dispatch-output", .symbol "proof-occurrence"]

/-- Positive control: a completed proof-gated action run and its exact private
continuation jointly enable theorem admission. -/
theorem sourceAfterProofActionFinish_accepts_pending_canary :
    (cmatchPattern []
      [sourceAfterProofActionFinishRule,
       sourceAfterProofCanaryFinishedRunning,
       sourceAfterProofCanaryAdmissionPending]
      (mkPattern sourceAfterProofActionFinishPatternAtoms)).isEmpty = false := by
  decide +kernel

/-- Negative control: a finished action cursor alone cannot manufacture
theorem admission. -/
theorem sourceAfterProofActionFinish_rejects_missing_pending_canary :
    cmatchPattern []
      [sourceAfterProofActionFinishRule,
       sourceAfterProofCanaryFinishedRunning]
      (mkPattern sourceAfterProofActionFinishPatternAtoms) = [] := by
  decide +kernel

/-- When both finish rules could see the same completed cursor, the
proof-gated continuation is scheduled first and consumes it together with its
private admission occurrence. -/
theorem sourceAfterProofActionFinish_precedes_generic_finish :
    sourceAfterProofActionFinishDirective.rule.priority <
      sourceActionFinishDirective.rule.priority := by
  decide

/-! ## One continuous proof-gated action run -/

private def sourceAfterProofThreadedCanaryPayload : Atom :=
  .expression
    [.symbol "mm-assertion-header", sourceAfterProofCanaryOwner, natAtom 0,
      stringAtom "after-proof-canary", natAtom 0]

private def sourceAfterProofThreadedCanaryAction : RuntimeAction :=
  .add sourceAfterProofThreadedCanaryPayload

private def sourceAfterProofThreadedCanaryActionRows : List Atom :=
  runtimeActionRowsFrom
      (sourceActionOwner sourceAfterProofCanaryOwner 5) 0
      [sourceAfterProofThreadedCanaryAction] ++
    indexSuccessorRows (sourceActionOwner sourceAfterProofCanaryOwner 5) 1

/-- A deliberately small whole machine: the exact proof-success release,
the source-derived post-proof plan, its one state mutation, and the three
rules required to thread them into admission. -/
private def sourceAfterProofThreadedCanaryProgram : List Atom :=
  [sourceAfterProofActionStartRule, sourceActionAddRule,
    sourceAfterProofActionFinishRule,
    sourceAfterProofCanaryRelease sourceAfterProofCanaryOwner,
    sourceAfterProofCanaryPlan sourceAfterProofCanaryOwner] ++
    sourceAfterProofThreadedCanaryActionRows

private def sourceAfterProofThreadedCanaryAdmission : Atom :=
  .expression
    [.symbol "mm-source-theorem-admitted", sourceAfterProofCanaryOwner,
      natAtom 5, .symbol "statement", .symbol "proof-occurrence"]

/-- The assembled runner—not three separately constructed phase spaces—adds
the source-state row, publishes theorem admission, and restores the exact next
source cursor. -/
theorem sourceAfterProofThreadedCanary_completes :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 10
        sourceAfterProofThreadedCanaryProgram).1
    sourceAfterProofThreadedCanaryPayload ∈ final ∧
      sourceAfterProofThreadedCanaryAdmission ∈ final ∧
      sourceControlAtom sourceAfterProofCanaryOwner 6 ∈ final := by
  decide +kernel

/-- Prepared post-proof data alone is inert: without the exact release
occurrence, the same bounded assembled runner cannot publish admission. -/
theorem sourceAfterProofThreadedCanary_without_release_does_not_admit :
    sourceAfterProofThreadedCanaryAdmission ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 10
        (sourceAfterProofThreadedCanaryProgram.erase
          (sourceAfterProofCanaryRelease sourceAfterProofCanaryOwner))).1 := by
  decide +kernel

/-- A release cannot skip a malformed action stream: removing the explicit
successor witness prevents both the mutation and the final admission. -/
theorem sourceAfterProofThreadedCanary_without_successor_does_not_admit :
    sourceAfterProofThreadedCanaryAdmission ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 10
        (sourceAfterProofThreadedCanaryProgram.erase
          (.expression
            [.symbol "mm-index-successor",
              sourceActionOwner sourceAfterProofCanaryOwner 5,
              natAtom 0, natAtom 1]))).1 := by
  decide +kernel

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

/-! ## Explicit floating-typecode comparison -/

private def normalFloatingTypecodeBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label", .var "hyp-position",
      .var "hyp-end", .var "stack-position", .var "stack-base"]

private def normalFloatingTypecodeHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
      .var "hyp-position",
      .expression
        [.symbol "mm-floating", .var "hyp-label", .var "expected-typecode",
          .var "variable-name"]]

private def normalFloatingTypecodeHypothesisSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-hypothesis-successor", .var "scope",
      .var "label", .var "hyp-position", .var "next-hyp-position"]

private def normalFloatingTypecodeStackSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof", .var "stack-position",
      .var "next-stack-position"]

private def normalFloatingTypecodeStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
      .expression
        [.symbol "mm-formula", .var "actual-typecode", .var "body"],
      .var "child-occurrence"]

private def normalFloatingTypecodeCheckTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-floating-typecode-check",
      .var "scope", .var "proof", .var "pc", .var "next-pc",
      .var "label", .var "hyp-position", .var "hyp-end",
      .var "stack-position", .var "stack-base",
      .var "next-hyp-position", .var "next-stack-position",
      .var "hyp-label", .var "expected-typecode", .var "variable-name",
      .var "actual-typecode", .var "body", .var "child-occurrence"]

private def normalFloatingExpectedTypecodeCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-floating-typecode-candidate", .var "proof",
      .var "pc", .var "expected-typecode"]

private def normalFloatingActualTypecodeCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-floating-typecode-candidate", .var "proof",
      .var "pc", .var "actual-typecode"]

private def normalFloatingTypecodePrepareSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodePrepareLocation,
      .var "floating-typecode-prepare-input",
      .var "floating-typecode-prepare-output"]

private def normalFloatingTypecodePreparePatternAtoms : List Atom :=
  [normalFloatingTypecodePrepareSelfTemplate,
   normalFloatingTypecodeBindTemplate,
   normalFloatingTypecodeHypothesisTemplate,
   normalFloatingTypecodeHypothesisSuccessorTemplate,
   normalFloatingTypecodeStackSuccessorTemplate,
   normalFloatingTypecodeStackTemplate]

private def normalFloatingTypecodePrepareInput : Atom :=
  .expression (.symbol "," :: normalFloatingTypecodePreparePatternAtoms)

private def normalFloatingTypecodePrepareSinks : List Sink :=
  [.remove normalFloatingTypecodeBindTemplate,
   .add normalFloatingTypecodeCheckTemplate,
   .add normalFloatingExpectedTypecodeCandidateTemplate,
   .add normalFloatingActualTypecodeCandidateTemplate]

private def normalFloatingTypecodePrepareOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalFloatingTypecodeBindTemplate],
      .expression [.symbol "+", normalFloatingTypecodeCheckTemplate],
      .expression
        [.symbol "+", normalFloatingExpectedTypecodeCandidateTemplate],
      .expression
        [.symbol "+", normalFloatingActualTypecodeCandidateTemplate]]

/-- Materialize the two ground typecodes before a floating-hypothesis bind.
The original bind marker is consumed, so neither success nor failure can be
bypassed by the older equality-only transition. -/
def normalFloatingTypecodePrepareRule : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodePrepareLocation,
      normalFloatingTypecodePrepareInput,
      normalFloatingTypecodePrepareOutput]

def normalFloatingTypecodePrepareDirective : SourceExecFact where
  atom := normalFloatingTypecodePrepareRule
  loc := normalFloatingTypecodePrepareLocation
  rule :=
    { priority := 3
      name := "mm-normal-floating-typecode-prepare"
      input := .compat (mkPattern normalFloatingTypecodePreparePatternAtoms)
      guards := []
      tmpl := mkTemplate normalFloatingTypecodePrepareSinks }

theorem extract_normalFloatingTypecodePrepareRule_exact :
    extractSupportedSourceExecFact normalFloatingTypecodePrepareRule =
      some normalFloatingTypecodePrepareDirective := by
  rfl

private def normalFloatingTypecodeEqualSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodeEqualLocation,
      .var "floating-typecode-equal-input",
      .var "floating-typecode-equal-output"]

private def normalFloatingTypecodeEqualCheckTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-floating-typecode-check",
      .var "scope", .var "proof", .var "pc", .var "next-pc",
      .var "label", .var "hyp-position", .var "hyp-end",
      .var "stack-position", .var "stack-base",
      .var "next-hyp-position", .var "next-stack-position",
      .var "hyp-label", .var "typecode", .var "variable-name",
      .var "typecode", .var "body", .var "child-occurrence"]

private def normalFloatingTypecodeEqualStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
      .expression [.symbol "mm-formula", .var "typecode", .var "body"],
      .var "child-occurrence"]

private def normalFloatingTypecodeEqualCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-normal-floating-typecode-candidate", .var "proof",
      .var "pc", .var "typecode"]

private def normalFloatingTypecodeNextBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base"]

private def normalFloatingTypecodeSubstitutionTemplate : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "body"]

private def normalFloatingTypecodeChildTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-child", .var "proof", .var "pc",
      .var "hyp-position", .var "child-occurrence"]

private def normalFloatingTypecodeReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]

private def normalFloatingTypecodeEqualPatternAtoms : List Atom :=
  [normalFloatingTypecodeEqualSelfTemplate,
   normalFloatingTypecodeEqualCheckTemplate,
   normalFloatingTypecodeEqualStackTemplate,
   normalFloatingTypecodeEqualCandidateTemplate]

private def normalFloatingTypecodeEqualInput : Atom :=
  .expression (.symbol "," :: normalFloatingTypecodeEqualPatternAtoms)

private def normalFloatingTypecodeEqualSinks : List Sink :=
  [.remove normalFloatingTypecodeEqualCheckTemplate,
   .remove normalFloatingTypecodeEqualStackTemplate,
   .remove normalFloatingTypecodeEqualCandidateTemplate,
   .add normalFloatingTypecodeNextBindTemplate,
   .add normalFloatingTypecodeSubstitutionTemplate,
   .add normalFloatingTypecodeChildTemplate,
   .add normalFloatingTypecodeReloadTemplate]

private def normalFloatingTypecodeEqualOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalFloatingTypecodeEqualCheckTemplate],
      .expression [.symbol "-", normalFloatingTypecodeEqualStackTemplate],
      .expression [.symbol "-", normalFloatingTypecodeEqualCandidateTemplate],
      .expression [.symbol "+", normalFloatingTypecodeNextBindTemplate],
      .expression [.symbol "+", normalFloatingTypecodeSubstitutionTemplate],
      .expression [.symbol "+", normalFloatingTypecodeChildTemplate],
      .expression [.symbol "+", normalFloatingTypecodeReloadTemplate]]

/-- Equal ground typecodes continue with exactly the original floating bind
effects, while also reinstalling the dispatch inventory for the next phase. -/
def normalFloatingTypecodeEqualRule : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodeEqualLocation,
      normalFloatingTypecodeEqualInput, normalFloatingTypecodeEqualOutput]

def normalFloatingTypecodeEqualDirective : SourceExecFact where
  atom := normalFloatingTypecodeEqualRule
  loc := normalFloatingTypecodeEqualLocation
  rule :=
    { priority := 4
      name := "mm-normal-floating-typecode-equal"
      input := .compat (mkPattern normalFloatingTypecodeEqualPatternAtoms)
      guards := []
      tmpl := mkTemplate normalFloatingTypecodeEqualSinks }

theorem extract_normalFloatingTypecodeEqualRule_exact :
    extractSupportedSourceExecFact normalFloatingTypecodeEqualRule =
      some normalFloatingTypecodeEqualDirective := by
  rfl

private def normalFloatingTypecodeFaultSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodeFaultLocation,
      .var "floating-typecode-fault-input",
      .var "floating-typecode-fault-output"]

private def normalFloatingTypecodeFaultFactors : List SourceFactor :=
  [.btm normalFloatingTypecodeFaultSelfTemplate,
   .btm normalFloatingTypecodeCheckTemplate,
   .btm normalFloatingTypecodeStackTemplate,
   .neqConstraint normalFloatingExpectedTypecodeCandidateTemplate
      normalFloatingActualTypecodeCandidateTemplate]

private def normalFloatingTypecodeFaultInput : Atom :=
  .expression
    [.symbol "I",
      .expression [.symbol "BTM", normalFloatingTypecodeFaultSelfTemplate],
      .expression [.symbol "BTM", normalFloatingTypecodeCheckTemplate],
      .expression [.symbol "BTM", normalFloatingTypecodeStackTemplate],
      .expression
        [.symbol "!=", normalFloatingExpectedTypecodeCandidateTemplate,
          normalFloatingActualTypecodeCandidateTemplate]]

private def normalFloatingTypecodeFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope", .var "proof", .var "pc",
      .symbol "typecode-mismatch", .var "label",
      .var "expected-typecode", .var "actual-typecode"]

private def normalFloatingTypecodeFaultSinks : List Sink :=
  [.remove normalFloatingTypecodeCheckTemplate,
   .remove normalFloatingTypecodeStackTemplate,
   .remove normalFloatingExpectedTypecodeCandidateTemplate,
   .remove normalFloatingActualTypecodeCandidateTemplate,
   .add normalFloatingTypecodeFaultTemplate]

private def normalFloatingTypecodeFaultOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalFloatingTypecodeCheckTemplate],
      .expression [.symbol "-", normalFloatingTypecodeStackTemplate],
      .expression
        [.symbol "-", normalFloatingExpectedTypecodeCandidateTemplate],
      .expression
        [.symbol "-", normalFloatingActualTypecodeCandidateTemplate],
      .expression [.symbol "+", normalFloatingTypecodeFaultTemplate]]

/-- Distinct ground typecodes have a constructive MM2 mismatch witness and
produce an explicit proof fault rather than a quiescent bind state. -/
def normalFloatingTypecodeFaultRule : Atom :=
  .expression
    [.symbol "exec", normalFloatingTypecodeFaultLocation,
      normalFloatingTypecodeFaultInput, normalFloatingTypecodeFaultOutput]

def normalFloatingTypecodeFaultDirective : SourceExecFact where
  atom := normalFloatingTypecodeFaultRule
  loc := normalFloatingTypecodeFaultLocation
  rule :=
    { priority := 4
      name := "mm-normal-floating-typecode-fault"
      input := .explicit normalFloatingTypecodeFaultFactors
      guards := []
      tmpl := mkTemplate normalFloatingTypecodeFaultSinks }

theorem extract_normalFloatingTypecodeFaultRule_exact :
    extractSupportedSourceExecFact normalFloatingTypecodeFaultRule =
      some normalFloatingTypecodeFaultDirective := by
  rfl

private def normalFloatingTypecodeCheckCanary
    (expected actual : String) : Atom :=
  .expression
    [.symbol "mm-assertion-floating-typecode-check",
      .symbol "scope", .symbol "proof", natAtom 3, natAtom 4,
      stringAtom "assertion", natAtom 0, natAtom 1, natAtom 0, natAtom 0,
      natAtom 1, natAtom 1, stringAtom "hyp", stringAtom expected,
      stringAtom "x", stringAtom actual, .expression [.symbol "mm-nil"],
      natAtom 0]

/-- Positive control: the continuation pattern accepts equal typecodes. -/
theorem normalFloatingTypecodeEqualPattern_matches_equal_canary :
    (cmatchAtom [] normalFloatingTypecodeEqualCheckTemplate
      (normalFloatingTypecodeCheckCanary "wff" "wff")).isSome = true := by
  decide +kernel

/-- Negative control: the equality continuation cannot accept a mismatched
typecode pair; the explicit fault rule owns that case. -/
theorem normalFloatingTypecodeEqualPattern_rejects_mismatch_canary :
    cmatchAtom [] normalFloatingTypecodeEqualCheckTemplate
      (normalFloatingTypecodeCheckCanary "wff" "class") = none := by
  decide +kernel

private def normalFloatingTypecodeFaultCanaryStack : Atom :=
  .expression
    [.symbol "mm-stack-cell", .symbol "proof", natAtom 0,
      .expression
        [.symbol "mm-formula", stringAtom "class",
          .expression [.symbol "mm-nil"]],
      natAtom 0]

private def normalFloatingTypecodeFaultCanaryExpected : Atom :=
  .expression
    [.symbol "mm-normal-floating-typecode-candidate", .symbol "proof",
      natAtom 3, stringAtom "wff"]

private def normalFloatingTypecodeFaultCanaryActual : Atom :=
  .expression
    [.symbol "mm-normal-floating-typecode-candidate", .symbol "proof",
      natAtom 3, stringAtom "class"]

private def normalFloatingTypecodeFaultCanaryObservation : Atom :=
  .expression
    [.symbol "mm-proof-fault", .symbol "scope", .symbol "proof", natAtom 3,
      .symbol "typecode-mismatch", stringAtom "assertion",
      stringAtom "wff", stringAtom "class"]

private def normalFloatingTypecodeFaultCanaryAtoms : List Atom :=
  [normalFloatingTypecodeFaultRule,
   normalFloatingTypecodeCheckCanary "wff" "class",
   normalFloatingTypecodeFaultCanaryStack,
   normalFloatingTypecodeFaultCanaryExpected,
   normalFloatingTypecodeFaultCanaryActual]

private theorem normalFloatingTypecodeFaultCanary_nodup :
    normalFloatingTypecodeFaultCanaryAtoms.Nodup := by
  decide +kernel

private theorem normalFloatingTypecodeFaultCanary_supported_singleton :
    cSupportedSourceExecFacts normalFloatingTypecodeFaultCanaryAtoms =
      [normalFloatingTypecodeFaultDirective] := by
  decide +kernel

/-- The concrete mismatch transition is observed through the NTT obtained by
running OSLF over the actual reflective MM2 GSLT. -/
theorem normalFloatingTypecodeFaultCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies
      normalFloatingTypecodeFaultCanaryAtoms.toFinset
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact
          normalFloatingTypecodeFaultCanaryAtoms.toFinset
          normalFloatingTypecodeFaultDirective)).pred := by
  exact computable_supported_singleton_inhabits_exact_target
    normalFloatingTypecodeFaultCanaryAtoms
    normalFloatingTypecodeFaultDirective
    normalFloatingTypecodeFaultCanary_nodup
    normalFloatingTypecodeFaultCanary_supported_singleton

/-- The same OSLF-indexed target step contains the explicit ground fault
observation used by the source-position rejection continuation. -/
theorem normalFloatingTypecodeFaultCanary_fires_observation :
    normalFloatingTypecodeFaultCanaryObservation ∈
      fireReflectiveSourceExecFact
        normalFloatingTypecodeFaultCanaryAtoms.toFinset
        normalFloatingTypecodeFaultDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      normalFloatingTypecodeFaultCanaryAtoms
      normalFloatingTypecodeFaultDirective
      normalFloatingTypecodeFaultCanary_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        normalFloatingTypecodeFaultDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        normalFloatingTypecodeFaultCanaryAtoms
        normalFloatingTypecodeFaultDirective
        normalFloatingTypecodeFaultCanary_nodup)
  rw [← agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

/-! ## Explicit disjoint-variable failure observations -/

private def normalDVSameVariableCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "assertion-label", .var "next-pair-position",
      .var "pair-end", .var "variable-name", .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "actual-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVSameVariableFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope", .var "proof", .var "pc",
      .symbol "dv-same-variable", .var "assertion-label",
      .var "variable-name", .var "context"]

private def normalDVSameVariableFaultInput : Atom :=
  .expression [.symbol ",", normalDVSameVariableCursorTemplate]

private def normalDVSameVariableFaultSinks : List Sink :=
  [.remove normalDVSameVariableCursorTemplate,
   .add normalDVSameVariableFaultTemplate]

private def normalDVSameVariableFaultOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalDVSameVariableCursorTemplate],
      .expression [.symbol "+", normalDVSameVariableFaultTemplate]]

/-- A caller cannot satisfy an assertion's DV pair by substituting the same
variable on both sides.  Reusing one pattern variable makes this a positive
MM2 match rather than a closed-world absence test. -/
def normalDVSameVariableFaultRule : Atom :=
  .expression
    [.symbol "exec", normalDVSameVariableFaultLocation,
      normalDVSameVariableFaultInput, normalDVSameVariableFaultOutput]

def normalDVSameVariableFaultDirective : SourceExecFact where
  atom := normalDVSameVariableFaultRule
  loc := normalDVSameVariableFaultLocation
  rule :=
    { priority := 18
      name := "mm-normal-dv-same-variable-fault"
      input := .compat (mkPattern [normalDVSameVariableCursorTemplate])
      guards := []
      tmpl := mkTemplate normalDVSameVariableFaultSinks }

theorem extract_normalDVSameVariableFaultRule_exact :
    extractSupportedSourceExecFact normalDVSameVariableFaultRule =
      some normalDVSameVariableFaultDirective := by
  rfl

private def normalDVFaultCanaryCursor (left right : String) : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .symbol "scope", .symbol "proof",
      natAtom 2, stringAtom "assertion", natAtom 1, natAtom 1,
      stringAtom left, .expression [.symbol "mm-nil"],
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", stringAtom right],
          .expression [.symbol "mm-nil"]],
      .expression [.symbol "mm-nil"],
      .expression [.symbol "mm-nil"], .symbol "context"]

/-- Positive control: equal substituted variables instantiate the explicit
DV-fault pattern. -/
theorem normalDVSameVariableFaultPattern_matches_equal_canary :
    (Conformance.Computable.cmatchAtom []
      normalDVSameVariableCursorTemplate
      (normalDVFaultCanaryCursor "z" "z")).isSome = true := by
  decide +kernel

/-- Negative control: distinct substituted variables do not instantiate the
equal-variable fault pattern.  Their general DV obligation remains governed by
the caller-DV relation. -/
theorem normalDVSameVariableFaultPattern_rejects_distinct_canary :
    Conformance.Computable.cmatchAtom []
      normalDVSameVariableCursorTemplate
      (normalDVFaultCanaryCursor "x" "y") = none := by
  decide +kernel

private def normalDVFailureReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalDVFailureReloadLocation,
      .var "dv-failure-reload-input", .var "dv-failure-reload-output"]

private def normalDVFailureReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-dv", .var "dv-failure-proof",
      .var "dv-failure-pc"]

private def normalDVFailureReloadInput : Atom :=
  .expression
    [.symbol ",", normalDVFailureReloadSelfTemplate,
      normalDVFailureReloadTriggerTemplate]

private def normalDVFailureReloadSinks
    (base : NormalProofRuleInventory) : List Sink :=
  [.add normalDVFailureReloadSelfTemplate,
   .remove normalDVFailureReloadTriggerTemplate,
   .add base.dvPairBegin,
   .add base.dvLeftConst,
   .add base.dvLeftVariable,
   .add base.dvRightConst,
   .add base.dvRightVariable,
   .add normalDVSameVariableFaultRule,
   .add base.dvRightNil,
   .add base.dvLeftNil,
   .add base.dvComplete]

private def normalDVFailureReloadOutput
    (base : NormalProofRuleInventory) : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", normalDVFailureReloadSelfTemplate],
      .expression [.symbol "-", normalDVFailureReloadTriggerTemplate],
      .expression [.symbol "+", base.dvPairBegin],
      .expression [.symbol "+", base.dvLeftConst],
      .expression [.symbol "+", base.dvLeftVariable],
      .expression [.symbol "+", base.dvRightConst],
      .expression [.symbol "+", base.dvRightVariable],
      .expression [.symbol "+", normalDVSameVariableFaultRule],
      .expression [.symbol "+", base.dvRightNil],
      .expression [.symbol "+", base.dvLeftNil],
      .expression [.symbol "+", base.dvComplete]]

/-- Reload the ordinary DV cases together with the authored equal-variable
failure case.  Its location precedes the existing generic reload at `22`, so
the same reload request is consumed exactly once by this extension. -/
def normalDVFailureReloadRule (base : NormalProofRuleInventory) : Atom :=
  .expression
    [.symbol "exec", normalDVFailureReloadLocation,
      normalDVFailureReloadInput, normalDVFailureReloadOutput base]

def normalDVFailureReloadDirective
    (base : NormalProofRuleInventory) : SourceExecFact where
  atom := normalDVFailureReloadRule base
  loc := normalDVFailureReloadLocation
  rule :=
    { priority := 21
      name := "mm-normal-dv-failure-reload"
      input := .compat
        (mkPattern
          [normalDVFailureReloadSelfTemplate,
           normalDVFailureReloadTriggerTemplate])
      guards := []
      tmpl := mkTemplate (normalDVFailureReloadSinks base) }

theorem extract_normalDVFailureReloadRule_exact
    (base : NormalProofRuleInventory) :
    extractSupportedSourceExecFact (normalDVFailureReloadRule base) =
      some (normalDVFailureReloadDirective base) := by
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
   sourceTheoremRejectActualCandidateTemplate,
   sourceAfterProofActionPlanTemplate]

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
   .remove sourceAfterProofActionPlanTemplate,
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
      .expression [.symbol "-", sourceAfterProofActionPlanTemplate],
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

/-- A wrong-conclusion verdict consumes the exact deferred delta of the same
theorem occurrence, so rejected input cannot leave a dormant action plan in
the terminal source state. -/
theorem sourceTheoremReject_requires_afterProof_plan :
    sourceAfterProofActionPlanTemplate ∈ sourceTheoremRejectPatternAtoms := by
  simp [sourceTheoremRejectPatternAtoms]

theorem sourceTheoremReject_removes_afterProof_plan :
    .remove sourceAfterProofActionPlanTemplate ∈ sourceTheoremRejectSinks := by
  simp [sourceTheoremRejectSinks]

private def sourceTheoremFaultRejectSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceTheoremFaultRejectLocation,
      .var "source-fault-input", .var "source-fault-output"]

private def sourceTheoremProofFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "source", .var "proof-owner",
      .var "fault-pc", .var "fault-reason",
      .var "fault-assertion-label", .var "fault-left",
      .var "fault-right"]

private def sourceTheoremFaultRejectedTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-rejected", .var "source",
      .var "position", sourceTheoremRejectStatementTemplate,
      .var "fault-reason", .var "fault-assertion-label",
      .var "fault-left", .var "fault-right"]

private def sourceTheoremFaultRejectPatternAtoms : List Atom :=
  [sourceTheoremFaultRejectSelfTemplate,
   sourceTheoremRejectPendingTemplate,
   sourceTheoremRejectContextTemplate,
   sourceTheoremProofFaultTemplate,
   sourceTheoremRejectPreparedHeaderTemplate,
   sourceAfterProofActionPlanTemplate]

private def sourceTheoremFaultRejectInput : Atom :=
  .expression (.symbol "," :: sourceTheoremFaultRejectPatternAtoms)

private def sourceTheoremFaultRejectSinks : List Sink :=
  [.add sourceTheoremFaultRejectSelfTemplate,
   .remove sourceTheoremRejectPendingTemplate,
   .remove sourceTheoremRejectContextTemplate,
   .remove sourceTheoremProofFaultTemplate,
   .remove sourceTheoremRejectPreparedHeaderTemplate,
   .remove sourceAfterProofActionPlanTemplate,
   .add sourceTheoremFaultRejectedTemplate]

private def sourceTheoremFaultRejectOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceTheoremFaultRejectSelfTemplate],
      .expression [.symbol "-", sourceTheoremRejectPendingTemplate],
      .expression [.symbol "-", sourceTheoremRejectContextTemplate],
      .expression [.symbol "-", sourceTheoremProofFaultTemplate],
      .expression [.symbol "-", sourceTheoremRejectPreparedHeaderTemplate],
      .expression [.symbol "-", sourceAfterProofActionPlanTemplate],
      .expression [.symbol "+", sourceTheoremFaultRejectedTemplate]]

/-- Reflect an explicit proof-machine fault through the exact pending theorem
occurrence.  Unlike wrong-conclusion rejection, this path needs no final stack
candidate because the assertion application itself was unauthorized. -/
def sourceTheoremFaultRejectRule : Atom :=
  .expression
    [.symbol "exec", sourceTheoremFaultRejectLocation,
      sourceTheoremFaultRejectInput, sourceTheoremFaultRejectOutput]

def sourceTheoremFaultRejectDirective : SourceExecFact where
  atom := sourceTheoremFaultRejectRule
  loc := sourceTheoremFaultRejectLocation
  rule :=
    { priority := 33
      name := "mm-source-theorem-proof-fault"
      input := .compat (mkPattern sourceTheoremFaultRejectPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceTheoremFaultRejectSinks }

theorem extract_sourceTheoremFaultRejectRule_exact :
    extractSupportedSourceExecFact sourceTheoremFaultRejectRule =
      some sourceTheoremFaultRejectDirective := by
  rfl

/-- A proof-machine fault has the same cleanup obligation as a mismatched
final conclusion: its exact deferred theorem delta is consumed, never
released. -/
theorem sourceTheoremFaultReject_requires_afterProof_plan :
    sourceAfterProofActionPlanTemplate ∈ sourceTheoremFaultRejectPatternAtoms := by
  simp [sourceTheoremFaultRejectPatternAtoms]

theorem sourceTheoremFaultReject_removes_afterProof_plan :
    .remove sourceAfterProofActionPlanTemplate ∈ sourceTheoremFaultRejectSinks := by
  simp [sourceTheoremFaultRejectSinks]

/-! ## Verifier-owned rule reinstallation -/

/-- Source scheduling consumes even an `exec` whose pattern does not match.
These are exactly the database-independent rules needed again at the next
source occurrence. -/
private def sourceVerifierReloadableBaseRules
    (base : NormalProofRuleInventory) : List Atom :=
  [sourceEventDispatchRule, sourceTheoremStartRule,
   sourceTheoremSuccessRule, sourceTheoremRejectRule,
   sourceTheoremFaultRejectRule,
   sourceTheoremCommitRule,
   sourceActionStartRule, sourceAfterProofActionStartRule,
   sourceActionAddRule, sourceActionRemoveRule, sourceActionFinishRule,
   sourceAfterProofActionFinishRule,
   sourceNormalProofActivateRule,
   base.dispatchReload]

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

/-! ### Reloadable verifier extensions

The source scheduler may consume an unmatched executable rule.  A guest
verifier extension consequently has to supply its source-level activation
rules twice: once for the initial program and once as verifier-owned rows
which the existing reload transition can reinstall.  This is deliberately a
small inventory seam: it does not grant source data the ability to author
rules, and it is reusable by independent proof-machine extensions. -/

/-- Verifier-owned source rules, including an explicit finite extension that
is reinstalled after each source-action reload. -/
def sourceVerifierReloadableRulesWith
    (base : NormalProofRuleInventory) (extensionRules : List Atom) : List Atom :=
  sourceVerifierReloadableBaseRules base ++ extensionRules ++
    [sourceVerifierReloadRule]

def sourceVerifierReloadableRules
    (base : NormalProofRuleInventory) : List Atom :=
  sourceVerifierReloadableRulesWith base []

def sourceVerifierRuleRows (base : NormalProofRuleInventory) : List Atom :=
  (sourceVerifierReloadableRules base).map sourceVerifierRuleRow

/-- Verifier-owned reload rows for an explicit finite source-rule extension. -/
def sourceVerifierRuleRowsWith
    (base : NormalProofRuleInventory) (extensionRules : List Atom) : List Atom :=
  (sourceVerifierReloadableRulesWith base extensionRules).map sourceVerifierRuleRow

/-- The current normal dispatcher relation omits its terminal observer even
though MM2 may consume that observer before an assertion macro-step finishes.
The extension retains the existing accept rule as verifier-owned inert code
so the existing normal reloader can restore it with the other proof rules. -/
def normalTerminalReloadRows
    (base : NormalProofRuleInventory) : List Atom :=
  [base.dispatchRuleRow normalFloatingTypecodePrepareRule,
   base.dispatchRuleRow normalFloatingTypecodeEqualRule,
   base.dispatchRuleRow normalFloatingTypecodeFaultRule,
   base.dispatchRuleRow (normalDVFailureReloadRule base),
   base.dispatchRuleRow sourceTheoremFaultRejectRule,
   base.dispatchRuleRow normalComparePrepareRule,
   base.dispatchRuleRow base.accept,
   base.dispatchRuleRow normalRejectRule,
   base.dispatchRuleRow sourceTheoremRejectRule]

def orderedSourceActionRules : List Atom :=
  [sourceActionStartRule, sourceAfterProofActionStartRule,
   sourceActionAddRule, sourceActionRemoveRule, sourceActionFinishRule,
   sourceAfterProofActionFinishRule,
   sourceNormalProofActivateRule,
   sourceVerifierReloadRule]

/-- Initial executable source rules for a finite verifier extension.  The
same extension must also be present in `sourceVerifierRuleRowsWith`, so an
unmatched startup rule is recoverable through the ordinary reload protocol. -/
def orderedSourceActionRulesWith (extensionRules : List Atom) : List Atom :=
  orderedSourceActionRules ++ extensionRules

def orderedSourceActionDirectives : List SourceExecFact :=
  [sourceActionStartDirective, sourceAfterProofActionStartDirective,
   sourceActionAddDirective, sourceActionRemoveDirective,
   sourceActionFinishDirective, sourceAfterProofActionFinishDirective,
   sourceNormalProofActivateDirective, sourceVerifierReloadDirective]

def sourceVerdictRules (base : NormalProofRuleInventory) : List Atom :=
  [normalFloatingTypecodePrepareRule,
   normalFloatingTypecodeEqualRule, normalFloatingTypecodeFaultRule,
   normalDVFailureReloadRule base, normalDVSameVariableFaultRule,
   sourceTheoremFaultRejectRule, normalComparePrepareRule,
   normalRejectRule, sourceTheoremRejectRule]

def sourceActionVerifierExtensionProgramWith
    (base : NormalProofRuleInventory) (extensionRules : List Atom) : List Atom :=
  normalTerminalReloadRows base ++
    sourceVerifierRuleRowsWith base extensionRules ++
      orderedSourceActionRulesWith extensionRules ++ sourceVerdictRules base

def sourceActionVerifierExtensionProgram
    (base : NormalProofRuleInventory) : List Atom :=
  sourceActionVerifierExtensionProgramWith base []

theorem orderedSourceActionRules_extract_exact :
    orderedSourceActionRules.filterMap extractSupportedSourceExecFact =
      orderedSourceActionDirectives := by
  rfl

/-! ## Assertion-header capability audit -/

/-- The complete current assertion-entry inventory names an assertion header
as an input premise.  Support rows without that header cannot start either
assertion application route. -/
theorem normalAssertionEntryRules_require_header
    (base : NormalProofRuleInventory) :
    [base.assertionStart, base.assertionBegin].all
      (execInputRequiresHead "mm-assertion-header") = true := by
  simp [base.assertionStartRequiresHeader,
    base.assertionBeginRequiresHeader]

/-- Negative control: a non-assertion hypothesis transition does not satisfy
the assertion-header entry audit accidentally. -/
theorem normalHypothesisStepRule_does_not_require_assertion_header
    (base : NormalProofRuleInventory) :
    execInputRequiresHead "mm-assertion-header" base.hypothesisStep =
      false := by
  exact base.hypothesisStepDoesNotRequireHeader

end Mettapedia.Languages.Metamath.MM2SourceActionExecution
