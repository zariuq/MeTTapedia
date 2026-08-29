import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
import Mettapedia.Languages.Metamath.MM2SourceEventTransformation
import Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-!
# Occurrence-indexed action-kind dispatch for Metamath source deltas

An admitted source action is passive data.  Its payload is still checked by
the verifier-owned add or remove rule; this small presentation only records
which of those two rules may be activated at an explicit action occurrence.
It therefore supplies a finite, order-preserving dispatch input without
turning a source row into executable code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-- The finite verifier rule family selected by one source-derived runtime
action.  The payload itself remains outside this tag and is checked by the
selected action rule. -/
def runtimeActionKind : RuntimeAction → Atom
  | .add _ => .symbol "mm-source-action-add"
  | .remove _ => .symbol "mm-source-action-remove"

/-- A passive action-kind row is indexed by the source plan owner and exact
action occurrence. -/
def runtimeActionKindRow (actionOwner : Atom) (position : Nat)
    (action : RuntimeAction) : Atom :=
  .expression
    [.symbol "mm-source-action-kind", actionOwner, natAtom position,
      runtimeActionKind action]

/-- Emit one action-kind row for each action occurrence, preserving duplicate
actions at distinct positions. -/
def runtimeActionKindRowsFrom (actionOwner : Atom) :
    Nat → List RuntimeAction → List Atom
  | _, [] => []
  | position, action :: actions =>
      runtimeActionKindRow actionOwner position action ::
        runtimeActionKindRowsFrom actionOwner (position + 1) actions

@[simp] theorem runtimeActionKindRowsFrom_length (actionOwner : Atom)
    (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionKindRowsFrom actionOwner position actions).length =
      actions.length := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp [runtimeActionKindRowsFrom, induction]

@[simp] theorem runtimeActionKindRowsFrom_all_proofNeutral
    (actionOwner : Atom) (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionKindRowsFrom actionOwner position actions).all
      isProofNeutralInitialAtom = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp [runtimeActionKindRowsFrom, runtimeActionKindRow,
        isProofNeutralInitialAtom, isVerifierTerminalObservation,
        isVerifierOwnedInternalRowShape,
        Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
        induction]

/-- The kind stream corresponding to a single source statement action plan. -/
def statementActionPlanActionKindRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  runtimeActionKindRowsFrom (sourceActionOwner owner plan.position) 0
    plan.actions

/-- The source-derived passive action-kind stream for all admitted plans. -/
def admittedSourceActionPlanActionKindRows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) : List Atom :=
  input.plans.flatMap (statementActionPlanActionKindRows owner)

@[simp] theorem statementActionPlanActionKindRows_all_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    (statementActionPlanActionKindRows owner plan).all
      isProofNeutralInitialAtom = true := by
  simp [statementActionPlanActionKindRows]

@[simp] theorem admittedSourceActionPlanActionKindRows_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    (admittedSourceActionPlanActionKindRows input).all
      isProofNeutralInitialAtom = true := by
  simp [admittedSourceActionPlanActionKindRows,
    statementActionPlanActionKindRows]

/-! ## Verifier-owned finite action dispatch -/

private def sourceActionKindDispatchLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-action-kind-dispatch"]

private def sourceActionKindDispatchSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceActionKindDispatchLocation,
      .var "source-action-kind-dispatch-input",
      .var "source-action-kind-dispatch-output"]

private def sourceActionRunningTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-running", .var "source", .var "position",
      .var "next-position", .var "statement", .var "dispatch-input",
      .var "dispatch-output", .var "action-position", .var "action-count"]

private def sourceActionKindRowTemplate : Atom :=
  .expression
    [.symbol "mm-source-action-kind",
      .expression [.symbol "mm-source-action-owner", .var "source",
        .var "position"],
      .var "action-position", .var "action-kind"]

/-- Verifier-owned association from a passive finite action kind to an opaque
executable handler. -/
def sourceActionKindHandlerRow (kind rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-action-kind-rule", kind, rule]

private def sourceActionKindHandlerTemplate : Atom :=
  .expression [.symbol "mm-internal-source-action-kind-rule",
    .var "action-kind", .var "action-handler-rule"]

private def sourceActionKindDispatchPatternAtoms : List Atom :=
  [sourceActionKindDispatchSelfTemplate, sourceActionRunningTemplate,
    sourceActionKindRowTemplate, sourceActionKindHandlerTemplate]

private def sourceActionKindDispatchInput : Atom :=
  .expression (.symbol "," :: sourceActionKindDispatchPatternAtoms)

private def sourceActionKindDispatchOutput : Atom :=
  .expression [.symbol "O",
    .expression [.symbol "+", .var "action-handler-rule"]]

/-- Load exactly the handler selected by the source-derived kind at the live
action occurrence.  The selected handler still validates its linked payload
and explicit successor before changing source state. -/
def sourceActionKindDispatchRule : Atom :=
  .expression [.symbol "exec", sourceActionKindDispatchLocation,
    sourceActionKindDispatchInput, sourceActionKindDispatchOutput]

def sourceActionKindDispatchCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-source-action-kind-dispatch",
    .var "source-action-kind-dispatch-rule"]

def sourceActionKindDispatchCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-action-kind-dispatch",
    sourceActionKindDispatchRule]

def sourceActionAfterProofFinishCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-source-action-after-proof-finish",
    .var "source-action-after-proof-finish-rule"]

def sourceActionAfterProofFinishCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-action-after-proof-finish",
    sourceAfterProofActionFinishRule]

private theorem sourceAfterProofActionStartRule_kind_dispatchable :
    (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
      (.var "source-action-kind-dispatch-rule")
      sourceAfterProofActionStartRule).isSome = true := by
  decide +kernel

/-- The proof-gated action start releases a verifier-owned dispatcher rather
than a permanent pair of competing action rules. -/
def sourceAfterProofActionStartRuleWithKindDispatch : Atom :=
  (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
    (.var "source-action-kind-dispatch-rule")
    sourceAfterProofActionStartRule).get
      (by simpa using sourceAfterProofActionStartRule_kind_dispatchable)

private theorem sourceActionAddRule_kind_dispatchable :
    (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
      (.var "source-action-kind-dispatch-rule") sourceActionAddRule).isSome =
      true := by
  decide +kernel

private def sourceActionAddRuleWithKindDispatch : Atom :=
  (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
    (.var "source-action-kind-dispatch-rule") sourceActionAddRule).get
      (by simpa using sourceActionAddRule_kind_dispatchable)

private theorem sourceActionAddRule_finish_dispatchable :
    (appendCapturedRuleSink? sourceActionAfterProofFinishCaptureTemplate
      (.var "source-action-after-proof-finish-rule")
      sourceActionAddRuleWithKindDispatch).isSome = true := by
  decide +kernel

/-- One successful add action makes both the next occurrence dispatcher and
the exact finalizer available.  At a nonfinal cursor the finalizer cannot
match; at the terminal cursor the dispatcher cannot match a further kind. -/
def sourceActionAddRuleWithKindDispatchAndFinish : Atom :=
  (appendCapturedRuleSink? sourceActionAfterProofFinishCaptureTemplate
    (.var "source-action-after-proof-finish-rule")
    sourceActionAddRuleWithKindDispatch).get
      (by simpa using sourceActionAddRule_finish_dispatchable)

private theorem sourceActionRemoveRule_kind_dispatchable :
    (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
      (.var "source-action-kind-dispatch-rule") sourceActionRemoveRule).isSome =
      true := by
  decide +kernel

private def sourceActionRemoveRuleWithKindDispatch : Atom :=
  (appendCapturedRuleSink? sourceActionKindDispatchCaptureTemplate
    (.var "source-action-kind-dispatch-rule") sourceActionRemoveRule).get
      (by simpa using sourceActionRemoveRule_kind_dispatchable)

private theorem sourceActionRemoveRule_finish_dispatchable :
    (appendCapturedRuleSink? sourceActionAfterProofFinishCaptureTemplate
      (.var "source-action-after-proof-finish-rule")
      sourceActionRemoveRuleWithKindDispatch).isSome = true := by
  decide +kernel

/-- The remove branch carries the same occurrence-local continuation shape as
the add branch. -/
def sourceActionRemoveRuleWithKindDispatchAndFinish : Atom :=
  (appendCapturedRuleSink? sourceActionAfterProofFinishCaptureTemplate
    (.var "source-action-after-proof-finish-rule")
    sourceActionRemoveRuleWithKindDispatch).get
      (by simpa using sourceActionRemoveRule_finish_dispatchable)

/-! ## Exact normal-result to source-verdict continuation -/

/-- Opaque verifier-owned continuation from normal proof acceptance into the
source theorem-success transition. -/
def normalAcceptSourceTheoremSuccessCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-normal-source-theorem-success",
    .var "normal-source-theorem-success-rule"]

def sourceTheoremCommitCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-source-theorem-commit",
    .var "source-theorem-commit-rule"]

def sourceAfterProofActionStartCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-source-after-proof-action-start",
    .var "source-after-proof-action-start-rule"]

private theorem normalAcceptRule_source_success_dispatchable :
    (appendCapturedRuleSink? normalAcceptSourceTheoremSuccessCaptureTemplate
      (.var "normal-source-theorem-success-rule") normalAcceptRule).isSome =
      true := by
  decide +kernel

/-- Normal proof acceptance releases precisely the verifier-owned theorem
success continuation.  It does not publish a source verdict itself. -/
def normalAcceptRuleWithSourceTheoremSuccess : Atom :=
  (appendCapturedRuleSink? normalAcceptSourceTheoremSuccessCaptureTemplate
    (.var "normal-source-theorem-success-rule") normalAcceptRule).get
      (by simpa using normalAcceptRule_source_success_dispatchable)

private theorem sourceTheoremSuccessRule_commit_dispatchable :
    (appendCapturedRuleSink? sourceTheoremCommitCaptureTemplate
      (.var "source-theorem-commit-rule") sourceTheoremSuccessRule).isSome =
      true := by
  decide +kernel

def sourceTheoremSuccessRuleWithCommit : Atom :=
  (appendCapturedRuleSink? sourceTheoremCommitCaptureTemplate
    (.var "source-theorem-commit-rule") sourceTheoremSuccessRule).get
      (by simpa using sourceTheoremSuccessRule_commit_dispatchable)

private theorem sourceTheoremCommitRule_after_proof_start_dispatchable :
    (appendCapturedRuleSink? sourceAfterProofActionStartCaptureTemplate
      (.var "source-after-proof-action-start-rule")
      sourceTheoremCommitRule).isSome = true := by
  decide +kernel

def sourceTheoremCommitRuleWithAfterProofActionStart : Atom :=
  (appendCapturedRuleSink? sourceAfterProofActionStartCaptureTemplate
    (.var "source-after-proof-action-start-rule")
    sourceTheoremCommitRule).get
      (by simpa using sourceTheoremCommitRule_after_proof_start_dispatchable)

def normalAcceptSourceTheoremSuccessCaptureRow : Atom :=
  .expression [.symbol "mm-internal-normal-source-theorem-success",
    sourceTheoremSuccessRuleWithCommit]

/-- The compact terminal has its own source-verdict continuation: compressed
proof execution may return from a normal assertion submachine and then emit
its final `mm-accepted` observation itself. -/
def compressedAcceptSourceTheoremSuccessCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-source-theorem-success",
    .var "compressed-source-theorem-success-rule"]

private theorem compressedAcceptRule_source_success_dispatchable :
    (appendCapturedRuleSink?
      compressedAcceptSourceTheoremSuccessCaptureTemplate
      (.var "compressed-source-theorem-success-rule")
      compressedAcceptRule).isSome = true := by
  decide +kernel

def compressedAcceptRuleWithSourceTheoremSuccess : Atom :=
  (appendCapturedRuleSink?
    compressedAcceptSourceTheoremSuccessCaptureTemplate
    (.var "compressed-source-theorem-success-rule")
    compressedAcceptRule).get
      (by simpa using compressedAcceptRule_source_success_dispatchable)

def compressedAcceptSourceTheoremSuccessCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-source-theorem-success",
    sourceTheoremSuccessRuleWithCommit]

/-- Opaque verifier-owned continuation used by compact proof-fault rules.
The compact rule still determines and emits the fault; this value only makes
the existing owner-bound source rejection transition available at that exact
observation boundary. -/
def compressedProofFaultSourceTheoremRejectCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-source-theorem-fault-reject",
    .var "compressed-source-theorem-fault-reject-rule"]

def compressedProofFaultSourceTheoremRejectCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-source-theorem-fault-reject",
    sourceTheoremFaultRejectRule]

/-- Strict selected-member transform for the compact terminal observation. -/
def replaceCompressedAcceptWithSourceTheoremSuccess? (rules : List Atom) :
    Option (List Atom) :=
  replaceMatching? compressedAcceptRule compressedAcceptRuleWithSourceTheoremSuccess
    rules

def sourceTheoremCommitCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-theorem-commit",
    sourceTheoremCommitRuleWithAfterProofActionStart]

def sourceAfterProofActionStartCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-after-proof-action-start",
    sourceAfterProofActionStartRuleWithKindDispatch]

/-- Strictly replace one normal terminal rule by its source-verdict
continuation.  The surface transformation fails when its selected source rule
is absent, so it cannot quietly append an unrelated terminal path. -/
def replaceNormalAcceptWithSourceTheoremSuccess? (rules : List Atom) :
    Option (List Atom) :=
  replaceMatching? normalAcceptRule normalAcceptRuleWithSourceTheoremSuccess
    rules

/-! ## Source-loop rearming after a deferred normal proof -/

/-- Opaque verifier-owned code for the ordinary source-rule reloader.  A
completed proof-gated source action captures this value only when it also
emits the matching source reload request. -/
def sourceVerifierReloadCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-source-verifier-reload",
    .var "source-verifier-reload-rule"]

def sourceVerifierReloadCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-verifier-reload",
    sourceVerifierReloadRule]

/-- The opaque source reloader is verifier-owned code, never admissible
source input. -/
@[simp] theorem sourceVerifierReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom sourceVerifierReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-verifier-reload" [sourceVerifierReloadRule] (by decide)

private theorem sourceAfterProofActionFinishRule_reloader_capturable :
    (appendCapturedRuleSink? sourceVerifierReloadCaptureTemplate
      (.var "source-verifier-reload-rule")
      sourceAfterProofActionFinishRule).isSome = true := by
  decide +kernel

/-- Releasing the next source cursor after a deferred normal proof also
releases the source-rule reloader that consumes the finish transition's own
reload request.  This prevents a long proof run from leaving the following
declaration or scope action behind an erased one-shot dispatcher. -/
def sourceAfterProofActionFinishRuleWithVerifierReload : Atom :=
  (appendCapturedRuleSink? sourceVerifierReloadCaptureTemplate
    (.var "source-verifier-reload-rule")
    sourceAfterProofActionFinishRule).get
      (by simpa using sourceAfterProofActionFinishRule_reloader_capturable)

/-- Compact-profile capture row for the proof-gated finalizer.  It differs
from the ordinary row only by carrying the opaque source-reloader continuation
needed to process the cursor that follows a long deferred proof run. -/
def sourceAfterProofActionFinishWithVerifierReloadCaptureRow : Atom :=
  .expression [.symbol "mm-internal-source-action-after-proof-finish",
    sourceAfterProofActionFinishRuleWithVerifierReload]

/-- The deferred-action finalizer is likewise an opaque verifier continuation,
not an admissible source row. -/
@[simp] theorem sourceAfterProofActionFinishWithVerifierReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom
      sourceAfterProofActionFinishWithVerifierReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-action-after-proof-finish"
    [sourceAfterProofActionFinishRuleWithVerifierReload] (by decide)

private theorem compressedNormalBaseSourceActionRules_replaceable :
    (replaceMatching? sourceAfterProofActionFinishRule
      sourceAfterProofActionFinishRuleWithVerifierReload
      orderedSourceActionRules).isSome = true := by
  decide +kernel

/-- The direct source-action presentation retains every ordinary rule except
that the proof-gated finalizer uses the verifier-owned reloader capture above.
The extension remains an explicit input to this finite profile. -/
def compressedNormalBaseSourceActionRules : List Atom :=
  (replaceMatching? sourceAfterProofActionFinishRule
    sourceAfterProofActionFinishRuleWithVerifierReload
    orderedSourceActionRules).get
      (by simpa using compressedNormalBaseSourceActionRules_replaceable)

def compressedNormalSourceActionRulesWith
    (extensionRules : List Atom) : List Atom :=
  compressedNormalBaseSourceActionRules ++ extensionRules

private theorem compressedNormalBaseSourceVerifierRules_replaceable :
    (replaceMatching? sourceAfterProofActionFinishRule
      sourceAfterProofActionFinishRuleWithVerifierReload
      (sourceVerifierReloadableRules normalProofMachineRuleInventory)).isSome =
        true := by
  decide +kernel

/-- The reloader's passive rule inventory carries the same transformed
proof-gated finalizer.  Extra finite verifier rules are inserted before the
ordinary reloader, exactly where the existing source profile stores them. -/
def compressedNormalBaseSourceVerifierRules : List Atom :=
  (replaceMatching? sourceAfterProofActionFinishRule
    sourceAfterProofActionFinishRuleWithVerifierReload
    (sourceVerifierReloadableRules normalProofMachineRuleInventory)).get
      (by simpa using compressedNormalBaseSourceVerifierRules_replaceable)

def compressedNormalSourceVerifierRulesWith
    (extensionRules : List Atom) : List Atom :=
  compressedNormalBaseSourceVerifierRules.dropLast ++ extensionRules ++
    [sourceVerifierReloadRule]

theorem compressedNormalBaseSourceActionRules_replaces_only_finish :
    sourceAfterProofActionFinishRule ∉ compressedNormalBaseSourceActionRules ∧
      sourceAfterProofActionFinishRuleWithVerifierReload ∈
        compressedNormalBaseSourceActionRules := by
  decide +kernel

theorem compressedNormalBaseSourceVerifierRules_replaces_only_finish :
    sourceAfterProofActionFinishRule ∉ compressedNormalBaseSourceVerifierRules ∧
      sourceAfterProofActionFinishRuleWithVerifierReload ∈
        compressedNormalBaseSourceVerifierRules := by
  decide +kernel

/-- Compact-profile normal dispatch rows.  The ordinary terminal reload
inventory is retained except that its acceptance rule is the captured
source-verdict continuation rather than the raw normal observation rule. -/
def compressedNormalTerminalReloadRows : List Atom :=
  [normalProofMachineRuleInventory.dispatchRuleRow
     normalFloatingTypecodePrepareRule,
   normalProofMachineRuleInventory.dispatchRuleRow
     normalFloatingTypecodeEqualRule,
   normalProofMachineRuleInventory.dispatchRuleRow
     normalFloatingTypecodeFaultRule,
   normalProofMachineRuleInventory.dispatchRuleRow
     (normalDVFailureReloadRule normalProofMachineRuleInventory),
   normalProofMachineRuleInventory.dispatchRuleRow normalComparePrepareRule,
   normalProofMachineRuleInventory.dispatchRuleRow
     normalAcceptRuleWithSourceTheoremSuccess,
   normalProofMachineRuleInventory.dispatchRuleRow normalRejectRule,
   normalProofMachineRuleInventory.dispatchRuleRow sourceTheoremRejectRule]

/-- The source-action support inventory for the deferred-normal compact
profile.  It differs from the existing extension only at the reloaded normal
acceptance continuation. -/
def compressedNormalSourceActionExtension
    (extensionRules : List Atom) : List Atom :=
  compressedNormalTerminalReloadRows ++
    (compressedNormalSourceVerifierRulesWith extensionRules).map
      sourceVerifierRuleRow ++
      compressedNormalSourceActionRulesWith extensionRules ++
        sourceVerdictRules normalProofMachineRuleInventory ++
          [sourceVerifierReloadCaptureRow]

/-- The finite verifier-owned inventory consumed by the occurrence-indexed
source action dispatcher.  No member is source input. -/
def sourceActionKindDispatchStaticRows : List Atom :=
  [sourceActionKindDispatchCaptureRow,
   sourceAfterProofActionFinishWithVerifierReloadCaptureRow,
   normalAcceptSourceTheoremSuccessCaptureRow,
   compressedAcceptSourceTheoremSuccessCaptureRow,
   compressedProofFaultSourceTheoremRejectCaptureRow,
   sourceTheoremCommitCaptureRow,
   sourceAfterProofActionStartCaptureRow,
   sourceActionKindHandlerRow (.symbol "mm-source-action-add")
     sourceActionAddRuleWithKindDispatchAndFinish,
   sourceActionKindHandlerRow (.symbol "mm-source-action-remove")
     sourceActionRemoveRuleWithKindDispatchAndFinish]

private def kindDispatchCanarySource : Atom := .symbol "source"

private def kindDispatchCanaryRunning : Atom :=
  .expression
    [.symbol "mm-source-action-running", kindDispatchCanarySource,
      natAtom 3, natAtom 4, .symbol "statement", .symbol "dispatch-input",
      .symbol "dispatch-output", natAtom 0, natAtom 1]

private def kindDispatchCanaryKindRow (occurrence : Nat) : Atom :=
  runtimeActionKindRow
    (sourceActionOwner kindDispatchCanarySource 3) occurrence
    (.add (.symbol "payload"))

private def kindDispatchCanaryHandler : Atom :=
  sourceActionKindHandlerRow (.symbol "mm-source-action-add")
    (.symbol "handler")

/-- Positive control: exact source owner, plan, action occurrence, and kind
select the corresponding verifier-owned handler. -/
theorem sourceActionKindDispatch_accepts_exact_canary :
    (cmatchPattern []
      [sourceActionKindDispatchRule, kindDispatchCanaryRunning,
       kindDispatchCanaryKindRow 0, kindDispatchCanaryHandler]
      (mkPattern sourceActionKindDispatchPatternAtoms)).isEmpty = false := by
  decide +kernel

/-- Negative control: a kind row at a different action occurrence cannot
select a handler for the live source action cursor. -/
theorem sourceActionKindDispatch_rejects_foreign_occurrence_canary :
    cmatchPattern []
      [sourceActionKindDispatchRule, kindDispatchCanaryRunning,
       kindDispatchCanaryKindRow 1, kindDispatchCanaryHandler]
      (mkPattern sourceActionKindDispatchPatternAtoms) = [] := by
  decide +kernel

#print axioms runtimeActionKindRowsFrom_all_proofNeutral
#print axioms sourceActionKindDispatch_accepts_exact_canary
#print axioms sourceActionKindDispatch_rejects_foreign_occurrence_canary

end Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
