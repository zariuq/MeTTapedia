import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
import Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
import Mettapedia.Languages.Metamath.SourceStateNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Source-derived Metamath scope execution in ordinary MM2

The authored scope meaning remains `SourceStateGSLT`: opening a scope records
the three active-prefix lengths, while closing it restores exactly those
prefixes and preserves permanent declarations, labels, and assertions.  This
module realizes the same boundary in ordinary MM2.

The MM2 source environment carries a stack of exact frontier checkpoints.
Closing a scope walks each active ledger backwards to its saved frontier.
Variable links are already emitted by native `$v` execution.  Hypothesis and
disjointness links use dedicated row families so their later native
declaration rules can publish and retract proof-runtime rows without changing
the scope protocol.

Scope close currently prepares the active ledgers and restores the source
environment before the residual proof-runtime action plan runs.  This permits
native scope ownership to grow monotonically as `$d`, `$f`, and `$e` move onto
their native routes; it does not treat an empty future ledger as evidence that
those declarations have already been realized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceScopeExecution

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.Metamath.SourceStateNativeTypes
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Authored source meaning and its OSLF-derived native theory -/

/-- Scope transitions are interpreted only by the complete authored source
state GSLT.  This abbreviation exposes the required OSLF stage at the use
site; it does not define a second scope calculus. -/
def sourceScopeOSLF :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
    SourceStateGSLT.theory

/-- The target-indexed native type generated from the authored source-state
GSLT by `sourceScopeOSLF`. -/
def sourceScopeNTT (target : SourceState) : SourceStateNativeType :=
  sourceStateExactTargetNativeType target

theorem openScope_inhabits_source_native_type
    {before after : SourceState}
    (opened : openScope? before = some after) :
    sourceScopeOSLF.satisfies before (sourceScopeNTT after).pred := by
  exact local_payload_inhabits_exact_target (payload := .openScope) (by
    simpa [applyLocalPayload?] using opened)

theorem closeScope_inhabits_source_native_type
    {before after : SourceState}
    (closed : closeScope? before = some after) :
    sourceScopeOSLF.satisfies before (sourceScopeNTT after).pred := by
  exact local_payload_inhabits_exact_target (payload := .closeScope) (by
    simpa [applyLocalPayload?] using closed)

theorem completeBlock_inhabits_source_native_type
    {before after : SourceState}
    (completed : completeBlock? before = some after) :
    sourceScopeOSLF.satisfies before (sourceScopeNTT after).pred := by
  exact local_payload_inhabits_exact_target (payload := .completeBlock) (by
    simpa [applyLocalPayload?] using completed)

theorem openScope_preserves_permanent_state
    {before after : SourceState}
    (opened : openScope? before = some after) :
    after.declaredConstants = before.declaredConstants /\
      after.declaredVariables = before.declaredVariables /\
      after.variableTypecodes = before.variableTypecodes /\
      after.usedLabels = before.usedLabels /\
      after.assertions = before.assertions := by
  rw [openScope?_eq_some_shape opened]
  simp

theorem closeScope_restores_three_active_prefixes
    {before after : SourceState}
    (closed : closeScope? before = some after) :
    exists boundary rest,
      before.scopes = boundary :: rest /\
      after.activeVariables =
        before.activeVariables.take boundary.activeVariableLength /\
      after.activeHypotheses =
        before.activeHypotheses.take boundary.activeHypothesisLength /\
      after.activeDistinctVariables =
        before.activeDistinctVariables.take boundary.activeDistinctLength /\
      after.scopes = rest := by
  obtain ⟨boundary, rest, scopes, shape⟩ :=
    closeScope?_eq_some_shape closed
  refine ⟨boundary, rest, scopes, ?_⟩
  rw [shape]
  simp

theorem closeScope_preserves_permanent_state
    {before after : SourceState}
    (closed : closeScope? before = some after) :
    after.declaredConstants = before.declaredConstants /\
      after.declaredVariables = before.declaredVariables /\
      after.variableTypecodes = before.variableTypecodes /\
      after.usedLabels = before.usedLabels /\
      after.assertions = before.assertions := by
  obtain ⟨boundary, rest, _, shape⟩ := closeScope?_eq_some_shape closed
  rw [shape]
  simp

/-! ## Exact frontier checkpoints -/

structure ScopeCheckpoint where
  activeVariableFrontier : Atom
  activeHypothesisFrontier : Atom
  activeDistinctFrontier : Atom
  dvOccurrenceFrontier : Atom
deriving DecidableEq

def scopeCheckpointAtom (checkpoint : ScopeCheckpoint) : Atom :=
  .expression
    [.symbol "mm-source-scope-checkpoint",
      checkpoint.activeVariableFrontier,
      checkpoint.activeHypothesisFrontier,
      checkpoint.activeDistinctFrontier,
      checkpoint.dvOccurrenceFrontier]

def decodeScopeCheckpointAtom : Atom -> Option ScopeCheckpoint
  | .expression
      [.symbol "mm-source-scope-checkpoint", variableFrontier,
        hypothesisFrontier, distinctFrontier, occurrenceFrontier] =>
      some
        { activeVariableFrontier := variableFrontier
          activeHypothesisFrontier := hypothesisFrontier
          activeDistinctFrontier := distinctFrontier
          dvOccurrenceFrontier := occurrenceFrontier }
  | _ => none

@[simp] theorem decodeScopeCheckpointAtom_scopeCheckpointAtom
    (checkpoint : ScopeCheckpoint) :
    decodeScopeCheckpointAtom (scopeCheckpointAtom checkpoint) =
      some checkpoint := by
  cases checkpoint
  rfl

theorem scopeCheckpointAtom_injective :
    Function.Injective scopeCheckpointAtom := by
  intro left right equal
  have decoded := congrArg decodeScopeCheckpointAtom equal
  simpa using decoded

def activeHypothesisLedgerOwner (owner : Atom) : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", owner]

def activeDistinctLedgerOwner (owner : Atom) : Atom :=
  .expression [.symbol "mm-source-active-distinct-ledger", owner]

def sourceActivityFrontierAtom (ledgerOwner frontier : Atom) : Atom :=
  .expression [.symbol "mm-source-activity-frontier", ledgerOwner, frontier]

/-- Scope-owned classification of one `$d` occurrence.  A first occurrence is
either currently live or inert according to its `$f` endpoints.  A duplicate
shares the capability of the earlier first occurrence and owns no runtime row. -/
inductive ActiveDistinctCapabilityKind where
  | live
  | inert
  | shared
deriving DecidableEq, Repr

def activeDistinctCapabilityKindAtom : ActiveDistinctCapabilityKind → Atom
  | .live => .symbol "mm-source-dv-capability-live"
  | .inert => .symbol "mm-source-dv-capability-inert"
  | .shared => .symbol "mm-source-dv-capability-shared"

def decodeActiveDistinctCapabilityKindAtom :
    Atom → Option ActiveDistinctCapabilityKind
  | .symbol "mm-source-dv-capability-live" => some .live
  | .symbol "mm-source-dv-capability-inert" => some .inert
  | .symbol "mm-source-dv-capability-shared" => some .shared
  | _ => none

@[simp] theorem decodeActiveDistinctCapabilityKindAtom_encoded
    (kind : ActiveDistinctCapabilityKind) :
    decodeActiveDistinctCapabilityKindAtom
      (activeDistinctCapabilityKindAtom kind) = some kind := by
  cases kind <;> rfl

/-- Exactly the three classifications emitted by native `$d` execution. -/
def activeDistinctClassificationValid
    (occurrence : DVOccurrenceKind)
    (capability : ActiveDistinctCapabilityKind) : Bool :=
  match occurrence, capability with
  | .first, .live => true
  | .first, .inert => true
  | .duplicate, .shared => true
  | _, _ => false

@[simp] theorem activeDistinctClassificationValid_first_live :
    activeDistinctClassificationValid .first .live = true := rfl

@[simp] theorem activeDistinctClassificationValid_first_inert :
    activeDistinctClassificationValid .first .inert = true := rfl

@[simp] theorem activeDistinctClassificationValid_duplicate_shared :
    activeDistinctClassificationValid .duplicate .shared = true := rfl

/-- Raw carrier for one active hypothesis occurrence.  The encoded hypothesis
is retained independently of its proof-runtime row: assertion-frame
reconstruction must distinguish `$f` from `$e`, while scope exit must retract
the exact row published at declaration time. -/
def activeHypothesisLinkRawAtom (owner previous next encodedHypothesis
    runtimeRow : Atom) : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link",
      activeHypothesisLedgerOwner owner, previous, next, encodedHypothesis,
      runtimeRow]

/-- Canonical active-hypothesis link.  Its runtime row is derived from the
same semantic hypothesis, so the two views cannot disagree. -/
def activeHypothesisLinkAtom (owner previous next : Atom)
    (hypothesis : HypothesisView) : Atom :=
  activeHypothesisLinkRawAtom owner previous next (hypothesisAtom hypothesis)
    (hypothesisLookupRow owner hypothesis)

structure ActiveHypothesisOccurrence where
  previous : Atom
  next : Atom
  hypothesis : HypothesisView
deriving DecidableEq

/-- Decode only canonical links whose semantic hypothesis and runtime row
agree exactly.  Directly authored rows with inconsistent duplicate views are
rejected. -/
def decodeActiveHypothesisLinkAtom (owner : Atom) :
    Atom -> Option ActiveHypothesisOccurrence
  | .expression
      [.symbol tag, actualLedgerOwner, previous, next, encodedHypothesis,
        runtimeRow] => do
      guard (tag == "mm-source-active-hypothesis-link")
      guard (actualLedgerOwner == activeHypothesisLedgerOwner owner)
      let hypothesis <- decodeHypothesisAtom encodedHypothesis
      guard (runtimeRow == hypothesisLookupRow owner hypothesis)
      pure { previous, next, hypothesis }
  | _ => none

@[simp] theorem decodeActiveHypothesisLinkAtom_activeHypothesisLinkAtom
    (owner previous next : Atom) (hypothesis : HypothesisView) :
    decodeActiveHypothesisLinkAtom owner
        (activeHypothesisLinkAtom owner previous next hypothesis) =
      some { previous, next, hypothesis } := by
  cases hypothesis <;>
    simp [decodeActiveHypothesisLinkAtom, activeHypothesisLinkAtom,
      activeHypothesisLinkRawAtom, hypothesisLookupRow]

theorem decodeActiveHypothesisLinkAtom_eq_none_of_runtime_ne
    (owner previous next runtimeRow : Atom) (hypothesis : HypothesisView)
    (runtime_ne : runtimeRow != hypothesisLookupRow owner hypothesis) :
    decodeActiveHypothesisLinkAtom owner
        (activeHypothesisLinkRawAtom owner previous next
          (hypothesisAtom hypothesis) runtimeRow) = none := by
  have runtime_ne' :
      runtimeRow ≠ hypothesisLookupRow owner hypothesis := by
    simpa [bne_iff_ne] using runtime_ne
  cases hypothesis <;>
    simp [decodeActiveHypothesisLinkAtom, activeHypothesisLinkRawAtom,
      runtime_ne']

theorem activeHypothesisLinkAtom_injective (owner : Atom) :
    Function.Injective (fun occurrence : ActiveHypothesisOccurrence =>
      activeHypothesisLinkAtom owner occurrence.previous occurrence.next
        occurrence.hypothesis) := by
  intro left right equal
  have decoded := congrArg (decodeActiveHypothesisLinkAtom owner) equal
  cases left with
  | mk leftPrevious leftNext leftHypothesis =>
      cases right with
      | mk rightPrevious rightNext rightHypothesis =>
          simp only [decodeActiveHypothesisLinkAtom_activeHypothesisLinkAtom,
            Option.some.injEq, ActiveHypothesisOccurrence.mk.injEq] at decoded
          rcases decoded with ⟨rfl, rfl, rfl⟩
          rfl

/-- One active `$d` occurrence retains whether it introduced the shared proof
capability or merely repeated an earlier pair.  The two row atoms are potential
capabilities: they are resident only while both `$f` endpoints are active. -/
def activeDistinctLinkAtom (owner previous next : Atom)
    (kind : DVOccurrenceKind) (capability : ActiveDistinctCapabilityKind)
    (leftRow rightRow : Atom) : Atom :=
  .expression
    [.symbol "mm-source-active-distinct-link",
      activeDistinctLedgerOwner owner, previous, next,
      dvOccurrenceKindAtom kind,
      activeDistinctCapabilityKindAtom capability, leftRow, rightRow]

def emptyScopedActivityRows (owner : Atom) : List Atom :=
  [sourceActivityFrontierAtom (activeHypothesisLedgerOwner owner)
      objectRootKey,
   sourceActivityFrontierAtom (activeDistinctLedgerOwner owner)
      objectRootKey]

@[simp] theorem emptyScopedActivityRows_length (owner : Atom) :
    (emptyScopedActivityRows owner).length = 2 := by
  rfl

/-! ## Ordinary MM2 scope protocol -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def scopeOpenLocation := location "02" "mm-source-scope-open"
private def scopeCloseUnderflowLocation :=
  location "01" "mm-source-scope-close-underflow"
private def scopeCloseStartLocation :=
  location "01" "mm-source-scope-close-start"
private def scopeCloseVariablePopLocation :=
  location "01" "mm-source-scope-close-variable-pop"
private def scopeCloseVariableDoneLocation :=
  location "00" "mm-source-scope-close-variable-done"
private def scopeCloseHypothesisPopLocation :=
  location "01" "mm-source-scope-close-hypothesis-pop"
private def scopeCloseHypothesisDoneLocation :=
  location "00" "mm-source-scope-close-hypothesis-done"
private def scopeCloseDistinctFirstLivePopLocation :=
  location "01" "mm-source-scope-close-distinct-first-live-pop"
private def scopeCloseDistinctDuplicatePopLocation :=
  location "01" "mm-source-scope-close-distinct-duplicate-pop"
private def scopeCloseDistinctFirstInertPopLocation :=
  location "01" "mm-source-scope-close-distinct-first-inert-pop"
private def scopeCloseDistinctDoneLocation :=
  location "00" "mm-source-scope-close-distinct-done"
private def scopeCloseRestoreLocation :=
  location "01" "mm-source-scope-close-restore"

private def openStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-open-scope", .var "scope-site"]

private def closeStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-close-scope", .var "scope-site"]

private def sourceCurrentTemplate (statement : Atom) : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", statement, .var "dispatch-input",
      .var "dispatch-output"]

private def openCurrentTemplate : Atom :=
  sourceCurrentTemplate openStatementTemplate

private def closeCurrentTemplate : Atom :=
  sourceCurrentTemplate closeStatementTemplate

private def checkpointTemplate : Atom :=
  .expression
    [.symbol "mm-source-scope-checkpoint", .var "saved-variable-frontier",
      .var "saved-hypothesis-frontier", .var "saved-distinct-frontier",
      .var "saved-occurrence-frontier"]

private def environmentTemplate (scopeStack : Atom) : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "source", scopeStack,
      .var "next-hypothesis", .var "next-assertion"]

private def emptyScopeStackTemplate : Atom :=
  .expression [.symbol "mm-nil"]

private def nonemptyScopeStackTemplate : Atom :=
  .expression [.symbol "mm-cons", checkpointTemplate, .var "scope-rest"]

private def variableOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", .var "source"]

private def hypothesisOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]

private def distinctOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-distinct-ledger", .var "source"]

private def variableFrontierTemplate (frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", variableOwnerTemplate, frontier]

private def hypothesisFrontierTemplate (frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate, frontier]

private def distinctFrontierTemplate (frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", distinctOwnerTemplate, frontier]

private def occurrenceFrontierTemplate (frontier : Atom) : Atom :=
  dvOccurrenceFrontierAtAtom (.var "source") frontier

private def currentVariableFrontierTemplate : Atom :=
  variableFrontierTemplate (.var "current-variable-frontier")

private def currentHypothesisFrontierTemplate : Atom :=
  hypothesisFrontierTemplate (.var "current-hypothesis-frontier")

private def currentDistinctFrontierTemplate : Atom :=
  distinctFrontierTemplate (.var "current-distinct-frontier")

private def currentOccurrenceFrontierTemplate : Atom :=
  occurrenceFrontierTemplate (.var "current-occurrence-frontier")

private def popOccurrenceFrontierTemplate : Atom :=
  occurrenceFrontierTemplate (.var "current-distinct-frontier")

private def currentCheckpointTemplate : Atom :=
  .expression
    [.symbol "mm-source-scope-checkpoint",
      .var "current-variable-frontier",
      .var "current-hypothesis-frontier",
      .var "current-distinct-frontier",
      .var "current-occurrence-frontier"]

private def openEnvironmentTemplate : Atom :=
  environmentTemplate (.var "scope-stack")

private def openedEnvironmentTemplate : Atom :=
  environmentTemplate
    (.expression
      [.symbol "mm-cons", currentCheckpointTemplate, .var "scope-stack"])

private def closeEnvironmentTemplate : Atom :=
  environmentTemplate nonemptyScopeStackTemplate

private def restoredEnvironmentTemplate : Atom :=
  environmentTemplate (.var "scope-rest")

private def sourceNextControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def statementAppliedTemplate (statement : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source",
      .var "position", statement]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-scope-reload",
      .var "source-verifier-reload-rule"]

def scopeSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-scope-reload", sourceVerifierReloadRule]

private def scopeRuleCaptureTemplate (phase ruleVariable : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-scope-rule", .symbol phase,
      .var ruleVariable]

private def scopeRuleCaptureRow (phase : String) (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-scope-rule", .symbol phase, rule]

private def variablePopCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "variable-pop" "variable-pop-rule"

private def variableDoneCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "variable-done" "variable-done-rule"

private def hypothesisPopCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "hypothesis-pop" "hypothesis-pop-rule"

private def hypothesisDoneCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "hypothesis-done" "hypothesis-done-rule"

private def distinctFirstLivePopCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "distinct-first-live-pop"
    "distinct-first-live-pop-rule"

private def distinctDuplicatePopCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "distinct-duplicate-pop"
    "distinct-duplicate-pop-rule"

private def distinctFirstInertPopCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "distinct-first-inert-pop"
    "distinct-first-inert-pop-rule"

private def distinctDoneCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "distinct-done" "distinct-done-rule"

private def restoreCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "restore" "restore-rule"

private def underflowCaptureTemplate : Atom :=
  scopeRuleCaptureTemplate "underflow" "underflow-rule"

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def sinkAtom : Sink -> Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom => .expression [.symbol "head", natAtom count, atom]
  | .tail count atom => .expression [.symbol "tail", natAtom count, atom]

private def mkRule (loc : Atom) (patterns : List Atom)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkAtom)]

private def openSelf : Atom := selfTemplate scopeOpenLocation "scope-open"

private def openPatterns : List Atom :=
  [openSelf, openCurrentTemplate, openEnvironmentTemplate,
   currentVariableFrontierTemplate, currentHypothesisFrontierTemplate,
   currentDistinctFrontierTemplate, currentOccurrenceFrontierTemplate,
   sourceReloadCaptureTemplate]

private def openSinks : List Sink :=
  [.add openSelf, .remove openCurrentTemplate, .remove openEnvironmentTemplate,
   .add openedEnvironmentTemplate, .add sourceNextControlTemplate,
   .add (statementAppliedTemplate openStatementTemplate),
   .add sourceReloadTemplate, .add (.var "source-verifier-reload-rule")]

def scopeOpenRule : Atom :=
  mkRule scopeOpenLocation openPatterns openSinks

def scopeOpenDirective : SourceExecFact where
  atom := scopeOpenRule
  loc := scopeOpenLocation
  rule :=
    { priority := 2
      name := "mm-source-scope-open"
      input := .compat (mkPattern openPatterns)
      guards := []
      tmpl := mkTemplate openSinks }

theorem extract_scopeOpenRule_exact :
    extractSupportedSourceExecFact scopeOpenRule =
      some scopeOpenDirective := by
  rfl

private def closeUnderflowSelf : Atom :=
  selfTemplate scopeCloseUnderflowLocation "scope-close-underflow"

private def closeUnderflowPatterns : List Atom :=
  [closeUnderflowSelf, closeCurrentTemplate,
   environmentTemplate emptyScopeStackTemplate]

private def closeRejectedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source",
      .var "position", closeStatementTemplate, .symbol "scope-underflow",
      .var "scope-site"]

private def closeUnderflowSinks : List Sink :=
  [.add closeUnderflowSelf, .remove closeCurrentTemplate,
   .add closeRejectedTemplate]

def scopeCloseUnderflowRule : Atom :=
  mkRule scopeCloseUnderflowLocation closeUnderflowPatterns
    closeUnderflowSinks

def scopeCloseUnderflowDirective : SourceExecFact where
  atom := scopeCloseUnderflowRule
  loc := scopeCloseUnderflowLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-underflow"
      input := .compat (mkPattern closeUnderflowPatterns)
      guards := []
      tmpl := mkTemplate closeUnderflowSinks }

theorem extract_scopeCloseUnderflowRule_exact :
    extractSupportedSourceExecFact scopeCloseUnderflowRule =
      some scopeCloseUnderflowDirective := by
  rfl

private def closeControlTemplate (phase : String) : Atom :=
  .expression
    [.symbol "mm-source-scope-close-control", .var "source",
      .var "position", .var "next-position", closeStatementTemplate,
      .var "dispatch-input", .var "dispatch-output",
      .var "scope-rest", .var "next-hypothesis", .var "next-assertion",
      .var "saved-variable-frontier", .var "saved-hypothesis-frontier",
      .var "saved-distinct-frontier", .var "saved-occurrence-frontier",
      .symbol phase]

private def closeVariableControl :=
  closeControlTemplate "mm-source-scope-close-variable"
private def closeHypothesisControl :=
  closeControlTemplate "mm-source-scope-close-hypothesis"
private def closeDistinctControl :=
  closeControlTemplate "mm-source-scope-close-distinct"
private def closeRestoreControl :=
  closeControlTemplate "mm-source-scope-close-restore"

private def closeStartSelf : Atom :=
  selfTemplate scopeCloseStartLocation "scope-close-start"

private def closeStartPatterns : List Atom :=
  [closeStartSelf, closeCurrentTemplate, closeEnvironmentTemplate,
   currentVariableFrontierTemplate, currentHypothesisFrontierTemplate,
   currentDistinctFrontierTemplate, currentOccurrenceFrontierTemplate,
   variablePopCaptureTemplate, variableDoneCaptureTemplate,
   underflowCaptureTemplate]

private def closeStartSinks : List Sink :=
  [.add closeStartSelf, .remove closeEnvironmentTemplate,
   .remove (.var "underflow-rule"),
   .add closeVariableControl, .add (.var "variable-pop-rule"),
   .add (.var "variable-done-rule")]

def scopeCloseStartRule : Atom :=
  mkRule scopeCloseStartLocation closeStartPatterns closeStartSinks

def scopeCloseStartDirective : SourceExecFact where
  atom := scopeCloseStartRule
  loc := scopeCloseStartLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-start"
      input := .compat (mkPattern closeStartPatterns)
      guards := []
      tmpl := mkTemplate closeStartSinks }

theorem extract_scopeCloseStartRule_exact :
    extractSupportedSourceExecFact scopeCloseStartRule =
      some scopeCloseStartDirective := by
  rfl

private def variableLinkToCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", variableOwnerTemplate,
      .var "previous-variable-frontier", .var "current-variable-frontier",
      .var "active-variable-entry"]

private def variablePopSelf : Atom :=
  selfTemplate scopeCloseVariablePopLocation "scope-close-variable-pop"

private def variablePopPatterns : List Atom :=
  [variablePopSelf, closeVariableControl, currentVariableFrontierTemplate,
   variableLinkToCurrentTemplate, variableDoneCaptureTemplate]

private def variablePopSinks : List Sink :=
  [.add variablePopSelf, .remove currentVariableFrontierTemplate,
   .remove variableLinkToCurrentTemplate,
   .add (variableFrontierTemplate (.var "previous-variable-frontier")),
   .add (.var "variable-done-rule")]

def scopeCloseVariablePopRule : Atom :=
  mkRule scopeCloseVariablePopLocation variablePopPatterns variablePopSinks

def scopeCloseVariablePopDirective : SourceExecFact where
  atom := scopeCloseVariablePopRule
  loc := scopeCloseVariablePopLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-variable-pop"
      input := .compat (mkPattern variablePopPatterns)
      guards := []
      tmpl := mkTemplate variablePopSinks }

theorem extract_scopeCloseVariablePopRule_exact :
    extractSupportedSourceExecFact scopeCloseVariablePopRule =
      some scopeCloseVariablePopDirective := by
  rfl

private def variableDoneSelf : Atom :=
  selfTemplate scopeCloseVariableDoneLocation "scope-close-variable-done"

private def savedVariableFrontierTemplate : Atom :=
  variableFrontierTemplate (.var "saved-variable-frontier")

private def variableDonePatterns : List Atom :=
  [variableDoneSelf, closeVariableControl, savedVariableFrontierTemplate]
    ++ [hypothesisPopCaptureTemplate, hypothesisDoneCaptureTemplate]

private def variableDoneSinks : List Sink :=
  [.add variableDoneSelf, .remove closeVariableControl,
   .add closeHypothesisControl, .add (.var "hypothesis-pop-rule"),
   .add (.var "hypothesis-done-rule")]

def scopeCloseVariableDoneRule : Atom :=
  mkRule scopeCloseVariableDoneLocation variableDonePatterns variableDoneSinks

def scopeCloseVariableDoneDirective : SourceExecFact where
  atom := scopeCloseVariableDoneRule
  loc := scopeCloseVariableDoneLocation
  rule :=
    { priority := 0
      name := "mm-source-scope-close-variable-done"
      input := .compat (mkPattern variableDonePatterns)
      guards := []
      tmpl := mkTemplate variableDoneSinks }

theorem extract_scopeCloseVariableDoneRule_exact :
    extractSupportedSourceExecFact scopeCloseVariableDoneRule =
      some scopeCloseVariableDoneDirective := by
  rfl

private def hypothesisLinkToCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", hypothesisOwnerTemplate,
      .var "previous-hypothesis-frontier",
      .var "current-hypothesis-frontier", .var "encoded-hypothesis",
      .var "hypothesis-runtime-row"]

private def hypothesisPopSelf : Atom :=
  selfTemplate scopeCloseHypothesisPopLocation "scope-close-hypothesis-pop"

private def hypothesisPopPatterns : List Atom :=
  [hypothesisPopSelf, closeHypothesisControl,
   currentHypothesisFrontierTemplate, hypothesisLinkToCurrentTemplate,
   .var "hypothesis-runtime-row", hypothesisDoneCaptureTemplate]

private def hypothesisPopSinks : List Sink :=
  [.add hypothesisPopSelf, .remove currentHypothesisFrontierTemplate,
   .remove hypothesisLinkToCurrentTemplate,
   .remove (.var "hypothesis-runtime-row"),
   .add (hypothesisFrontierTemplate
      (.var "previous-hypothesis-frontier")),
   .add (.var "hypothesis-done-rule")]

def scopeCloseHypothesisPopRule : Atom :=
  mkRule scopeCloseHypothesisPopLocation hypothesisPopPatterns
    hypothesisPopSinks

def scopeCloseHypothesisPopDirective : SourceExecFact where
  atom := scopeCloseHypothesisPopRule
  loc := scopeCloseHypothesisPopLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-hypothesis-pop"
      input := .compat (mkPattern hypothesisPopPatterns)
      guards := []
      tmpl := mkTemplate hypothesisPopSinks }

theorem extract_scopeCloseHypothesisPopRule_exact :
    extractSupportedSourceExecFact scopeCloseHypothesisPopRule =
      some scopeCloseHypothesisPopDirective := by
  rfl

private def hypothesisDoneSelf : Atom :=
  selfTemplate scopeCloseHypothesisDoneLocation
    "scope-close-hypothesis-done"

private def savedHypothesisFrontierTemplate : Atom :=
  hypothesisFrontierTemplate (.var "saved-hypothesis-frontier")

private def hypothesisDonePatterns : List Atom :=
  [hypothesisDoneSelf, closeHypothesisControl,
   savedHypothesisFrontierTemplate, distinctFirstLivePopCaptureTemplate,
   distinctDuplicatePopCaptureTemplate, distinctFirstInertPopCaptureTemplate,
   distinctDoneCaptureTemplate]

private def hypothesisDoneSinks : List Sink :=
  [.add hypothesisDoneSelf, .remove closeHypothesisControl,
   .add closeDistinctControl, .add (.var "distinct-first-live-pop-rule"),
   .add (.var "distinct-duplicate-pop-rule"),
   .add (.var "distinct-first-inert-pop-rule"),
   .add (.var "distinct-done-rule")]

def scopeCloseHypothesisDoneRule : Atom :=
  mkRule scopeCloseHypothesisDoneLocation hypothesisDonePatterns
    hypothesisDoneSinks

def scopeCloseHypothesisDoneDirective : SourceExecFact where
  atom := scopeCloseHypothesisDoneRule
  loc := scopeCloseHypothesisDoneLocation
  rule :=
    { priority := 0
      name := "mm-source-scope-close-hypothesis-done"
      input := .compat (mkPattern hypothesisDonePatterns)
      guards := []
      tmpl := mkTemplate hypothesisDoneSinks }

theorem extract_scopeCloseHypothesisDoneRule_exact :
    extractSupportedSourceExecFact scopeCloseHypothesisDoneRule =
      some scopeCloseHypothesisDoneDirective := by
  rfl

private def distinctLinkToCurrentTemplate
    (occurrenceKind : DVOccurrenceKind)
    (capabilityKind : ActiveDistinctCapabilityKind) : Atom :=
  .expression
    [.symbol "mm-source-active-distinct-link", distinctOwnerTemplate,
      .var "previous-distinct-frontier", .var "current-distinct-frontier",
      dvOccurrenceKindAtom occurrenceKind,
      activeDistinctCapabilityKindAtom capabilityKind,
      .expression
        [.symbol "mm-caller-dv", .var "source", .var "distinct-left-name",
          .var "distinct-right-name"],
      .expression
        [.symbol "mm-caller-dv", .var "source", .var "distinct-right-name",
          .var "distinct-left-name"]]

private def exactOccurrenceLinkToCurrentTemplate
    (occurrenceKind : DVOccurrenceKind) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-link", .var "source",
      .var "previous-occurrence-frontier", .var "current-distinct-frontier",
      .expression
        [.symbol "mm-source-dv-occurrence-entry",
          .expression
            [.symbol "mm-pair", .var "distinct-left-name",
              .var "distinct-right-name"],
          dvOccurrenceKindAtom occurrenceKind]]

private def distinctLeftRuntimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-caller-dv", .var "source", .var "distinct-left-name",
      .var "distinct-right-name"]

private def distinctRightRuntimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-caller-dv", .var "source", .var "distinct-right-name",
      .var "distinct-left-name"]

private def distinctFirstLivePopSelf : Atom :=
  selfTemplate scopeCloseDistinctFirstLivePopLocation
    "scope-close-distinct-first-live-pop"

private def distinctFirstLivePopPatterns : List Atom :=
  [distinctFirstLivePopSelf, closeDistinctControl,
   currentDistinctFrontierTemplate,
   popOccurrenceFrontierTemplate,
   distinctLinkToCurrentTemplate .first .live,
   exactOccurrenceLinkToCurrentTemplate .first,
   distinctLeftRuntimeRowTemplate, distinctRightRuntimeRowTemplate,
   distinctDoneCaptureTemplate]

private def distinctFirstLivePopSinks : List Sink :=
  [.add distinctFirstLivePopSelf, .remove currentDistinctFrontierTemplate,
   .remove popOccurrenceFrontierTemplate,
   .remove (distinctLinkToCurrentTemplate .first .live),
   .remove (exactOccurrenceLinkToCurrentTemplate .first),
   .remove distinctLeftRuntimeRowTemplate,
   .remove distinctRightRuntimeRowTemplate,
   .add (distinctFrontierTemplate (.var "previous-distinct-frontier")),
   .add (occurrenceFrontierTemplate (.var "previous-occurrence-frontier")),
   .add (.var "distinct-done-rule")]

def scopeCloseDistinctFirstLivePopRule : Atom :=
  mkRule scopeCloseDistinctFirstLivePopLocation
    distinctFirstLivePopPatterns distinctFirstLivePopSinks

def scopeCloseDistinctFirstLivePopDirective : SourceExecFact where
  atom := scopeCloseDistinctFirstLivePopRule
  loc := scopeCloseDistinctFirstLivePopLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-distinct-first-live-pop"
      input := .compat (mkPattern distinctFirstLivePopPatterns)
      guards := []
      tmpl := mkTemplate distinctFirstLivePopSinks }

theorem extract_scopeCloseDistinctFirstLivePopRule_exact :
    extractSupportedSourceExecFact scopeCloseDistinctFirstLivePopRule =
      some scopeCloseDistinctFirstLivePopDirective := by
  rfl

private def distinctDuplicatePopSelf : Atom :=
  selfTemplate scopeCloseDistinctDuplicatePopLocation
    "scope-close-distinct-duplicate-pop"

private def distinctDuplicatePopPatterns : List Atom :=
  [distinctDuplicatePopSelf, closeDistinctControl,
   currentDistinctFrontierTemplate,
   popOccurrenceFrontierTemplate,
   distinctLinkToCurrentTemplate .duplicate .shared,
   exactOccurrenceLinkToCurrentTemplate .duplicate,
   distinctDoneCaptureTemplate]

private def distinctDuplicatePopSinks : List Sink :=
  [.add distinctDuplicatePopSelf, .remove currentDistinctFrontierTemplate,
   .remove popOccurrenceFrontierTemplate,
   .remove (distinctLinkToCurrentTemplate .duplicate .shared),
   .remove (exactOccurrenceLinkToCurrentTemplate .duplicate),
   .add (distinctFrontierTemplate (.var "previous-distinct-frontier")),
   .add (occurrenceFrontierTemplate (.var "previous-occurrence-frontier")),
   .add (.var "distinct-done-rule")]

def scopeCloseDistinctDuplicatePopRule : Atom :=
  mkRule scopeCloseDistinctDuplicatePopLocation
    distinctDuplicatePopPatterns distinctDuplicatePopSinks

def scopeCloseDistinctDuplicatePopDirective : SourceExecFact where
  atom := scopeCloseDistinctDuplicatePopRule
  loc := scopeCloseDistinctDuplicatePopLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-distinct-duplicate-pop"
      input := .compat (mkPattern distinctDuplicatePopPatterns)
      guards := []
      tmpl := mkTemplate distinctDuplicatePopSinks }

theorem extract_scopeCloseDistinctDuplicatePopRule_exact :
    extractSupportedSourceExecFact scopeCloseDistinctDuplicatePopRule =
      some scopeCloseDistinctDuplicatePopDirective := by
  rfl

private def distinctFirstInertPopSelf : Atom :=
  selfTemplate scopeCloseDistinctFirstInertPopLocation
    "scope-close-distinct-first-inert-pop"

private def distinctFirstInertPopPatterns : List Atom :=
  [distinctFirstInertPopSelf, closeDistinctControl,
   currentDistinctFrontierTemplate,
   popOccurrenceFrontierTemplate,
   distinctLinkToCurrentTemplate .first .inert,
   exactOccurrenceLinkToCurrentTemplate .first,
   distinctDoneCaptureTemplate]

private def distinctFirstInertPopSinks : List Sink :=
  [.add distinctFirstInertPopSelf, .remove currentDistinctFrontierTemplate,
   .remove popOccurrenceFrontierTemplate,
   .remove (distinctLinkToCurrentTemplate .first .inert),
   .remove (exactOccurrenceLinkToCurrentTemplate .first),
   .add (distinctFrontierTemplate (.var "previous-distinct-frontier")),
   .add (occurrenceFrontierTemplate (.var "previous-occurrence-frontier")),
   .add (.var "distinct-done-rule")]

def scopeCloseDistinctFirstInertPopRule : Atom :=
  mkRule scopeCloseDistinctFirstInertPopLocation
    distinctFirstInertPopPatterns distinctFirstInertPopSinks

def scopeCloseDistinctFirstInertPopDirective : SourceExecFact where
  atom := scopeCloseDistinctFirstInertPopRule
  loc := scopeCloseDistinctFirstInertPopLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-distinct-first-inert-pop"
      input := .compat (mkPattern distinctFirstInertPopPatterns)
      guards := []
      tmpl := mkTemplate distinctFirstInertPopSinks }

theorem extract_scopeCloseDistinctFirstInertPopRule_exact :
    extractSupportedSourceExecFact scopeCloseDistinctFirstInertPopRule =
      some scopeCloseDistinctFirstInertPopDirective := by
  rfl

private def distinctDoneSelf : Atom :=
  selfTemplate scopeCloseDistinctDoneLocation "scope-close-distinct-done"

private def savedDistinctFrontierTemplate : Atom :=
  distinctFrontierTemplate (.var "saved-distinct-frontier")

private def savedOccurrenceFrontierTemplate : Atom :=
  occurrenceFrontierTemplate (.var "saved-occurrence-frontier")

private def distinctDonePatterns : List Atom :=
  [distinctDoneSelf, closeDistinctControl, savedDistinctFrontierTemplate,
    savedOccurrenceFrontierTemplate]
    ++ [restoreCaptureTemplate]

private def distinctDoneSinks : List Sink :=
  [.add distinctDoneSelf, .remove closeDistinctControl,
   .add closeRestoreControl, .add (.var "restore-rule")]

def scopeCloseDistinctDoneRule : Atom :=
  mkRule scopeCloseDistinctDoneLocation distinctDonePatterns distinctDoneSinks

def scopeCloseDistinctDoneDirective : SourceExecFact where
  atom := scopeCloseDistinctDoneRule
  loc := scopeCloseDistinctDoneLocation
  rule :=
    { priority := 0
      name := "mm-source-scope-close-distinct-done"
      input := .compat (mkPattern distinctDonePatterns)
      guards := []
      tmpl := mkTemplate distinctDoneSinks }

theorem extract_scopeCloseDistinctDoneRule_exact :
    extractSupportedSourceExecFact scopeCloseDistinctDoneRule =
      some scopeCloseDistinctDoneDirective := by
  rfl

private def restoreSelf : Atom :=
  selfTemplate scopeCloseRestoreLocation "scope-close-restore"

private def restorePatterns : List Atom :=
  [restoreSelf, closeRestoreControl, closeCurrentTemplate,
    sourceReloadCaptureTemplate]

private def restoreSinks : List Sink :=
  [.add restoreSelf, .remove closeRestoreControl,
   .remove closeCurrentTemplate, .add restoredEnvironmentTemplate,
   .add sourceNextControlTemplate,
   .add (statementAppliedTemplate closeStatementTemplate),
   .add sourceReloadTemplate, .add (.var "source-verifier-reload-rule")]

def scopeCloseRestoreRule : Atom :=
  mkRule scopeCloseRestoreLocation restorePatterns restoreSinks

def scopeCloseRestoreDirective : SourceExecFact where
  atom := scopeCloseRestoreRule
  loc := scopeCloseRestoreLocation
  rule :=
    { priority := 1
      name := "mm-source-scope-close-restore"
      input := .compat (mkPattern restorePatterns)
      guards := []
      tmpl := mkTemplate restoreSinks }

theorem extract_scopeCloseRestoreRule_exact :
    extractSupportedSourceExecFact scopeCloseRestoreRule =
      some scopeCloseRestoreDirective := by
  rfl

def scopeExecutionRules : List Atom :=
  [scopeOpenRule, scopeCloseUnderflowRule, scopeCloseStartRule,
   scopeCloseVariablePopRule, scopeCloseVariableDoneRule,
   scopeCloseHypothesisPopRule, scopeCloseHypothesisDoneRule,
   scopeCloseDistinctFirstLivePopRule,
   scopeCloseDistinctDuplicatePopRule,
   scopeCloseDistinctFirstInertPopRule, scopeCloseDistinctDoneRule,
   scopeCloseRestoreRule]

def scopeExecutionDirectives : List SourceExecFact :=
  [scopeOpenDirective, scopeCloseUnderflowDirective,
   scopeCloseStartDirective, scopeCloseVariablePopDirective,
   scopeCloseVariableDoneDirective, scopeCloseHypothesisPopDirective,
   scopeCloseHypothesisDoneDirective,
   scopeCloseDistinctFirstLivePopDirective,
   scopeCloseDistinctDuplicatePopDirective,
   scopeCloseDistinctFirstInertPopDirective,
   scopeCloseDistinctDoneDirective, scopeCloseRestoreDirective]

def scopeExecutionStaticRows : List Atom :=
  [scopeSourceReloadCaptureRow,
   scopeRuleCaptureRow "variable-pop" scopeCloseVariablePopRule,
   scopeRuleCaptureRow "variable-done" scopeCloseVariableDoneRule,
   scopeRuleCaptureRow "hypothesis-pop" scopeCloseHypothesisPopRule,
   scopeRuleCaptureRow "hypothesis-done" scopeCloseHypothesisDoneRule,
   scopeRuleCaptureRow "distinct-first-live-pop"
     scopeCloseDistinctFirstLivePopRule,
   scopeRuleCaptureRow "distinct-duplicate-pop"
     scopeCloseDistinctDuplicatePopRule,
   scopeRuleCaptureRow "distinct-first-inert-pop"
     scopeCloseDistinctFirstInertPopRule,
   scopeRuleCaptureRow "distinct-done" scopeCloseDistinctDoneRule,
   scopeRuleCaptureRow "restore" scopeCloseRestoreRule,
   scopeRuleCaptureRow "underflow" scopeCloseUnderflowRule]

theorem scopeExecutionRules_extract_exact :
    scopeExecutionRules.filterMap extractSupportedSourceExecFact =
      scopeExecutionDirectives := by
  rfl

@[simp] theorem scopeSourceReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom scopeSourceReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-scope-reload" [sourceVerifierReloadRule]
      (by decide)

/-! ## Complete bounded controls -/

private def fixtureOwner : Atom := .symbol "scope-source"

private def openSite : LocatedByteSpan :=
  { fileId := "scope.mm", start := 0, stop := 2 }

private def closeSite : LocatedByteSpan :=
  { fileId := "scope.mm", start := 8, stop := 10 }

private def openStatement : RawStatement := .openScope openSite
private def closeStatement : RawStatement := .closeScope closeSite

private def activeName : LocatedName :=
  { span := { fileId := "scope.mm", start := 3, stop := 4 }
    name := "x" }

private def activeEntry : ObjectOccurrence :=
  activeOccurrenceEntry activeName

private def openProgram : List Atom :=
  [scopeOpenRule, sourceCurrentAtom fixtureOwner 0 1 openStatement,
   sourceInitialEnvironmentAtom fixtureOwner,
   objectFrontierAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey,
   sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
     objectRootKey,
   sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
     objectRootKey,
   dvOccurrenceFrontierAtAtom fixtureOwner (natAtom 0),
   scopeSourceReloadCaptureRow]

private def openedCheckpoint : ScopeCheckpoint :=
  { activeVariableFrontier := objectRootKey
    activeHypothesisFrontier := objectRootKey
    activeDistinctFrontier := objectRootKey
    dvOccurrenceFrontier := natAtom 0 }

private def openedEnvironment : Atom :=
  sourceEnvironmentAtom fixtureOwner
    (listAtom id [scopeCheckpointAtom openedCheckpoint]) 0 0

theorem openProgram_completes_exact_checkpoint :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 openProgram).1
    openedEnvironment ∈ final /\
      sourceControlAtom fixtureOwner 1 ∈ final /\
      .expression
        [.symbol "mm-source-statement-applied", fixtureOwner, natAtom 0,
          rawStatementAtom openStatement] ∈ final := by
  decide +kernel

def openProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 1 openProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 openProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 1 openProgram

private def closeVariableFrontier : Atom := locatedNameAtom activeName

private def closeHypothesisFrontier : Atom :=
  .expression [.symbol "scope-hypothesis-frontier"]

private def closeDistinctFrontier : Atom :=
  .expression [.symbol "scope-distinct-frontier"]

private def closeHypothesis : HypothesisView :=
  .essential "scope-hypothesis"
    { typecode := "wff", body := [.var "x"] }

private def closeHypothesisRuntimeRow : Atom :=
  hypothesisLookupRow fixtureOwner closeHypothesis

private def closeDistinctLeftRuntimeRow : Atom :=
  callerDVRow fixtureOwner "x" "y"

private def closeDistinctRightRuntimeRow : Atom :=
  callerDVRow fixtureOwner "y" "x"

private def closeDistinctFirstOccurrence : MarkedDVOccurrence :=
  { pair := ("x", "y"), kind := .first }

private def closeDistinctDuplicateOccurrence : MarkedDVOccurrence :=
  { pair := ("x", "y"), kind := .duplicate }

private def closeCheckpointStack : Atom :=
  listAtom id [scopeCheckpointAtom openedCheckpoint]

private def closeProgram : List Atom :=
  scopeExecutionRules ++
    scopeExecutionStaticRows ++
    [sourceCurrentAtom fixtureOwner 1 2 closeStatement,
     sourceEnvironmentAtom fixtureOwner closeCheckpointStack 0 0,
     objectLinkAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey
       closeVariableFrontier activeEntry,
     objectFrontierAtom (activeVariableLedgerOwner fixtureOwner)
       closeVariableFrontier,
     sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
       closeHypothesisFrontier,
     activeHypothesisLinkAtom fixtureOwner objectRootKey
       closeHypothesisFrontier closeHypothesis,
     closeHypothesisRuntimeRow,
     sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
       closeDistinctFrontier,
     dvOccurrenceFrontierAtAtom fixtureOwner closeDistinctFrontier,
     dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0)
       closeDistinctFrontier closeDistinctFirstOccurrence,
     activeDistinctLinkAtom fixtureOwner objectRootKey closeDistinctFrontier
       .first .live
       closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow,
     closeDistinctLeftRuntimeRow, closeDistinctRightRuntimeRow]

theorem closeProgram_restores_exact_active_prefix :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 30 closeProgram).1
    sourceInitialEnvironmentAtom fixtureOwner ∈ final /\
      objectFrontierAtom (activeVariableLedgerOwner fixtureOwner)
        objectRootKey ∈ final /\
      objectLinkAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey
        closeVariableFrontier activeEntry ∉ final /\
      sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
        objectRootKey ∈ final /\
      activeHypothesisLinkAtom fixtureOwner objectRootKey
        closeHypothesisFrontier closeHypothesis ∉ final /\
      closeHypothesisRuntimeRow ∉ final /\
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        objectRootKey ∈ final /\
      dvOccurrenceFrontierAtAtom fixtureOwner (natAtom 0) ∈ final /\
      dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0) closeDistinctFrontier
        closeDistinctFirstOccurrence ∉ final /\
      activeDistinctLinkAtom fixtureOwner objectRootKey closeDistinctFrontier
        .first .live
        closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow ∉ final /\
      closeDistinctLeftRuntimeRow ∉ final /\
      closeDistinctRightRuntimeRow ∉ final /\
      sourceCurrentAtom fixtureOwner 1 2 closeStatement ∉ final /\
      sourceControlAtom fixtureOwner 2 ∈ final /\
      .expression
        [.symbol "mm-source-statement-applied", fixtureOwner, natAtom 1,
          rawStatementAtom closeStatement] ∈ final := by
  decide +kernel

def closeProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 30 closeProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 30 closeProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 30 closeProgram

/-! The remaining controls distinguish two cases that the earlier link shape
could not represent: an inert first occurrence and a duplicate sharing a live
outer capability. -/

private def closeInertDistinctProgram : List Atom :=
  scopeExecutionRules ++ scopeExecutionStaticRows ++
    [sourceCurrentAtom fixtureOwner 1 2 closeStatement,
     sourceEnvironmentAtom fixtureOwner closeCheckpointStack 0 0,
     objectFrontierAtom (activeVariableLedgerOwner fixtureOwner)
       objectRootKey,
     sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
       objectRootKey,
     sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
       closeDistinctFrontier,
     dvOccurrenceFrontierAtAtom fixtureOwner closeDistinctFrontier,
     dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0) closeDistinctFrontier
       closeDistinctFirstOccurrence,
     activeDistinctLinkAtom fixtureOwner objectRootKey closeDistinctFrontier
       .first .inert closeDistinctLeftRuntimeRow
       closeDistinctRightRuntimeRow]

theorem closeInertDistinctProgram_pops_without_runtime_rows :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 30
        closeInertDistinctProgram).1
    sourceInitialEnvironmentAtom fixtureOwner ∈ final /\
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        objectRootKey ∈ final /\
      dvOccurrenceFrontierAtAtom fixtureOwner (natAtom 0) ∈ final /\
      dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0) closeDistinctFrontier
        closeDistinctFirstOccurrence ∉ final /\
      activeDistinctLinkAtom fixtureOwner objectRootKey closeDistinctFrontier
        .first .inert closeDistinctLeftRuntimeRow
        closeDistinctRightRuntimeRow ∉ final /\
      closeDistinctLeftRuntimeRow ∉ final /\
      closeDistinctRightRuntimeRow ∉ final := by
  decide +kernel

def closeInertDistinctProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 30 closeInertDistinctProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 30
        closeInertDistinctProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 30
    closeInertDistinctProgram

private def duplicateSavedDistinctFrontier : Atom :=
  .expression [.symbol "scope-distinct-first-frontier"]

private def duplicateCheckpoint : ScopeCheckpoint :=
  { activeVariableFrontier := objectRootKey
    activeHypothesisFrontier := objectRootKey
    activeDistinctFrontier := duplicateSavedDistinctFrontier
    dvOccurrenceFrontier := duplicateSavedDistinctFrontier }

private def duplicateCheckpointStack : Atom :=
  listAtom id [scopeCheckpointAtom duplicateCheckpoint]

private def closeDuplicateDistinctProgram : List Atom :=
  scopeExecutionRules ++ scopeExecutionStaticRows ++
    [sourceCurrentAtom fixtureOwner 1 2 closeStatement,
     sourceEnvironmentAtom fixtureOwner duplicateCheckpointStack 0 0,
     objectFrontierAtom (activeVariableLedgerOwner fixtureOwner)
       objectRootKey,
     sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
       objectRootKey,
     sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
       closeDistinctFrontier,
     dvOccurrenceFrontierAtAtom fixtureOwner closeDistinctFrontier,
     dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0)
       duplicateSavedDistinctFrontier closeDistinctFirstOccurrence,
     dvOccurrenceLinkAtAtom fixtureOwner duplicateSavedDistinctFrontier
       closeDistinctFrontier closeDistinctDuplicateOccurrence,
     activeDistinctLinkAtom fixtureOwner objectRootKey
       duplicateSavedDistinctFrontier .first .live
       closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow,
     activeDistinctLinkAtom fixtureOwner duplicateSavedDistinctFrontier
       closeDistinctFrontier .duplicate .shared
       closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow,
     closeDistinctLeftRuntimeRow, closeDistinctRightRuntimeRow]

/-- Popping a repeated occurrence retains both the earlier occurrence link and
the shared proof-facing rows. -/
theorem closeDuplicateDistinctProgram_preserves_shared_capability :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 30
        closeDuplicateDistinctProgram).1
    sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        duplicateSavedDistinctFrontier ∈ final /\
      dvOccurrenceFrontierAtAtom fixtureOwner
        duplicateSavedDistinctFrontier ∈ final /\
      dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0)
        duplicateSavedDistinctFrontier closeDistinctFirstOccurrence ∈ final /\
      dvOccurrenceLinkAtAtom fixtureOwner duplicateSavedDistinctFrontier
        closeDistinctFrontier closeDistinctDuplicateOccurrence ∉ final /\
      activeDistinctLinkAtom fixtureOwner objectRootKey
        duplicateSavedDistinctFrontier .first .live
        closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow ∈ final /\
      activeDistinctLinkAtom fixtureOwner duplicateSavedDistinctFrontier
        closeDistinctFrontier .duplicate .shared
        closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow ∉ final /\
      closeDistinctLeftRuntimeRow ∈ final /\
      closeDistinctRightRuntimeRow ∈ final := by
  decide +kernel

def closeDuplicateDistinctProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 30 closeDuplicateDistinctProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 30
        closeDuplicateDistinctProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 30
    closeDuplicateDistinctProgram

/-! A scope pop must join the active-capability link to the exact source
occurrence link.  Equal cursors and occurrence kinds are insufficient when the
encoded pair differs. -/

private def mismatchedOccurrence : MarkedDVOccurrence :=
  { pair := ("x", "z"), kind := .first }

private def distinctPopControl : Atom :=
  .expression
    [.symbol "mm-source-scope-close-control", fixtureOwner, natAtom 1,
      natAtom 2, rawStatementAtom closeStatement, .symbol "dispatch-input",
      .symbol "dispatch-output", .expression [.symbol "mm-nil"], natAtom 0, natAtom 0,
      objectRootKey, objectRootKey, objectRootKey, natAtom 0,
      .symbol "mm-source-scope-close-distinct"]

private def mismatchedOccurrencePopAtoms : List Atom :=
  [scopeCloseDistinctFirstLivePopRule, distinctPopControl,
   sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
     closeDistinctFrontier,
   dvOccurrenceFrontierAtAtom fixtureOwner closeDistinctFrontier,
   activeDistinctLinkAtom fixtureOwner objectRootKey closeDistinctFrontier
     .first .live closeDistinctLeftRuntimeRow closeDistinctRightRuntimeRow,
   dvOccurrenceLinkAtAtom fixtureOwner (natAtom 0) closeDistinctFrontier
     mismatchedOccurrence,
   closeDistinctLeftRuntimeRow, closeDistinctRightRuntimeRow,
   scopeRuleCaptureRow "distinct-done" scopeCloseDistinctDoneRule]

private def mismatchedOccurrencePopSpace : Space :=
  mismatchedOccurrencePopAtoms.toFinset

private theorem mismatchedOccurrencePopAtoms_nodup :
    mismatchedOccurrencePopAtoms.Nodup := by
  decide +kernel

private theorem mismatchedOccurrencePop_fire_agreement :
    (cFireReflectiveSourceExecFact mismatchedOccurrencePopAtoms
        scopeCloseDistinctFirstLivePopDirective).toFinset =
      fireReflectiveSourceExecFact mismatchedOccurrencePopSpace
        scopeCloseDistinctFirstLivePopDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    mismatchedOccurrencePopAtoms scopeCloseDistinctFirstLivePopDirective
    mismatchedOccurrencePopAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      scopeCloseDistinctFirstLivePopDirective.rule.tmpl).1
        (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      mismatchedOccurrencePopAtoms scopeCloseDistinctFirstLivePopDirective
      mismatchedOccurrencePopAtoms_nodup)

theorem distinctPop_rejects_mismatched_occurrence_pair :
    sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        objectRootKey ∉
      fireReflectiveSourceExecFact mismatchedOccurrencePopSpace
        scopeCloseDistinctFirstLivePopDirective /\
    dvOccurrenceFrontierAtAtom fixtureOwner (natAtom 0) ∉
      fireReflectiveSourceExecFact mismatchedOccurrencePopSpace
        scopeCloseDistinctFirstLivePopDirective := by
  rw [← mismatchedOccurrencePop_fire_agreement]
  decide +kernel

private def underflowProgram : List Atom :=
  [scopeCloseUnderflowRule,
   sourceCurrentAtom fixtureOwner 0 1 closeStatement,
   sourceInitialEnvironmentAtom fixtureOwner]

private def underflowRejectedAtom : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 0,
      rawStatementAtom closeStatement, .symbol "scope-underflow",
      locatedByteSpanAtom closeSite]

theorem closeUnderflow_rejects_without_advancing :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 underflowProgram).1
    underflowRejectedAtom ∈ final /\
      sourceControlAtom fixtureOwner 1 ∉ final := by
  decide +kernel

private def semanticOpenState : SourceState :=
  { initialState with
    scopes :=
      [{ activeVariableLength := 0
         activeHypothesisLength := 0
         activeDistinctLength := 0 }] }

theorem fixture_source_open_applies :
    openScope? initialState = some semanticOpenState := by
  decide

theorem fixture_source_open_inhabits_ntt :
    sourceScopeOSLF.satisfies initialState
      (sourceScopeNTT semanticOpenState).pred :=
  openScope_inhabits_source_native_type fixture_source_open_applies

private def semanticCloseBefore : SourceState :=
  { semanticOpenState with
    declaredVariables := ["x"]
    activeVariables := ["x"] }

private def semanticCloseMiddle : SourceState :=
  { initialState with
    declaredVariables := ["x"]
    pendingBlockCompletions := 1 }

private def semanticCloseAfter : SourceState :=
  { initialState with declaredVariables := ["x"] }

theorem fixture_source_close_applies :
    closeScope? semanticCloseBefore = some semanticCloseMiddle := by
  decide

theorem fixture_source_complete_applies :
    completeBlock? semanticCloseMiddle = some semanticCloseAfter := by
  decide

theorem fixture_source_close_two_step_ntt :
    sourceScopeOSLF.satisfies semanticCloseBefore
        (sourceScopeNTT semanticCloseMiddle).pred /\
      sourceScopeOSLF.satisfies semanticCloseMiddle
        (sourceScopeNTT semanticCloseAfter).pred := by
  exact
    ⟨closeScope_inhabits_source_native_type fixture_source_close_applies,
      completeBlock_inhabits_source_native_type fixture_source_complete_applies⟩

section AxiomAudit

#print axioms decodeActiveHypothesisLinkAtom_activeHypothesisLinkAtom
#print axioms decodeActiveHypothesisLinkAtom_eq_none_of_runtime_ne
#print axioms activeHypothesisLinkAtom_injective
#print axioms openScope_inhabits_source_native_type
#print axioms closeScope_inhabits_source_native_type
#print axioms completeBlock_inhabits_source_native_type
#print axioms closeScope_restores_three_active_prefixes
#print axioms scopeCheckpointAtom_injective
#print axioms scopeExecutionRules_extract_exact
#print axioms openProgram_completes_exact_checkpoint
#print axioms openProgram_has_oslf_native_trace
#print axioms closeProgram_restores_exact_active_prefix
#print axioms closeProgram_has_oslf_native_trace
#print axioms closeInertDistinctProgram_pops_without_runtime_rows
#print axioms closeInertDistinctProgram_has_oslf_native_trace
#print axioms closeDuplicateDistinctProgram_preserves_shared_capability
#print axioms closeDuplicateDistinctProgram_has_oslf_native_trace
#print axioms distinctPop_rejects_mismatched_occurrence_pair
#print axioms closeUnderflow_rejects_without_advancing
#print axioms fixture_source_close_two_step_ntt

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceScopeExecution
