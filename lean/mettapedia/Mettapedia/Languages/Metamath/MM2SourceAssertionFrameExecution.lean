import Mettapedia.Languages.Metamath.MM2SourceAssertionFrame
import Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Native assertion-frame snapshot execution

This module begins the ordinary-MM2 transaction for a source `$a`
declaration.  It checks the raw formula through the shared source formula
validator, then snapshots the active hypothesis and distinct-variable ledgers
in chronological order.  Ledger links are read newest-first and prepended to
the transaction accumulator, implementing `prependReverseSnapshot`.

No assertion runtime row is published here.  The resulting snapshot remains
private until the certificate and candidate frame have been checked by later
transaction stages.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Typed transaction context -/

/-- Source-bound semantic data retained after the current row and passive
candidate are consumed.  Source resumption is authorized separately by the
captured reload rule and the ordinary successor protocol. -/
structure AssertionFrameContext where
  position : Nat
  nextPosition : Nat
  statement : RawStatement
  assertionPosition : Nat
  nextAssertionPosition : Nat
  certificate : List String
  assertion : SourceAssertion
deriving DecidableEq

def assertionFrameContextAtom (context : AssertionFrameContext) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context",
      natAtom context.position, natAtom context.nextPosition,
      rawStatementAtom context.statement, natAtom context.assertionPosition,
      natAtom context.nextAssertionPosition,
      listAtom stringAtom context.certificate,
      sourceAssertionAtom context.assertion]

def decodeAssertionFrameContextAtom : Atom -> Option AssertionFrameContext
  | .expression
      [.symbol tag, encodedPosition, encodedNextPosition, encodedStatement,
        encodedAssertionPosition,
        encodedNextAssertionPosition,
        encodedCertificate, encodedAssertion] => do
      guard (tag == "mm-internal-source-assertion-frame-context")
      let position <- decodeNatAtom encodedPosition
      let nextPosition <- decodeNatAtom encodedNextPosition
      let statement <- decodeRawStatementAtom encodedStatement
      let assertionPosition <- decodeNatAtom encodedAssertionPosition
      let nextAssertionPosition <-
        decodeNatAtom encodedNextAssertionPosition
      let certificate <- decodeListAtom decodeStringAtom encodedCertificate
      let assertion <- decodeSourceAssertionAtom encodedAssertion
      pure
        { position, nextPosition, statement, assertionPosition,
          nextAssertionPosition, certificate, assertion }
  | _ => none

@[simp] theorem decodeAssertionFrameContextAtom_encoded
    (context : AssertionFrameContext) :
    decodeAssertionFrameContextAtom (assertionFrameContextAtom context) =
      some context := by
  cases context
  simp [decodeAssertionFrameContextAtom, assertionFrameContextAtom]

theorem assertionFrameContextAtom_injective :
    Function.Injective assertionFrameContextAtom := by
  intro left right equal
  have decoded := congrArg decodeAssertionFrameContextAtom equal
  simpa using decoded

def assertionFrameRunningAtom (owner hypothesisFrontier distinctFrontier : Atom)
    (context : AssertionFrameContext) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-running", owner,
      assertionFrameContextAtom context, hypothesisFrontier,
      distinctFrontier]

def assertionHypothesisSnapshotControlAtom (owner cursor snapshot
    distinctFrontier : Atom) (context : AssertionFrameContext) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-hypothesis-snapshot", owner,
      assertionFrameContextAtom context, cursor, snapshot, distinctFrontier]

def assertionDistinctSnapshotControlAtom (owner hypothesisSnapshot cursor
    snapshot : Atom) (context : AssertionFrameContext) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-distinct-snapshot", owner,
      assertionFrameContextAtom context, hypothesisSnapshot, cursor, snapshot]

def assertionFrameSnapshotAtom (owner hypothesisSnapshot distinctSnapshot : Atom)
    (context : AssertionFrameContext) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-snapshot", owner,
      assertionFrameContextAtom context, hypothesisSnapshot, distinctSnapshot]

def assertionPhaseReloadTriggerAtom (phase : String) (owner : Atom) : Atom :=
  .expression [.symbol ("mm-reload-source-assertion-" ++ phase), owner]

def assertionFrameReloadTriggerAtom (owner : Atom) : Atom :=
  assertionPhaseReloadTriggerAtom "frame" owner

def assertionCertificateReloadCapabilityRow (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-reloader", rule]

/-! ## Ordinary MM2 templates -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-assertion-frame-start"
private def formulaFaultLocation :=
  location "04" "mm-source-assertion-frame-formula-fault"
private def formulaCompleteLocation :=
  location "04" "mm-source-assertion-frame-formula-complete"
private def hypothesisFloatingLocation :=
  location "05" "mm-source-assertion-frame-hypothesis-floating"
private def hypothesisEssentialLocation :=
  location "05" "mm-source-assertion-frame-hypothesis-essential"
private def hypothesisDoneLocation :=
  location "05" "mm-source-assertion-frame-hypothesis-done"
private def distinctFirstLiveLocation :=
  location "06" "mm-source-assertion-frame-distinct-first-live"
private def distinctFirstInertLocation :=
  location "06" "mm-source-assertion-frame-distinct-first-inert"
private def distinctDuplicateLocation :=
  location "06" "mm-source-assertion-frame-distinct-duplicate"
private def distinctDoneLocation :=
  location "06" "mm-source-assertion-frame-distinct-done"
private def reloadLocation :=
  location "34" "mm-source-assertion-frame-reload"

def assertionFrameFormulaValidationKey : Atom :=
  .symbol "mm-source-assertion-frame-formula"

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def labelTemplate : Atom := locatedNameTemplate "assertion-label"
private def typecodeTemplate : Atom := locatedNameTemplate "assertion-typecode"

private def axiomStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-axiom", .var "declaration-site", labelTemplate,
      typecodeTemplate, .var "raw-body", .var "declaration-terminator"]

private def formulaTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "assertion-typecode-name",
      .var "encoded-body"]

private def frameTemplate : Atom :=
  .expression
    [.symbol "mm-frame", .var "candidate-distinct-variables",
      .var "candidate-hypothesis-labels"]

private def assertionTemplate : Atom :=
  .expression
    [.symbol "mm-assertion", .var "assertion-label-name", formulaTemplate,
      frameTemplate, .var "candidate-hypotheses"]

private def contextTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context", .var "position",
      .var "next-position", axiomStatementTemplate, .var "assertion-position",
      .var "next-assertion-position",
      .var "mandatory-variables", assertionTemplate]

private def currentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", axiomStatementTemplate, .var "dispatch-input",
      .var "dispatch-output"]

private def candidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-assertion-candidate", .var "source",
      .var "position", .var "next-position", axiomStatementTemplate,
      .var "assertion-position", .var "next-assertion-position",
      .symbol "mm-source-action-immediate",
      .var "mandatory-variables", assertionTemplate]

private def environmentTemplate : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "source", .var "scope-stack",
      .var "next-hypothesis", .var "assertion-position"]

private def hypothesisOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]

private def distinctOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-distinct-ledger", .var "source"]

private def hypothesisFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate,
      .var "hypothesis-frontier"]

private def distinctFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", distinctOwnerTemplate,
      .var "distinct-frontier"]

private def runningTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-running", .var "source",
      contextTemplate, .var "hypothesis-frontier", .var "distinct-frontier"]

private def formulaRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-request", .var "source",
      .var "position", assertionFrameFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate]

private def formulaCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-complete", .var "source",
      .var "position", assertionFrameFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate]

private def formulaFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-fault", .var "source",
      .var "position", assertionFrameFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate, .var "formula-fault-reason"]

private def hypothesisSnapshotControlTemplate (cursor snapshot : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-hypothesis-snapshot",
      .var "source", contextTemplate, cursor, snapshot,
      .var "distinct-frontier"]

private def currentHypothesisSnapshotControlTemplate : Atom :=
  hypothesisSnapshotControlTemplate (.var "hypothesis-cursor")
    (.var "hypothesis-snapshot")

private def previousHypothesisSnapshotControlTemplate
    (encodedHypothesis : Atom) : Atom :=
  hypothesisSnapshotControlTemplate (.var "previous-hypothesis-cursor")
    (.expression
      [.symbol "mm-cons", encodedHypothesis, .var "hypothesis-snapshot"])

private def floatingHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-floating", .var "hypothesis-label",
      .var "hypothesis-typecode", .var "hypothesis-variable"]

private def floatingRuntimeTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "source",
      .var "hypothesis-label",
      .expression
        [.symbol "mm-formula", .var "hypothesis-typecode",
          .expression
            [.symbol "mm-cons",
              .expression
                [.symbol "mm-variable", .var "hypothesis-variable"],
              nilTemplate]]]

private def essentialHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-essential", .var "hypothesis-label",
      .var "hypothesis-formula"]

private def essentialRuntimeTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "source",
      .var "hypothesis-label", .var "hypothesis-formula"]

private def hypothesisLinkTemplate (encodedHypothesis runtimeRow : Atom) : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", hypothesisOwnerTemplate,
      .var "previous-hypothesis-cursor", .var "hypothesis-cursor",
      encodedHypothesis, runtimeRow]

private def distinctSnapshotControlTemplate
    (cursor snapshot : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-distinct-snapshot",
      .var "source", contextTemplate, .var "hypothesis-snapshot", cursor,
      snapshot]

private def currentDistinctSnapshotControlTemplate : Atom :=
  distinctSnapshotControlTemplate (.var "distinct-cursor")
    (.var "distinct-snapshot")

private def pairTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "distinct-left-name",
      .var "distinct-right-name"]

private def previousDistinctSnapshotControlTemplate : Atom :=
  distinctSnapshotControlTemplate (.var "previous-distinct-cursor")
    (.expression [.symbol "mm-cons", pairTemplate, .var "distinct-snapshot"])

private def distinctLinkTemplate (occurrence : DVOccurrenceKind)
    (capability : ActiveDistinctCapabilityKind) : Atom :=
  .expression
    [.symbol "mm-source-active-distinct-link", distinctOwnerTemplate,
      .var "previous-distinct-cursor", .var "distinct-cursor",
      dvOccurrenceKindAtom occurrence,
      activeDistinctCapabilityKindAtom capability,
      .expression
        [.symbol "mm-caller-dv", .var "source", .var "distinct-left-name",
          .var "distinct-right-name"],
      .expression
        [.symbol "mm-caller-dv", .var "source", .var "distinct-right-name",
          .var "distinct-left-name"]]

private def completedSnapshotTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-snapshot", .var "source",
      contextTemplate, .var "hypothesis-snapshot", .var "distinct-snapshot"]

private def rejectedTemplate (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source", .var "position",
      axiomStatementTemplate, reason, evidence]

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

private def mkDirective (atom loc : Atom) (priority : Nat) (name : String)
    (patterns : List Atom) (sinks : List Sink) : SourceExecFact :=
  { atom
    loc
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def frameReloadRuleCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-reloader",
      .var "assertion-frame-reload-rule"]

private def certificateReloadRuleCaptureTemplate : Atom :=
  assertionCertificateReloadCapabilityRow
    (.var "assertion-certificate-reload-rule")

private def persistentRule (loc : Atom) (priority : Nat) (name stem : String)
    (patterns : List Atom) (sinks : List Sink) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let allPatterns := self :: frameReloadRuleCaptureTemplate :: patterns
  let allSinks :=
    .add self ::
      .add (.var "assertion-frame-reload-rule") ::
      .add (assertionFrameReloadTriggerAtom (.var "source")) :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc priority name allPatterns allSinks)

/-! ## Formula validation and ledger snapshot rules -/

private def startPair : Atom × SourceExecFact :=
  persistentRule startLocation 2 "mm-source-assertion-frame-start"
    "assertion-frame-start"
    [currentTemplate, candidateTemplate, environmentTemplate,
      hypothesisFrontierTemplate, distinctFrontierTemplate]
    [.remove currentTemplate, .remove candidateTemplate,
      .add runningTemplate, .add formulaRequestTemplate]

def assertionFrameStartRule : Atom := startPair.1
def assertionFrameStartDirective : SourceExecFact := startPair.2

private def formulaFaultPair : Atom × SourceExecFact :=
  persistentRule formulaFaultLocation 4
    "mm-source-assertion-frame-formula-fault" "assertion-frame-formula-fault"
    [runningTemplate, formulaFaultTemplate]
    [.remove runningTemplate, .remove formulaFaultTemplate,
      .add (rejectedTemplate (.symbol "invalid-assertion-formula")
        (.var "formula-fault-reason"))]

def assertionFrameFormulaFaultRule : Atom := formulaFaultPair.1
def assertionFrameFormulaFaultDirective : SourceExecFact := formulaFaultPair.2

private def formulaCompletePair : Atom × SourceExecFact :=
  persistentRule formulaCompleteLocation 4
    "mm-source-assertion-frame-formula-complete"
    "assertion-frame-formula-complete"
    [runningTemplate, formulaCompleteTemplate]
    [.remove runningTemplate, .remove formulaCompleteTemplate,
      .add (hypothesisSnapshotControlTemplate (.var "hypothesis-frontier")
        nilTemplate)]

def assertionFrameFormulaCompleteRule : Atom := formulaCompletePair.1
def assertionFrameFormulaCompleteDirective : SourceExecFact :=
  formulaCompletePair.2

private def hypothesisFloatingPair : Atom × SourceExecFact :=
  persistentRule hypothesisFloatingLocation 5
    "mm-source-assertion-frame-hypothesis-floating"
    "assertion-frame-hypothesis-floating"
    [currentHypothesisSnapshotControlTemplate,
      hypothesisLinkTemplate floatingHypothesisTemplate
        floatingRuntimeTemplate]
    [.remove currentHypothesisSnapshotControlTemplate,
      .add (previousHypothesisSnapshotControlTemplate
        floatingHypothesisTemplate)]

def assertionFrameHypothesisFloatingRule : Atom := hypothesisFloatingPair.1
def assertionFrameHypothesisFloatingDirective : SourceExecFact :=
  hypothesisFloatingPair.2

private def hypothesisEssentialPair : Atom × SourceExecFact :=
  persistentRule hypothesisEssentialLocation 5
    "mm-source-assertion-frame-hypothesis-essential"
    "assertion-frame-hypothesis-essential"
    [currentHypothesisSnapshotControlTemplate,
      hypothesisLinkTemplate essentialHypothesisTemplate
        essentialRuntimeTemplate]
    [.remove currentHypothesisSnapshotControlTemplate,
      .add (previousHypothesisSnapshotControlTemplate
        essentialHypothesisTemplate)]

def assertionFrameHypothesisEssentialRule : Atom := hypothesisEssentialPair.1
def assertionFrameHypothesisEssentialDirective : SourceExecFact :=
  hypothesisEssentialPair.2

private def hypothesisDonePair : Atom × SourceExecFact :=
  persistentRule hypothesisDoneLocation 5
    "mm-source-assertion-frame-hypothesis-done"
    "assertion-frame-hypothesis-done"
    [hypothesisSnapshotControlTemplate objectRootKey
      (.var "hypothesis-snapshot")]
    [.remove (hypothesisSnapshotControlTemplate objectRootKey
        (.var "hypothesis-snapshot")),
      .add (distinctSnapshotControlTemplate (.var "distinct-frontier")
        nilTemplate)]

def assertionFrameHypothesisDoneRule : Atom := hypothesisDonePair.1
def assertionFrameHypothesisDoneDirective : SourceExecFact :=
  hypothesisDonePair.2

private def distinctPair (loc : Atom) (priority : Nat) (name stem : String)
    (occurrence : DVOccurrenceKind)
    (capability : ActiveDistinctCapabilityKind) : Atom × SourceExecFact :=
  persistentRule loc priority name stem
    [currentDistinctSnapshotControlTemplate,
      distinctLinkTemplate occurrence capability]
    [.remove currentDistinctSnapshotControlTemplate,
      .add previousDistinctSnapshotControlTemplate]

def assertionFrameDistinctFirstLiveRule : Atom :=
  (distinctPair distinctFirstLiveLocation 6
    "mm-source-assertion-frame-distinct-first-live"
    "assertion-frame-distinct-first-live" .first .live).1
def assertionFrameDistinctFirstLiveDirective : SourceExecFact :=
  (distinctPair distinctFirstLiveLocation 6
    "mm-source-assertion-frame-distinct-first-live"
    "assertion-frame-distinct-first-live" .first .live).2

def assertionFrameDistinctFirstInertRule : Atom :=
  (distinctPair distinctFirstInertLocation 6
    "mm-source-assertion-frame-distinct-first-inert"
    "assertion-frame-distinct-first-inert" .first .inert).1
def assertionFrameDistinctFirstInertDirective : SourceExecFact :=
  (distinctPair distinctFirstInertLocation 6
    "mm-source-assertion-frame-distinct-first-inert"
    "assertion-frame-distinct-first-inert" .first .inert).2

def assertionFrameDistinctDuplicateRule : Atom :=
  (distinctPair distinctDuplicateLocation 6
    "mm-source-assertion-frame-distinct-duplicate"
    "assertion-frame-distinct-duplicate" .duplicate .shared).1
def assertionFrameDistinctDuplicateDirective : SourceExecFact :=
  (distinctPair distinctDuplicateLocation 6
    "mm-source-assertion-frame-distinct-duplicate"
    "assertion-frame-distinct-duplicate" .duplicate .shared).2

private def distinctDonePair : Atom × SourceExecFact :=
  persistentRule distinctDoneLocation 6
    "mm-source-assertion-frame-distinct-done"
    "assertion-frame-distinct-done"
    [distinctSnapshotControlTemplate objectRootKey
      (.var "distinct-snapshot"), certificateReloadRuleCaptureTemplate]
    [.remove (distinctSnapshotControlTemplate objectRootKey
        (.var "distinct-snapshot")),
      .add completedSnapshotTemplate,
      .add (.var "assertion-certificate-reload-rule"),
      .add (assertionPhaseReloadTriggerAtom "certificate" (.var "source"))]

def assertionFrameDistinctDoneRule : Atom := distinctDonePair.1
def assertionFrameDistinctDoneDirective : SourceExecFact := distinctDonePair.2

def assertionFrameSnapshotRules : List Atom :=
  [assertionFrameStartRule, assertionFrameFormulaFaultRule,
   assertionFrameFormulaCompleteRule,
   assertionFrameHypothesisFloatingRule,
   assertionFrameHypothesisEssentialRule,
   assertionFrameHypothesisDoneRule,
   assertionFrameDistinctFirstLiveRule,
   assertionFrameDistinctFirstInertRule,
   assertionFrameDistinctDuplicateRule,
   assertionFrameDistinctDoneRule]

def assertionFrameSnapshotDirectives : List SourceExecFact :=
  [assertionFrameStartDirective, assertionFrameFormulaFaultDirective,
   assertionFrameFormulaCompleteDirective,
   assertionFrameHypothesisFloatingDirective,
   assertionFrameHypothesisEssentialDirective,
   assertionFrameHypothesisDoneDirective,
   assertionFrameDistinctFirstLiveDirective,
   assertionFrameDistinctFirstInertDirective,
   assertionFrameDistinctDuplicateDirective,
   assertionFrameDistinctDoneDirective]

/-- Every variable authored in an assertion-frame transaction sink is
inherited from that directive's input.  The transaction therefore cannot
mint an unresolved data variable. -/
theorem assertionFrameSnapshotDirectives_dataVariablesInherited :
    (assertionFrameSnapshotDirectives.all fun directive =>
      ruleSinksVariablesInherited directive.rule.input
        directive.rule.tmpl.sinks) = true := by
  decide

theorem assertionFrameSnapshotRules_extract_exact :
    assertionFrameSnapshotRules.filterMap extractSupportedSourceExecFact =
      assertionFrameSnapshotDirectives := by
  rfl

/-! ## Finite inventory and opaque reload -/

private def snapshotRuleKinds : List String :=
  ["start", "formula-fault", "formula-complete", "hypothesis-floating",
   "hypothesis-essential", "hypothesis-done", "distinct-first-live",
   "distinct-first-inert", "distinct-duplicate", "distinct-done"]

private def snapshotRuleVariables : List String :=
  ["frame-rule-start", "frame-rule-formula-fault",
   "frame-rule-formula-complete", "frame-rule-hypothesis-floating",
   "frame-rule-hypothesis-essential", "frame-rule-hypothesis-done",
   "frame-rule-distinct-first-live", "frame-rule-distinct-first-inert",
   "frame-rule-distinct-duplicate", "frame-rule-distinct-done"]

def assertionFrameRuleCaptureRow (kind : String) (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-rule", .symbol kind, rule]

private def assertionFrameRuleCaptureTemplate
    (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-rule", .symbol kind,
      .var variableName]

def assertionFrameRuleCaptureRows : List Atom :=
  List.zipWith assertionFrameRuleCaptureRow snapshotRuleKinds
    assertionFrameSnapshotRules

private def reloadTriggerTemplate : Atom :=
  assertionFrameReloadTriggerAtom (.var "source")

private def reloadPatterns : List Atom :=
  reloadTriggerTemplate ::
    List.zipWith assertionFrameRuleCaptureTemplate snapshotRuleKinds
      snapshotRuleVariables

private def reloadSinks : List Sink :=
  [.remove reloadTriggerTemplate] ++
    snapshotRuleVariables.map fun variableName => .add (.var variableName)

def assertionFrameReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def assertionFrameReloadDirective : SourceExecFact :=
  { atom := assertionFrameReloadRule
    loc := reloadLocation
    rule :=
      { priority := 34
        name := "mm-source-assertion-frame-reload"
        input := .compat (mkPattern reloadPatterns)
        guards := []
        tmpl := mkTemplate reloadSinks } }

theorem extract_assertionFrameReloadRule_exact :
    extractSupportedSourceExecFact assertionFrameReloadRule =
      some assertionFrameReloadDirective := by
  rfl

def assertionFrameReloadRuleCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-reloader",
      assertionFrameReloadRule]

def assertionFrameFormulaContinuationRows : List Atom :=
  [formulaValidationFaultContinuationRow assertionFrameFormulaValidationKey
      assertionFrameFormulaFaultRule,
   formulaValidationCompleteContinuationRow assertionFrameFormulaValidationKey
      assertionFrameFormulaCompleteRule]

def assertionFrameSnapshotStaticRows : List Atom :=
  assertionFrameFormulaContinuationRows ++ assertionFrameRuleCaptureRows ++
    [assertionFrameReloadRuleCaptureRow]

theorem assertionFrameFormulaContinuationRows_not_proofNeutral
    {row : Atom} (member : row ∈ assertionFrameFormulaContinuationRows) :
    isProofNeutralInitialAtom row = false := by
  simp only [assertionFrameFormulaContinuationRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact formulaValidationFaultContinuationRow_not_proofNeutral _ _
  · exact formulaValidationCompleteContinuationRow_not_proofNeutral _ _

/-! ## Focused scheduled and hostile controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "assertion-frame.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureStatement : RawStatement :=
  .axiomatic (fixtureSpan 0 2) (fixtureName "ax" 3 5)
    (fixtureName "wff" 6 9) [] (fixtureSpan 10 12)

private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [] }

private def fixtureAssertion : SourceAssertion :=
  { label := "ax"
    formula := fixtureFormula
    frame := { distinctVariables := [], hypothesisLabels := [] }
    hypotheses := [] }

private def fixtureContext : AssertionFrameContext :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    certificate := []
    assertion := fixtureAssertion }

private def fixtureOwner : Atom := .symbol "assertion-frame-source"

private def fixtureCandidate : SourceAssertionCandidate :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    gate := .immediate
    mandatoryVariables := []
    assertion := fixtureAssertion }

private def fixtureCurrent : Atom :=
  .expression
    [.symbol "mm-source-current", fixtureOwner, natAtom 2, natAtom 3,
      rawStatementAtom fixtureStatement, .symbol "dispatch-input",
      .symbol "dispatch-output"]

private def startCanaryAtoms : List Atom :=
  [assertionFrameStartRule, assertionFrameReloadRuleCaptureRow, fixtureCurrent,
   sourceAssertionCandidateAtom fixtureOwner fixtureCandidate,
   sourceInitialEnvironmentAtom fixtureOwner,
   sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
      objectRootKey,
   sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
      objectRootKey]

private def startCanarySpace : Space := startCanaryAtoms.toFinset

private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel

private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms =
      [assertionFrameStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some assertionFrameStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms assertionFrameStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          assertionFrameStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

theorem startCanary_emits_source_bound_formula_request :
    assertionFrameRunningAtom fixtureOwner objectRootKey objectRootKey
        fixtureContext ∈
      cFireReflectiveSourceExecFact startCanaryAtoms
        assertionFrameStartDirective /\
    formulaValidationRequestAtom fixtureOwner 2
        assertionFrameFormulaValidationKey (fixtureName "wff" 6 9) []
        (formulaAtom fixtureFormula) ∈
      cFireReflectiveSourceExecFact startCanaryAtoms
        assertionFrameStartDirective := by
  decide +kernel

private def wrongGateCandidate : SourceAssertionCandidate :=
  { fixtureCandidate with gate := .afterProof }

theorem startPattern_rejects_afterProof_candidate_for_axiom :
    cmatchInputSpec []
      [assertionFrameStartRule, fixtureCurrent,
       assertionFrameReloadRuleCaptureRow,
       sourceAssertionCandidateAtom fixtureOwner wrongGateCandidate,
       sourceInitialEnvironmentAtom fixtureOwner,
       sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
         objectRootKey,
       sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
         objectRootKey]
      assertionFrameStartDirective.rule.input = [] := by
  decide +kernel

private def floatingHypothesis : HypothesisView :=
  .floating "vx" "setvar" "x"

private def hypothesisSnapshotControl : Atom :=
  assertionHypothesisSnapshotControlAtom fixtureOwner
    (stringAtom "vx") (listAtom id []) objectRootKey fixtureContext

private def exactFloatingLink : Atom :=
  activeHypothesisLinkAtom fixtureOwner objectRootKey (stringAtom "vx")
    floatingHypothesis

private def floatingSnapshotCanaryAtoms : List Atom :=
  [assertionFrameHypothesisFloatingRule, assertionFrameReloadRuleCaptureRow,
   hypothesisSnapshotControl,
   exactFloatingLink]

theorem floatingSnapshot_prepends_exact_hypothesis :
    assertionHypothesisSnapshotControlAtom fixtureOwner objectRootKey
        (listAtom hypothesisAtom [floatingHypothesis]) objectRootKey
        fixtureContext ∈
      cFireReflectiveSourceExecFact floatingSnapshotCanaryAtoms
        assertionFrameHypothesisFloatingDirective := by
  decide +kernel

private def forgedFloatingLink : Atom :=
  activeHypothesisLinkRawAtom fixtureOwner objectRootKey (stringAtom "vx")
    (hypothesisAtom floatingHypothesis)
    (hypothesisLookupRow fixtureOwner
      (.floating "vx" "class" "x"))

theorem floatingSnapshot_rejects_inconsistent_runtime_row :
    cmatchInputSpec []
      [assertionFrameHypothesisFloatingRule, hypothesisSnapshotControl,
       assertionFrameReloadRuleCaptureRow,
       forgedFloatingLink]
      assertionFrameHypothesisFloatingDirective.rule.input = [] := by
  decide +kernel

private def distinctControl : Atom :=
  assertionDistinctSnapshotControlAtom fixtureOwner (listAtom id [])
    (stringAtom "d1") (listAtom id []) fixtureContext

private def distinctLink : Atom :=
  activeDistinctLinkAtom fixtureOwner objectRootKey (stringAtom "d1")
    .duplicate .shared
    (.expression
      [.symbol "mm-caller-dv", fixtureOwner, stringAtom "x", stringAtom "y"])
    (.expression
      [.symbol "mm-caller-dv", fixtureOwner, stringAtom "y", stringAtom "x"])

private def distinctSnapshotCanaryAtoms : List Atom :=
  [assertionFrameDistinctDuplicateRule, assertionFrameReloadRuleCaptureRow,
   distinctControl, distinctLink]

theorem distinctSnapshot_preserves_duplicate_occurrence :
    assertionDistinctSnapshotControlAtom fixtureOwner (listAtom id [])
        objectRootKey (listAtom stringPairAtom [("x", "y")]) fixtureContext ∈
      cFireReflectiveSourceExecFact distinctSnapshotCanaryAtoms
        assertionFrameDistinctDuplicateDirective := by
  decide +kernel

private def continuousEssentialHypothesis : HypothesisView :=
  .essential "e1"
    { typecode := "wff", body := [.var "x", .var "y"] }

private def continuousFloatingFrontier : Atom := stringAtom "vx"
private def continuousEssentialFrontier : Atom := stringAtom "e1"
private def continuousDistinctFirstFrontier : Atom := stringAtom "d1"
private def continuousDistinctDuplicateFrontier : Atom := stringAtom "d2"

private def continuousLeftRow : Atom :=
  .expression
    [.symbol "mm-caller-dv", fixtureOwner, stringAtom "x", stringAtom "y"]

private def continuousRightRow : Atom :=
  .expression
    [.symbol "mm-caller-dv", fixtureOwner, stringAtom "y", stringAtom "x"]

private def continuousSnapshotProgram : List Atom :=
  assertionFrameSnapshotRules ++
    [assertionFrameReloadRuleCaptureRow,
     assertionCertificateReloadCapabilityRow
       (.symbol "certificate-reload-rule"),
     assertionHypothesisSnapshotControlAtom fixtureOwner
        continuousEssentialFrontier (listAtom id [])
        continuousDistinctDuplicateFrontier fixtureContext,
     activeHypothesisLinkAtom fixtureOwner objectRootKey
       continuousFloatingFrontier floatingHypothesis,
     activeHypothesisLinkAtom fixtureOwner continuousFloatingFrontier
       continuousEssentialFrontier continuousEssentialHypothesis,
     activeDistinctLinkAtom fixtureOwner objectRootKey
       continuousDistinctFirstFrontier .first .live
       continuousLeftRow continuousRightRow,
     activeDistinctLinkAtom fixtureOwner continuousDistinctFirstFrontier
       continuousDistinctDuplicateFrontier .duplicate .shared
       continuousLeftRow continuousRightRow]

private def continuousExpectedHypotheses : Atom :=
  listAtom hypothesisAtom [floatingHypothesis, continuousEssentialHypothesis]

private def continuousExpectedDistinct : Atom :=
  listAtom stringPairAtom [("x", "y"), ("x", "y")]

/-- The data path followed by the scheduled snapshot rules has the exact
chronological target.  This symbolic receipt is deliberately separate from
the executable `RunN` trace below, avoiding whole-trace normalization. -/
theorem continuousSnapshot_reference_order_exact :
    Mettapedia.Languages.Metamath.MM2SourceAssertionFrame.prependReverseSnapshot
        [continuousEssentialHypothesis, floatingHypothesis] =
      [floatingHypothesis, continuousEssentialHypothesis] /\
    Mettapedia.Languages.Metamath.MM2SourceAssertionFrame.prependReverseSnapshot
        [("x", "y"), ("x", "y")] =
      [("x", "y"), ("x", "y")] := by
  decide +kernel

def continuousSnapshotProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 10 continuousSnapshotProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 10
        continuousSnapshotProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 10
    continuousSnapshotProgram

#print axioms decodeAssertionFrameContextAtom_encoded
#print axioms assertionFrameContextAtom_injective
#print axioms assertionFrameSnapshotDirectives_dataVariablesInherited
#print axioms assertionFrameSnapshotRules_extract_exact
#print axioms extract_assertionFrameReloadRule_exact
#print axioms assertionFrameFormulaContinuationRows_not_proofNeutral
#print axioms startCanary_selects_directive
#print axioms startCanary_inhabits_target_native_type
#print axioms startCanary_emits_source_bound_formula_request
#print axioms startPattern_rejects_afterProof_candidate_for_axiom
#print axioms floatingSnapshot_prepends_exact_hypothesis
#print axioms floatingSnapshot_rejects_inconsistent_runtime_row
#print axioms distinctSnapshot_preserves_duplicate_occurrence
#print axioms continuousSnapshot_reference_order_exact
#print axioms continuousSnapshotProgram_has_oslf_native_trace

end Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
