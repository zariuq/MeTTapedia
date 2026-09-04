import Mettapedia.Languages.Metamath.MM2SourceAssertionFrameSelectionExecution

/-!
# Source-derived assertion publication

An admitted assertion candidate determines a finite linked publication plan.
The plan keeps every runtime row wrapped until the formula, certificate, and
frame-selection transactions have produced private validation evidence.  The
publisher then follows an explicit occurrence-successor relation, publishes
one source-derived row per step, advances the source assertion counter, and
restores the ordinary source dispatcher.

This module establishes the generated-input capability boundary: every
payload in a generated publication plan belongs to the exact
`assertionExecutionRowsFor` list computed from that source candidate.  It does
not claim that an arbitrarily authored publication wrapper is authorized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionPublication

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameSelectionExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Pure source-derived plan -/

def assertionPublicationOwnerAtom (owner : Atom) (position : Nat) : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-owner", owner,
      natAtom position]

def assertionPublicationPayloadRows (owner : Atom)
    (candidate : SourceAssertionCandidate) : List Atom :=
  assertionExecutionRowsFor owner candidate.assertionPosition
    candidate.assertion

def assertionPublicationHeaderAtom (owner : Atom)
    (candidate : SourceAssertionCandidate) : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-plan", owner,
      natAtom candidate.position, natAtom candidate.nextPosition,
      rawStatementAtom candidate.statement,
      natAtom candidate.assertionPosition,
      natAtom candidate.nextAssertionPosition,
      listAtom stringAtom candidate.mandatoryVariables,
      sourceAssertionAtom candidate.assertion,
      natAtom (assertionPublicationPayloadRows owner candidate).length]

def assertionPublicationLinkedRows (owner : Atom)
    (candidate : SourceAssertionCandidate) : List Atom :=
  linkedRows "source-assertion-publication"
    (assertionPublicationOwnerAtom owner candidate.position) id
    (assertionPublicationPayloadRows owner candidate)

def assertionPublicationSuccessorRows (owner : Atom)
    (candidate : SourceAssertionCandidate) : List Atom :=
  indexSuccessorRows
    (assertionPublicationOwnerAtom owner candidate.position)
    (assertionPublicationPayloadRows owner candidate).length

def assertionPublicationPlanRows (owner : Atom)
    (candidate : SourceAssertionCandidate) : List Atom :=
  [assertionPublicationHeaderAtom owner candidate] ++
    assertionPublicationLinkedRows owner candidate ++
    assertionPublicationSuccessorRows owner candidate

@[simp] theorem assertionPublicationPayloadRows_length
    (owner : Atom) (candidate : SourceAssertionCandidate) :
    (assertionPublicationPayloadRows owner candidate).length =
      candidate.assertion.hypotheses.length * 2 +
        candidate.assertion.frame.distinctVariables.length * 2 + 3 := by
  simp [assertionPublicationPayloadRows, assertionExecutionRowsFor,
    assertionHypothesisRows, assertionHypothesisSuccessorRows,
    assertionDVPairRows, assertionDVSuccessorRows]
  omega

/-- Every linked payload in a generated plan is selected from the exact
source-derived assertion runtime list, with the canonical successor. -/
theorem mem_assertionPublicationLinkedRows_iff
    (owner : Atom) (candidate : SourceAssertionCandidate) (row : Atom) :
    row ∈ assertionPublicationLinkedRows owner candidate ↔
      ∃ (position : Nat)
          (inBounds : position <
            (assertionPublicationPayloadRows owner candidate).length),
        linkedRow "source-assertion-publication"
          (assertionPublicationOwnerAtom owner candidate.position)
          position (position + 1)
          ((assertionPublicationPayloadRows owner candidate).get
            ⟨position, inBounds⟩) = row := by
  exact mem_linkedRows_iff _ _ _ _ _

theorem assertionPublicationPlanRows_all_proofNeutral
    (owner : Atom) (candidate : SourceAssertionCandidate) :
    (assertionPublicationPlanRows owner candidate).all
      isProofNeutralInitialAtom = true := by
  simp [assertionPublicationPlanRows, assertionPublicationHeaderAtom,
    assertionPublicationLinkedRows, assertionPublicationSuccessorRows,
    isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-! ## Ordinary-MM2 transaction -/

private def publicationFamily : Atom :=
  stringAtom "source-assertion-publication"

private def startLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-source-assertion-publication-start"]

private def addLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-source-assertion-publication-add"]

private def doneLocation : Atom :=
  .expression [.symbol "10", .symbol "mm-source-assertion-publication-done"]

private def reloadLocation : Atom :=
  .expression [.symbol "38", .symbol "mm-source-assertion-publication-reload"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def labelTemplate : Atom := locatedNameTemplate "publication-label"
private def typecodeTemplate : Atom :=
  locatedNameTemplate "publication-typecode"

private def statementTemplate : Atom :=
  .expression
    [.symbol "mm-source-axiom", .var "publication-site", labelTemplate,
      typecodeTemplate, .var "publication-raw-body",
      .var "publication-terminator"]

private def formulaTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "publication-typecode-name",
      .var "publication-formula-body"]

private def frameTemplate : Atom :=
  .expression
    [.symbol "mm-frame", .var "publication-candidate-distinct",
      .var "publication-candidate-labels"]

private def assertionTemplate : Atom :=
  .expression
    [.symbol "mm-assertion", .var "publication-label-name",
      formulaTemplate, frameTemplate,
      .var "publication-candidate-hypotheses"]

private def contextTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context",
      .var "publication-position", .var "publication-next-position",
      statementTemplate,
      .var "publication-assertion-position",
      .var "publication-next-assertion-position",
      .var "publication-mandatory-variables", assertionTemplate]

private def selectionEvidenceTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-valid",
      .var "publication-source", contextTemplate]

private def publicationOwnerTemplate : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-owner",
      .var "publication-source", .var "publication-position"]

private def headerTemplate : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-plan",
      .var "publication-source", .var "publication-position",
      .var "publication-next-position", statementTemplate,
      .var "publication-assertion-position",
      .var "publication-next-assertion-position",
      .var "publication-mandatory-variables", assertionTemplate,
      .var "publication-count"]

private def environmentTemplate (assertionPosition : Atom) : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "publication-source",
      .var "publication-scope-stack", .var "publication-next-hypothesis",
      assertionPosition]

private def runningTemplate (actionPosition : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-running",
      .var "publication-source", contextTemplate,
      .var "publication-scope-stack", .var "publication-next-hypothesis",
      publicationOwnerTemplate, actionPosition,
      .var "publication-count"]

private def linkedTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", publicationFamily,
      publicationOwnerTemplate, .var "publication-action-position",
      .var "publication-next-action-position",
      .var "publication-runtime-row"]

private def successorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", publicationOwnerTemplate,
      .var "publication-action-position",
      .var "publication-next-action-position"]

private def nextSourceControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "publication-source",
      .var "publication-next-position"]

private def statementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "publication-source",
      .var "publication-position", statementTemplate]

private def sourceReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-verifier", .var "publication-source"]

private def publicationReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-assertion-publication",
      .var "publication-source"]

def assertionPublicationReloadTriggerAtom (owner : Atom) : Atom :=
  assertionPhaseReloadTriggerAtom "publication" owner

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-reload",
      .var "publication-source-reload-rule"]

def assertionPublicationSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-reload",
      sourceVerifierReloadRule]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def sinkAtom : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

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

private def publicationReloadRuleCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-reloader",
      .var "assertion-publication-reload-rule"]

private def persistentRule (loc : Atom) (priority : Nat) (name stem : String)
    (patterns : List Atom) (sinks : List Sink) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let allPatterns := self :: publicationReloadRuleCaptureTemplate :: patterns
  let allSinks :=
    .add self ::
      .add (.var "assertion-publication-reload-rule") ::
      .add publicationReloadTriggerTemplate :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc priority name allPatterns allSinks)

private def startPair : Atom × SourceExecFact :=
  persistentRule startLocation 9 "mm-source-assertion-publication-start"
    "assertion-publication-start"
    [selectionEvidenceTemplate, headerTemplate,
      environmentTemplate (.var "publication-assertion-position")]
    [.remove selectionEvidenceTemplate, .remove headerTemplate,
      .remove (environmentTemplate (.var "publication-assertion-position")),
      .add (runningTemplate (natAtom 0))]

def assertionPublicationStartRule : Atom := startPair.1
def assertionPublicationStartDirective : SourceExecFact := startPair.2

private def addPair : Atom × SourceExecFact :=
  persistentRule addLocation 9 "mm-source-assertion-publication-add"
    "assertion-publication-add"
    [runningTemplate (.var "publication-action-position"),
      linkedTemplate, successorTemplate]
    [.remove (runningTemplate (.var "publication-action-position")),
      .remove linkedTemplate, .remove successorTemplate,
      .add (.var "publication-runtime-row"),
      .add (runningTemplate (.var "publication-next-action-position"))]

def assertionPublicationAddRule : Atom := addPair.1
def assertionPublicationAddDirective : SourceExecFact := addPair.2

private def donePair : Atom × SourceExecFact :=
  persistentRule doneLocation 10 "mm-source-assertion-publication-done"
    "assertion-publication-done"
    [runningTemplate (.var "publication-count"),
      sourceReloadCaptureTemplate]
    [.remove (runningTemplate (.var "publication-count")),
      .add (environmentTemplate
        (.var "publication-next-assertion-position")),
      .add nextSourceControlTemplate, .add statementAppliedTemplate,
      .add sourceReloadTriggerTemplate,
      .add (.var "publication-source-reload-rule")]

def assertionPublicationDoneRule : Atom := donePair.1
def assertionPublicationDoneDirective : SourceExecFact := donePair.2

def assertionPublicationRules : List Atom :=
  [assertionPublicationStartRule, assertionPublicationAddRule,
   assertionPublicationDoneRule]

def assertionPublicationDirectives : List SourceExecFact :=
  [assertionPublicationStartDirective, assertionPublicationAddDirective,
   assertionPublicationDoneDirective]

theorem assertionPublicationRules_extract_exact :
    assertionPublicationRules.filterMap extractSupportedSourceExecFact =
      assertionPublicationDirectives := by
  rfl

/-! ## Finite inventory and opaque reload -/

private def publicationRuleKinds : List String :=
  ["start", "add", "done"]

private def publicationRuleVariables : List String :=
  ["publication-rule-start", "publication-rule-add",
   "publication-rule-done"]

def assertionPublicationRuleCaptureRow (kind : String)
    (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-rule",
      .symbol kind, rule]

private def assertionPublicationRuleCaptureTemplate
    (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-rule",
      .symbol kind, .var variableName]

def assertionPublicationRuleCaptureRows : List Atom :=
  List.zipWith assertionPublicationRuleCaptureRow publicationRuleKinds
    assertionPublicationRules

private def reloadPatterns : List Atom :=
  publicationReloadTriggerTemplate ::
    List.zipWith assertionPublicationRuleCaptureTemplate publicationRuleKinds
      publicationRuleVariables

private def reloadSinks : List Sink :=
  [.remove publicationReloadTriggerTemplate] ++
    publicationRuleVariables.map fun variableName => .add (.var variableName)

def assertionPublicationReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def assertionPublicationReloadDirective : SourceExecFact :=
  { atom := assertionPublicationReloadRule
    loc := reloadLocation
    rule :=
      { priority := 38
        name := "mm-source-assertion-publication-reload"
        input := .compat (mkPattern reloadPatterns)
        guards := []
        tmpl := mkTemplate reloadSinks } }

theorem extract_assertionPublicationReloadRule_exact :
    extractSupportedSourceExecFact assertionPublicationReloadRule =
      some assertionPublicationReloadDirective := by
  rfl

def assertionPublicationReloadRuleCaptureRow : Atom :=
  assertionPublicationReloadCapabilityRow assertionPublicationReloadRule

/-! ## Focused generated-plan and scheduled controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "assertion-publication.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureStatement : RawStatement :=
  .axiomatic (fixtureSpan 0 2) (fixtureName "ax" 3 5)
    (fixtureName "wff" 6 9) [] (fixtureSpan 10 12)

private def fixtureAssertion : SourceAssertion :=
  { label := "ax"
    formula := { typecode := "wff", body := [] }
    frame := { distinctVariables := [], hypothesisLabels := [] }
    hypotheses := [] }

private def fixtureCandidate : SourceAssertionCandidate :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    gate := .immediate
    mandatoryVariables := []
    assertion := fixtureAssertion }

private def fixtureContext : AssertionFrameContext :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    certificate := []
    assertion := fixtureAssertion }

private def fixtureOwner : Atom := .symbol "assertion-publication-source"

private def tinyOwner : Atom := .symbol "source"
private def tinyPosition : Atom := .symbol "position"
private def tinyNextPosition : Atom := .symbol "next-position"
private def tinyAssertionPosition : Atom := .symbol "assertion-position"
private def tinyNextAssertionPosition : Atom :=
  .symbol "next-assertion-position"
private def tinyCount : Atom := .symbol "count"

private def tinyStatement : Atom :=
  .expression
    [.symbol "mm-source-axiom", .symbol "site",
      .expression
        [.symbol "mm-source-name", .symbol "label-span",
          .symbol "label-name"],
      .expression
        [.symbol "mm-source-name", .symbol "typecode-span",
          .symbol "typecode-name"],
      .symbol "raw-body", .symbol "terminator"]

private def tinyAssertion : Atom :=
  .expression
    [.symbol "mm-assertion", .symbol "label-name",
      .expression
        [.symbol "mm-formula", .symbol "typecode-name",
          .symbol "formula-body"],
      .expression
        [.symbol "mm-frame", .symbol "candidate-distinct",
          .symbol "candidate-labels"],
      .symbol "candidate-hypotheses"]

private def tinyContext : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context", tinyPosition,
      tinyNextPosition, tinyStatement, tinyAssertionPosition,
      tinyNextAssertionPosition, .symbol "mandatory-variables",
      tinyAssertion]

private def tinyPublicationOwner : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-owner", tinyOwner,
      tinyPosition]

private def tinyRunning (actionPosition : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-running",
      tinyOwner, tinyContext, .symbol "scope-stack",
      .symbol "next-hypothesis", tinyPublicationOwner, actionPosition,
      tinyCount]

private def tinyHeader : Atom :=
  .expression
    [.symbol "mm-source-assertion-publication-plan", tinyOwner,
      tinyPosition, tinyNextPosition, tinyStatement, tinyAssertionPosition,
      tinyNextAssertionPosition, .symbol "mandatory-variables",
      tinyAssertion, tinyCount]

private def tinyEnvironment : Atom :=
  .expression
    [.symbol "mm-source-environment", tinyOwner, .symbol "scope-stack",
      .symbol "next-hypothesis", tinyAssertionPosition]

private def startCanaryProgram : List Atom :=
  [assertionPublicationStartRule, assertionPublicationReloadRuleCaptureRow,
   .expression
     [.symbol "mm-internal-source-assertion-frame-valid", tinyOwner,
       tinyContext],
   tinyHeader, tinyEnvironment]

def startCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact startCanaryProgram
    assertionPublicationStartDirective

theorem startCanary_begins_at_zero_and_consumes_environment :
    tinyRunning (natAtom 0) ∈ startCanaryTarget ∧
      tinyEnvironment ∉ startCanaryTarget := by
  decide +kernel

theorem startCanary_inhabits_exact_native_target :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      startCanaryProgram
      (reflectiveNativeListExactTargetNativeType .leaveInert
        startCanaryTarget).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert startCanaryProgram startCanaryTarget).2
  rfl

private def tinyPayload : Atom := .symbol "runtime-row"

private def tinyLinked (nextPosition : Nat) : Atom :=
  linkedRow "source-assertion-publication" tinyPublicationOwner 0
    nextPosition tinyPayload

private def tinySuccessor : Atom :=
  .expression
    [.symbol "mm-index-successor", tinyPublicationOwner, natAtom 0,
      natAtom 1]

private def addCanaryProgram : List Atom :=
  [assertionPublicationAddRule, assertionPublicationReloadRuleCaptureRow,
   tinyRunning (natAtom 0), tinyLinked 1,
   tinySuccessor]

theorem addCanary_publishes_exact_source_row_and_advances :
    tinyPayload ∈
        cFireReflectiveSourceExecFact addCanaryProgram
          assertionPublicationAddDirective ∧
      tinyRunning (natAtom 1) ∈
        cFireReflectiveSourceExecFact addCanaryProgram
          assertionPublicationAddDirective := by
  decide +kernel

private def forgedSuccessorCanaryProgram : List Atom :=
  [assertionPublicationAddRule, assertionPublicationReloadRuleCaptureRow,
   tinyRunning (natAtom 0), tinyLinked 2,
   tinySuccessor]

theorem forgedSuccessorCanary_cannot_publish :
    tinyPayload ∉
      cFireReflectiveSourceExecFact forgedSuccessorCanaryProgram
        assertionPublicationAddDirective := by
  decide +kernel

private def doneCanaryProgram : List Atom :=
  [assertionPublicationDoneRule, assertionPublicationReloadRuleCaptureRow,
   tinyRunning tinyCount,
   .expression
     [.symbol "mm-internal-source-assertion-publication-reload",
       .symbol "source-reload-rule"]]

def doneCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact doneCanaryProgram
    assertionPublicationDoneDirective

theorem doneCanary_advances_environment_and_source :
    (.expression
      [.symbol "mm-source-environment", tinyOwner,
        .symbol "scope-stack", .symbol "next-hypothesis",
        tinyNextAssertionPosition] : Atom) ∈ doneCanaryTarget ∧
    (.expression
      [.symbol "mm-source-control", tinyOwner,
        tinyNextPosition] : Atom) ∈ doneCanaryTarget ∧
    (.expression
      [.symbol "mm-source-statement-applied", tinyOwner, tinyPosition,
        tinyStatement] : Atom) ∈ doneCanaryTarget := by
  decide +kernel

theorem fixture_plan_payloads_are_exact_assertion_rows :
    assertionPublicationPayloadRows fixtureOwner fixtureCandidate =
      assertionExecutionRowsFor fixtureOwner 0 fixtureAssertion := by
  rfl

#print axioms assertionPublicationPayloadRows_length
#print axioms mem_assertionPublicationLinkedRows_iff
#print axioms assertionPublicationPlanRows_all_proofNeutral
#print axioms assertionPublicationRules_extract_exact
#print axioms extract_assertionPublicationReloadRule_exact
#print axioms startCanary_begins_at_zero_and_consumes_environment
#print axioms startCanary_inhabits_exact_native_target
#print axioms addCanary_publishes_exact_source_row_and_advances
#print axioms forgedSuccessorCanary_cannot_publish
#print axioms doneCanary_advances_environment_and_source
#print axioms fixture_plan_payloads_are_exact_assertion_rows

end Mettapedia.Languages.Metamath.MM2SourceAssertionPublication
