import Mettapedia.Languages.Metamath.MM2SourceActionPlan
import Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution

/-!
# Native `$e` declaration execution in ordinary MM2

An essential-hypothesis declaration is committed only after two independent
checks have completed.  The label lookup proves that the located label is
fresh in the permanent object ledger.  The shared formula validator proves
that the proposed tagged formula agrees with the raw located names and with
the permanent and active-variable ledgers.

The source-data transformation supplies a passive candidate extracted from
the exact source-state action delta.  Execution treats that candidate as
untrusted data: it checks the label and formula before publishing the runtime
hypothesis row or extending the active-hypothesis scope ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.Metamath.SourceStateNativeTypes
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Semantic authority -/

/-- Native execution is licensed by the accepted `$e` transition of the
authored source-state GSLT, classified through its OSLF-derived NTT. -/
theorem essentialDeclaration_inhabits_source_native_type
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (declared : declareEssential? before label formula = some after) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact local_payload_inhabits_exact_target
    (payload := .declareEssential label formula) declared

/-! ## Source-derived passive candidates -/

def essentialCandidateAtom (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (label : LocatedName)
    (candidateFormula : Atom) : Atom :=
  .expression
    [.symbol "mm-source-essential-candidate", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement, candidateFormula,
      .expression
        [.symbol "mm-hypothesis-lookup", owner, stringAtom label.name,
          candidateFormula]]

/-- Extract the one proposed runtime row from the exact source-state delta.
Unexpected deltas produce no candidate and therefore cannot enter native
execution. -/
def essentialCandidateRow? (owner : Atom)
    (plan : StatementActionPlan) : Option Atom :=
  match plan.statement, plan.actions with
  | statement@(.essential _ label _ _ _),
      [.add (.expression
        [.symbol "mm-hypothesis-lookup", actualOwner, actualLabel,
          candidateFormula])] =>
      if actualOwner == owner && actualLabel == stringAtom label.name then
        some (essentialCandidateAtom owner plan.position plan.nextPosition
          statement label candidateFormula)
      else
        none
  | _, _ => none

def essentialCandidateRows (owner : Atom)
    (plans : List StatementActionPlan) : List Atom :=
  plans.filterMap (essentialCandidateRow? owner)

@[simp] theorem essentialCandidateAtom_proofNeutral
    (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (label : LocatedName)
    (candidateFormula : Atom) :
    isProofNeutralInitialAtom
      (essentialCandidateAtom owner position nextPosition statement label
        candidateFormula) = true := by
  simp [essentialCandidateAtom, isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-- Every successfully derived essential-candidate row is passive initial
data. -/
theorem essentialCandidateRow?_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) (row : Atom)
    (derived : essentialCandidateRow? owner plan = some row) :
    isProofNeutralInitialAtom row = true := by
  unfold essentialCandidateRow? at derived
  split at derived <;> simp_all
  obtain ⟨_, rfl⟩ := derived
  apply essentialCandidateAtom_proofNeutral

/-- The complete essential-candidate list is proof-neutral. -/
@[simp] theorem essentialCandidateRows_all_proofNeutral
    (owner : Atom) (plans : List StatementActionPlan) :
    (essentialCandidateRows owner plans).all isProofNeutralInitialAtom =
      true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [essentialCandidateRows, List.mem_filterMap] at member
  obtain ⟨plan, _, derived⟩ := member
  exact essentialCandidateRow?_proofNeutral owner plan row derived

/-! ## Protected transaction observations -/

def essentialRequestAtom (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (label typecode : LocatedName)
    (body : List LocatedName) (candidateFormula : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-request", owner,
      natAtom position, natAtom nextPosition, rawStatementAtom statement,
      locatedNameAtom label, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula]

def essentialControlAtom (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (label typecode : LocatedName)
    (body : List LocatedName) (candidateFormula : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-control", owner,
      natAtom position, natAtom nextPosition, rawStatementAtom statement,
      locatedNameAtom label, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula]

/-! ## Ordinary MM2 templates -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation := location "02" "mm-source-essential-start"
private def labelOccupiedLocation :=
  location "03" "mm-source-essential-label-occupied"
private def labelMissingLocation :=
  location "03" "mm-source-essential-label-missing"
private def formulaFaultLocation :=
  location "04" "mm-source-essential-formula-fault"
private def commitLocation := location "05" "mm-source-essential-commit"

private def essentialLabelLookupKey : Atom :=
  .symbol "mm-source-essential-label-lookup"

private def essentialFormulaValidationKey : Atom :=
  .symbol "mm-source-essential-formula-validation"

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def labelTemplate : Atom := locatedNameTemplate "label"
private def typecodeTemplate : Atom := locatedNameTemplate "typecode"

private def statementTemplate : Atom :=
  .expression
    [.symbol "mm-source-essential", .var "declaration-site", labelTemplate,
      typecodeTemplate, .var "raw-body", .var "declaration-terminator"]

private def formulaTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "typecode-name", .var "encoded-body"]

private def runtimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "source", .var "label-name",
      formulaTemplate]

private def currentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", statementTemplate, .var "dispatch-input",
      .var "dispatch-output"]

private def candidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-essential-candidate", .var "source",
      .var "position", .var "next-position", statementTemplate,
      formulaTemplate, runtimeRowTemplate]

private def requestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-request", .var "source",
      .var "position", .var "next-position", statementTemplate,
      labelTemplate, typecodeTemplate, .var "raw-body", formulaTemplate]

private def controlTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-control", .var "source",
      .var "position", .var "next-position", statementTemplate,
      labelTemplate, typecodeTemplate, .var "raw-body", formulaTemplate]

private def objectFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source",
      .var "object-frontier"]

private def hypothesisOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]

private def hypothesisFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate,
      .var "hypothesis-frontier"]

private def labelLookupTemplate : Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", .var "source",
      essentialLabelLookupKey, requestTemplate, labelTemplate, objectRootKey,
      .var "object-frontier"]

private def labelFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-found", .var "source", requestTemplate,
      labelTemplate, .var "occupied-object"]

private def labelMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-missing", .var "source", requestTemplate,
      labelTemplate]

private def formulaRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-request", .var "source",
      .var "position", essentialFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate]

private def formulaCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-complete", .var "source",
      .var "position", essentialFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate]

private def formulaFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-fault", .var "source",
      .var "position", essentialFormulaValidationKey, typecodeTemplate,
      .var "raw-body", formulaTemplate, .var "formula-fault-reason"]

private def objectReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", .var "source"]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-reload",
      .var "source-verifier-reload-rule"]

def essentialSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-reload", sourceVerifierReloadRule]

private def formulaStartCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-formula-start",
      .var "formula-validation-start-rule"]

def essentialFormulaStartCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-essential-formula-start",
      validationStartRule]

private def labelEntryTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-entry", .symbol "mm-source-object-label",
      labelTemplate]

private def appendedLabelLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "object-frontier",
      labelTemplate, labelEntryTemplate]

private def appendedLabelFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source", labelTemplate]

private def appendedHypothesisLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", hypothesisOwnerTemplate,
      .var "hypothesis-frontier", labelTemplate,
      .expression
        [.symbol "mm-essential", .var "label-name", formulaTemplate],
      runtimeRowTemplate]

private def appendedHypothesisFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate,
      labelTemplate]

private def nextSourceControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def statementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source", .var "position",
      statementTemplate]

private def rejectedTemplate (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source", .var "position",
      statementTemplate, reason, evidence]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def sinkAtom : Sink → Atom
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

private def persistentRule (loc : Atom) (priority : Nat) (name stem : String)
    (patterns : List Atom) (sinks : List Sink) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let allPatterns := self :: patterns
  let allSinks := .add self :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc priority name allPatterns allSinks)

/-! ## Declaration stages -/

private def startPair : Atom × SourceExecFact :=
  persistentRule startLocation 2 "mm-source-essential-start"
    "essential-start" [currentTemplate, candidateTemplate,
      objectFrontierTemplate]
    [.remove currentTemplate, .remove candidateTemplate,
      .add labelLookupTemplate, .add objectReloadTemplate]

def essentialStartRule : Atom := startPair.1
def essentialStartDirective : SourceExecFact := startPair.2

private def labelOccupiedPair : Atom × SourceExecFact :=
  persistentRule labelOccupiedLocation 3
    "mm-source-essential-label-occupied" "essential-label-occupied"
    [labelFoundTemplate]
    [.remove labelFoundTemplate,
      .add (rejectedTemplate (.symbol "occupied-essential-label")
        (.var "occupied-object"))]

def essentialLabelOccupiedRule : Atom := labelOccupiedPair.1
def essentialLabelOccupiedDirective : SourceExecFact := labelOccupiedPair.2

private def labelMissingPair : Atom × SourceExecFact :=
  persistentRule labelMissingLocation 3
    "mm-source-essential-label-missing" "essential-label-missing"
    [labelMissingTemplate, formulaStartCaptureTemplate]
    [.remove labelMissingTemplate, .add controlTemplate,
      .add formulaRequestTemplate,
      .add (.var "formula-validation-start-rule")]

def essentialLabelMissingRule : Atom := labelMissingPair.1
def essentialLabelMissingDirective : SourceExecFact := labelMissingPair.2

private def formulaFaultPair : Atom × SourceExecFact :=
  persistentRule formulaFaultLocation 4
    "mm-source-essential-formula-fault" "essential-formula-fault"
    [controlTemplate, formulaFaultTemplate]
    [.remove controlTemplate, .remove formulaFaultTemplate,
      .add (rejectedTemplate (.symbol "invalid-essential-formula")
        (.var "formula-fault-reason"))]

def essentialFormulaFaultRule : Atom := formulaFaultPair.1
def essentialFormulaFaultDirective : SourceExecFact := formulaFaultPair.2

private def commitPair : Atom × SourceExecFact :=
  persistentRule commitLocation 5 "mm-source-essential-commit"
    "essential-commit"
    [controlTemplate, formulaCompleteTemplate, objectFrontierTemplate,
      hypothesisFrontierTemplate, sourceReloadCaptureTemplate]
    [.remove controlTemplate, .remove formulaCompleteTemplate,
      .remove objectFrontierTemplate, .remove hypothesisFrontierTemplate,
      .add appendedLabelLinkTemplate, .add appendedLabelFrontierTemplate,
      .add runtimeRowTemplate, .add appendedHypothesisLinkTemplate,
      .add appendedHypothesisFrontierTemplate,
      .add nextSourceControlTemplate, .add statementAppliedTemplate,
      .add sourceReloadTemplate,
      .add (.var "source-verifier-reload-rule")]

def essentialCommitRule : Atom := commitPair.1
def essentialCommitDirective : SourceExecFact := commitPair.2

/-! ## Rule inventory and reload rows -/

def essentialDeclarationOwnRules : List Atom :=
  [essentialStartRule, essentialLabelOccupiedRule,
   essentialLabelMissingRule, essentialFormulaFaultRule,
   essentialCommitRule]

def essentialDeclarationOwnDirectives : List SourceExecFact :=
  [essentialStartDirective, essentialLabelOccupiedDirective,
   essentialLabelMissingDirective, essentialFormulaFaultDirective,
   essentialCommitDirective]

def essentialDeclarationRules : List Atom :=
  essentialDeclarationOwnRules ++ formulaValidationRules ++ lookupRules

def essentialDeclarationDirectives : List SourceExecFact :=
  essentialDeclarationOwnDirectives ++ formulaValidationDirectives ++
    lookupDirectives

def essentialLookupStaticRows : List Atom :=
  [objectLookupFoundContinuationRow essentialLabelLookupKey .constant
      essentialLabelOccupiedRule,
   objectLookupFoundContinuationRow essentialLabelLookupKey .variable
      essentialLabelOccupiedRule,
   objectLookupFoundContinuationRow essentialLabelLookupKey .label
      essentialLabelOccupiedRule,
   objectLookupMissingContinuationRow essentialLabelLookupKey
      essentialLabelMissingRule]

def essentialFormulaContinuationStaticRows : List Atom :=
  [formulaValidationFaultContinuationRow essentialFormulaValidationKey
      essentialFormulaFaultRule,
   formulaValidationCompleteContinuationRow essentialFormulaValidationKey
      essentialCommitRule]

def essentialDeclarationStaticRows : List Atom :=
  essentialLookupStaticRows ++ essentialFormulaContinuationStaticRows ++
    formulaValidationStaticRows ++
      [essentialSourceReloadCaptureRow, essentialFormulaStartCaptureRow]

theorem essentialDeclarationRules_extract_exact :
    essentialDeclarationRules.filterMap extractSupportedSourceExecFact =
      essentialDeclarationDirectives := by
  rfl

theorem essentialLookupStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ essentialLookupStaticRows) :
    isProofNeutralInitialAtom row = false := by
  simp only [essentialLookupStaticRows, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact objectLookupFoundContinuationRow_not_proofNeutral _ _ _
  · exact objectLookupFoundContinuationRow_not_proofNeutral _ _ _
  · exact objectLookupFoundContinuationRow_not_proofNeutral _ _ _
  · exact objectLookupMissingContinuationRow_not_proofNeutral _ _

theorem essentialFormulaContinuationStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ essentialFormulaContinuationStaticRows) :
    isProofNeutralInitialAtom row = false := by
  simp only [essentialFormulaContinuationStaticRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact formulaValidationFaultContinuationRow_not_proofNeutral _ _
  · exact formulaValidationCompleteContinuationRow_not_proofNeutral _ _

@[simp] theorem essentialSourceReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom essentialSourceReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-essential-reload" [sourceVerifierReloadRule]
      (by decide)

@[simp] theorem essentialFormulaStartCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom essentialFormulaStartCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-essential-formula-start" [validationStartRule]
      (by decide)

/-! ## Positive and hostile controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "essential.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureSite : LocatedByteSpan := fixtureSpan 0 2
private def fixtureLabel : LocatedName := fixtureName "ex" 3 5
private def fixtureTypecode : LocatedName := fixtureName "wff" 6 9
private def fixtureVariable : LocatedName := fixtureName "x" 10 11
private def fixtureTerminator : LocatedByteSpan := fixtureSpan 12 14
private def fixtureBody : List LocatedName := [fixtureVariable]
private def fixtureStatement : RawStatement :=
  .essential fixtureSite fixtureLabel fixtureTypecode fixtureBody
    fixtureTerminator
private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [.var "x"] }
private def fixtureFormulaAtom : Atom := formulaAtom fixtureFormula
private def fixtureOwner : Atom := .symbol "essential-source"
private def fixtureObjectEntries : List ObjectOccurrence :=
  [{ kind := .constant, occurrence := fixtureTypecode },
   { kind := .variable, occurrence := fixtureVariable }]
private def fixtureObjectFrontier : Atom :=
  objectFrontierKey fixtureObjectEntries
private def fixtureCandidate : Atom :=
  essentialCandidateAtom fixtureOwner 2 3 fixtureStatement fixtureLabel
    fixtureFormulaAtom
private def fixtureCurrent : Atom :=
  .expression
    [.symbol "mm-source-current", fixtureOwner, natAtom 2, natAtom 3,
      rawStatementAtom fixtureStatement, .symbol "dispatch-input",
      .symbol "dispatch-output"]

private def fixturePlan : StatementActionPlan :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    gate := .immediate
    actions :=
      [.add (hypothesisLookupRow fixtureOwner
        (.essential "ex" fixtureFormula))] }

@[simp] theorem essentialCandidateRow?_fixturePlan :
    essentialCandidateRow? fixtureOwner fixturePlan =
      some fixtureCandidate := by
  rfl

private def startCanaryAtoms : List Atom :=
  [essentialStartRule, fixtureCurrent, fixtureCandidate,
   objectFrontierAtom fixtureOwner fixtureObjectFrontier]

private def startCanarySpace : Space := startCanaryAtoms.toFinset

private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel

private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms =
      [essentialStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some essentialStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms essentialStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          essentialStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

private def fixtureRequest : Atom :=
  essentialRequestAtom fixtureOwner 2 3 fixtureStatement fixtureLabel
    fixtureTypecode fixtureBody fixtureFormulaAtom

private def expectedLabelLookup : Atom :=
  keyedLookupAtom fixtureOwner essentialLabelLookupKey fixtureRequest
    fixtureLabel objectRootKey fixtureObjectFrontier

theorem startCanary_emits_exact_label_lookup :
    expectedLabelLookup ∈
      cFireReflectiveSourceExecFact startCanaryAtoms
        essentialStartDirective := by
  decide +kernel

private def fixtureControl : Atom :=
  essentialControlAtom fixtureOwner 2 3 fixtureStatement fixtureLabel
    fixtureTypecode fixtureBody fixtureFormulaAtom

private def fixtureComplete : Atom :=
  formulaValidationCompleteAtom fixtureOwner 2
    essentialFormulaValidationKey fixtureTypecode fixtureBody fixtureFormulaAtom

private def fixtureHypothesisFrontier : Atom := objectRootKey

private def commitCanaryAtoms : List Atom :=
  [essentialCommitRule, fixtureControl, fixtureComplete,
   objectFrontierAtom fixtureOwner fixtureObjectFrontier,
   sourceActivityFrontierAtom
     (activeHypothesisLedgerOwner fixtureOwner) fixtureHypothesisFrontier,
   essentialSourceReloadCaptureRow]

private def commitCanarySpace : Space := commitCanaryAtoms.toFinset

private theorem commitCanaryAtoms_nodup : commitCanaryAtoms.Nodup := by
  decide +kernel

private theorem commitCanaryAtoms_supported :
    cSupportedSourceExecFacts commitCanaryAtoms =
      [essentialCommitDirective] := by
  rfl

theorem commitCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace commitCanarySpace) =
      some essentialCommitDirective := by
  exact reflective_selects_of_computable_supported_singleton
    commitCanaryAtoms essentialCommitDirective commitCanaryAtoms_nodup
    commitCanaryAtoms_supported

theorem commitCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies commitCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact commitCanarySpace
          essentialCommitDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected commitCanary_selects_directive)

theorem commitCanary_publishes_exact_runtime_row :
    hypothesisLookupRow fixtureOwner (.essential "ex" fixtureFormula) ∈
      cFireReflectiveSourceExecFact commitCanaryAtoms
        essentialCommitDirective := by
  decide +kernel

theorem commitCanary_extends_active_scope_with_same_row :
    activeHypothesisLinkAtom fixtureOwner fixtureHypothesisFrontier
        (locatedNameAtom fixtureLabel)
        (.essential "ex" fixtureFormula) ∈
      cFireReflectiveSourceExecFact commitCanaryAtoms
        essentialCommitDirective := by
  decide +kernel

private def fixtureFault : Atom :=
  formulaValidationFaultAtom fixtureOwner 2 essentialFormulaValidationKey
    fixtureTypecode fixtureBody fixtureFormulaAtom "body-tag-mismatch"

private def faultCanaryAtoms : List Atom :=
  [essentialFormulaFaultRule, fixtureControl, fixtureFault]

theorem formulaFaultCanary_rejects_without_runtime_publication :
    (.expression
        [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 2,
          rawStatementAtom fixtureStatement,
          .symbol "invalid-essential-formula",
          .symbol "body-tag-mismatch"] ∈
        cFireReflectiveSourceExecFact faultCanaryAtoms
          essentialFormulaFaultDirective) ∧
      hypothesisLookupRow fixtureOwner (.essential "ex" fixtureFormula) ∉
        cFireReflectiveSourceExecFact faultCanaryAtoms
          essentialFormulaFaultDirective := by
  decide +kernel

section AxiomAudit

#print axioms essentialDeclaration_inhabits_source_native_type
#print axioms essentialCandidateAtom_proofNeutral
#print axioms essentialCandidateRow?_proofNeutral
#print axioms essentialCandidateRows_all_proofNeutral
#print axioms essentialCandidateRow?_fixturePlan
#print axioms essentialDeclarationRules_extract_exact
#print axioms essentialLookupStaticRows_not_proofNeutral
#print axioms essentialFormulaContinuationStaticRows_not_proofNeutral
#print axioms essentialSourceReloadCaptureRow_not_proofNeutral
#print axioms essentialFormulaStartCaptureRow_not_proofNeutral
#print axioms startCanary_selects_directive
#print axioms startCanary_inhabits_target_native_type
#print axioms startCanary_emits_exact_label_lookup
#print axioms commitCanary_selects_directive
#print axioms commitCanary_inhabits_target_native_type
#print axioms commitCanary_publishes_exact_runtime_row
#print axioms commitCanary_extends_active_scope_with_same_row
#print axioms formulaFaultCanary_rejects_without_runtime_publication

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
