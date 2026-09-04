import Mettapedia.Languages.Metamath.MM2SourceDVPairCommit
import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration

/-!
# Active-name validation for Metamath `$d` statements in ordinary MM2

Before any disjoint pair can be committed, every located name in the current
`$d` statement must be found in the active-variable ledger as a variable.  A
successful scan emits one verifier-owned marker per exact source occurrence
and a completion marker.  It changes no durable source ledger.

The pair validator consumes these markers and separately checks arity,
within-statement uniqueness, pair order, and pair count.  This separation lets
an inactive name stop the transaction before any pair capability is published.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVNameValidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Protected controls and observations -/

def dvNameValidationRequestAtom (owner : Atom)
    (statementPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-request", owner,
      natAtom statementPosition]

def dvNameValidatedAtom (owner : Atom) (statementPosition : Nat)
    (name : LocatedName) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validated", owner,
      natAtom statementPosition, locatedNameAtom name]

def dvNameValidationCompleteAtom (owner : Atom)
    (statementPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-complete", owner,
      natAtom statementPosition]

def dvNameValidationFaultAtom (owner : Atom) (statementPosition : Nat)
    (reason : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-fault", owner,
      natAtom statementPosition, .symbol reason]

@[simp] theorem dvNameValidationRequestAtom_not_proofNeutral
    (owner : Atom) (statementPosition : Nat) :
    isProofNeutralInitialAtom
      (dvNameValidationRequestAtom owner statementPosition) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-name-validation-request"
    [owner, natAtom statementPosition] (by decide)

@[simp] theorem dvNameValidatedAtom_not_proofNeutral
    (owner : Atom) (statementPosition : Nat) (name : LocatedName) :
    isProofNeutralInitialAtom
      (dvNameValidatedAtom owner statementPosition name) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-name-validated"
    [owner, natAtom statementPosition, locatedNameAtom name] (by decide)

/-! ## Exact active-ledger scan -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-dv-name-validation-start"
private def arityEmptyLocation :=
  location "02" "mm-source-dv-name-validation-arity-empty"
private def aritySingleLocation :=
  location "02" "mm-source-dv-name-validation-arity-single"
private def foundMoreLocation :=
  location "03" "mm-source-dv-name-validation-found-more"
private def foundLastLocation :=
  location "03" "mm-source-dv-name-validation-found-last"
private def missingLocation :=
  location "03" "mm-source-dv-name-validation-missing"
private def constantLocation :=
  location "03" "mm-source-dv-name-validation-constant"
private def labelLocation :=
  location "03" "mm-source-dv-name-validation-label"
private def reloadLocation :=
  location "36" "mm-source-dv-name-validation-reload"

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def candidateTemplate : Atom := locatedNameTemplate "candidate"
private def nextTemplate : Atom := locatedNameTemplate "next"

private def validNamesTemplate : Atom :=
  .expression
    [.symbol "mm-cons", candidateTemplate,
      .expression [.symbol "mm-cons", nextTemplate, .var "after-next"]]

private def emptyStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv", .var "declaration-site", nilTemplate,
      .var "declaration-terminator"]

private def singleStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv", .var "declaration-site",
      .expression [.symbol "mm-cons", candidateTemplate, nilTemplate],
      .var "declaration-terminator"]

private def validStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv", .var "declaration-site", validNamesTemplate,
      .var "declaration-terminator"]

private def currentTemplate (statement : Atom) : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source",
      .var "statement-position", .var "next-statement-position", statement,
      .var "dispatch-input", .var "dispatch-output"]

private def requestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-request",
      .var "source", .var "statement-position"]

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", .var "source"]

private def activeFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", activeOwnerTemplate,
      .var "active-frontier"]

private def controlTemplate (candidate remaining : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation", .var "source",
      .var "statement-position", candidate, remaining,
      .var "active-frontier"]

private def initialControlTemplate : Atom :=
  controlTemplate candidateTemplate
    (.expression
      [.symbol "mm-cons", nextTemplate, .var "after-next"])

private def moreControlTemplate : Atom :=
  controlTemplate candidateTemplate
    (.expression
      [.symbol "mm-cons", nextTemplate, .var "remaining-after-next"])

private def lastControlTemplate : Atom :=
  controlTemplate candidateTemplate nilTemplate

private def nextControlTemplate : Atom :=
  controlTemplate nextTemplate (.var "remaining-after-next")

private def anyControlTemplate : Atom :=
  controlTemplate candidateTemplate (.var "remaining-names")

private def lookupTemplate (control candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", activeOwnerTemplate, control,
      candidate, objectRootKey, .var "active-frontier"]

private def foundTemplate (control candidate kind : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-found", activeOwnerTemplate, control,
      candidate,
      .expression
        [.symbol "mm-source-object-entry", kind,
          .expression
            [.symbol "mm-source-name", .var "active-span",
              .var "candidate-name"]]]

private def missingTemplate (control candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", activeOwnerTemplate, control,
      candidate]

private def validatedTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validated", .var "source",
      .var "statement-position", candidateTemplate]

private def completeTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-complete",
      .var "source", .var "statement-position"]

private def faultTemplate (reason : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-fault",
      .var "source", .var "statement-position", .symbol reason]

private def objectReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", activeOwnerTemplate]

private def reloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-dv-name-validation", .var "source"]

def dvNameValidationReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-name-validation", owner]

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

private def mkCompatDirective (atom loc : Atom) (priority : Nat)
    (name : String) (patterns : List Atom) (sinks : List Sink) :
    SourceExecFact :=
  { atom
    loc
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def startSelf : Atom :=
  selfTemplate startLocation "dv-name-validation-start"
private def startPatterns : List Atom :=
  [startSelf, requestTemplate, currentTemplate validStatementTemplate,
    activeFrontierTemplate]
private def startSinks : List Sink :=
  [.add startSelf, .remove requestTemplate,
    .add (lookupTemplate initialControlTemplate candidateTemplate),
    .add objectReloadTemplate, .add reloadTriggerTemplate]

def validationStartRule : Atom := mkRule startLocation startPatterns startSinks
def validationStartDirective : SourceExecFact :=
  mkCompatDirective validationStartRule startLocation 2
    "mm-source-dv-name-validation-start" startPatterns startSinks

private def arityRuleFor (loc : Atom) (stem : String) (statement : Atom)
    (reason : String) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let patterns := [self, requestTemplate, currentTemplate statement]
  let sinks : List Sink :=
    [.add self, .remove requestTemplate, .add (faultTemplate reason)]
  let atom := mkRule loc patterns sinks
  (atom, mkCompatDirective atom loc 2 stem patterns sinks)

def validationArityEmptyRule : Atom :=
  (arityRuleFor arityEmptyLocation
    "mm-source-dv-name-validation-arity-empty" emptyStatementTemplate
    "arity").1
def validationArityEmptyDirective : SourceExecFact :=
  (arityRuleFor arityEmptyLocation
    "mm-source-dv-name-validation-arity-empty" emptyStatementTemplate
    "arity").2

def validationAritySingleRule : Atom :=
  (arityRuleFor aritySingleLocation
    "mm-source-dv-name-validation-arity-single" singleStatementTemplate
    "arity").1
def validationAritySingleDirective : SourceExecFact :=
  (arityRuleFor aritySingleLocation
    "mm-source-dv-name-validation-arity-single" singleStatementTemplate
    "arity").2

private def foundRuleFor (loc : Atom) (stem : String) (control : Atom)
    (more : Bool) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let found := foundTemplate control candidateTemplate
    (.symbol "mm-source-object-variable")
  let patterns := [self, found]
  let sinks : List Sink :=
    if more then
      [.add self, .remove found, .add validatedTemplate,
        .add (lookupTemplate nextControlTemplate nextTemplate),
        .add objectReloadTemplate, .add reloadTriggerTemplate]
    else
      [.add self, .remove found, .add validatedTemplate,
        .add completeTemplate]
  let atom := mkRule loc patterns sinks
  (atom, mkCompatDirective atom loc 3 stem patterns sinks)

def validationFoundMoreRule : Atom :=
  (foundRuleFor foundMoreLocation
    "mm-source-dv-name-validation-found-more" moreControlTemplate true).1
def validationFoundMoreDirective : SourceExecFact :=
  (foundRuleFor foundMoreLocation
    "mm-source-dv-name-validation-found-more" moreControlTemplate true).2

def validationFoundLastRule : Atom :=
  (foundRuleFor foundLastLocation
    "mm-source-dv-name-validation-found-last" lastControlTemplate false).1
def validationFoundLastDirective : SourceExecFact :=
  (foundRuleFor foundLastLocation
    "mm-source-dv-name-validation-found-last" lastControlTemplate false).2

private def failureRuleFor (loc : Atom) (stem reason : String)
    (observation : Atom) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let patterns := [self, observation]
  let sinks : List Sink :=
    [.add self, .remove observation, .add (faultTemplate reason)]
  let atom := mkRule loc patterns sinks
  (atom, mkCompatDirective atom loc 3 stem patterns sinks)

def validationMissingRule : Atom :=
  (failureRuleFor missingLocation "mm-source-dv-name-validation-missing"
    "inactive-variable"
    (missingTemplate anyControlTemplate candidateTemplate)).1
def validationMissingDirective : SourceExecFact :=
  (failureRuleFor missingLocation "mm-source-dv-name-validation-missing"
    "inactive-variable"
    (missingTemplate anyControlTemplate candidateTemplate)).2

private def wrongKindRuleFor (loc : Atom) (stem : String)
    (kind : ObjectKind) : Atom × SourceExecFact :=
  failureRuleFor loc stem "wrong-active-kind"
    (foundTemplate anyControlTemplate candidateTemplate (objectKindAtom kind))

def validationConstantRule : Atom :=
  (wrongKindRuleFor constantLocation
    "mm-source-dv-name-validation-constant" .constant).1
def validationConstantDirective : SourceExecFact :=
  (wrongKindRuleFor constantLocation
    "mm-source-dv-name-validation-constant" .constant).2

def validationLabelRule : Atom :=
  (wrongKindRuleFor labelLocation
    "mm-source-dv-name-validation-label" .label).1
def validationLabelDirective : SourceExecFact :=
  (wrongKindRuleFor labelLocation
    "mm-source-dv-name-validation-label" .label).2

theorem extract_validationStartRule_exact :
    extractSupportedSourceExecFact validationStartRule =
      some validationStartDirective := by rfl
theorem extract_validationArityEmptyRule_exact :
    extractSupportedSourceExecFact validationArityEmptyRule =
      some validationArityEmptyDirective := by rfl
theorem extract_validationAritySingleRule_exact :
    extractSupportedSourceExecFact validationAritySingleRule =
      some validationAritySingleDirective := by rfl
theorem extract_validationFoundMoreRule_exact :
    extractSupportedSourceExecFact validationFoundMoreRule =
      some validationFoundMoreDirective := by rfl
theorem extract_validationFoundLastRule_exact :
    extractSupportedSourceExecFact validationFoundLastRule =
      some validationFoundLastDirective := by rfl
theorem extract_validationMissingRule_exact :
    extractSupportedSourceExecFact validationMissingRule =
      some validationMissingDirective := by rfl
theorem extract_validationConstantRule_exact :
    extractSupportedSourceExecFact validationConstantRule =
      some validationConstantDirective := by rfl
theorem extract_validationLabelRule_exact :
    extractSupportedSourceExecFact validationLabelRule =
      some validationLabelDirective := by rfl

def validationStepRules : List Atom :=
  [validationFoundMoreRule, validationFoundLastRule,
    validationMissingRule, validationConstantRule, validationLabelRule]

def validationStepDirectives : List SourceExecFact :=
  [validationFoundMoreDirective, validationFoundLastDirective,
    validationMissingDirective, validationConstantDirective,
    validationLabelDirective]

def validationRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-name-validation-rule", rule]

@[simp] theorem validationRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (validationRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-name-validation-rule" [rule] (by decide)

def validationStaticRows : List Atom :=
  validationStepRules.map validationRuleRow

private def reloadSelf : Atom :=
  selfTemplate reloadLocation "dv-name-validation-reload"
private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-rule",
      .var "dv-name-validation-rule"]
private def reloadPatterns : List Atom :=
  [reloadSelf, reloadTriggerTemplate, reloadRuleTemplate]
private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove reloadTriggerTemplate,
    .add (.var "dv-name-validation-rule")]

def validationReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks
def validationReloadDirective : SourceExecFact :=
  mkCompatDirective validationReloadRule reloadLocation 36
    "mm-source-dv-name-validation-reload" reloadPatterns reloadSinks

theorem extract_validationReloadRule_exact :
    extractSupportedSourceExecFact validationReloadRule =
      some validationReloadDirective := by rfl

def validationRules : List Atom :=
  [validationStartRule, validationArityEmptyRule,
    validationAritySingleRule] ++ validationStepRules ++
      [validationReloadRule]

def validationDirectives : List SourceExecFact :=
  [validationStartDirective, validationArityEmptyDirective,
    validationAritySingleDirective] ++ validationStepDirectives ++
      [validationReloadDirective]

theorem validationRules_extract_exact :
    validationRules.filterMap extractSupportedSourceExecFact =
      validationDirectives := by
  rfl

/-! ## Complete active-name trace and negative controls -/

private def fixtureOwner : Atom := .symbol "dv-name-validation-source"
private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "dv-name-validation.mm", start, stop }
private def fixtureName (name : String) (start : Nat) : LocatedName :=
  { span := fixtureSpan start (start + 1), name }
private def xName : LocatedName := fixtureName "x" 3
private def yName : LocatedName := fixtureName "y" 5
private def zName : LocatedName := fixtureName "z" 7
private def fixtureStatement : RawStatement :=
  .djDecl (fixtureSpan 0 2) [xName, yName, zName] (fixtureSpan 9 11)
private def fixtureRequest : Atom :=
  dvNameValidationRequestAtom fixtureOwner 0

def dvNameValidationControlAtom (owner : Atom) (statementPosition : Nat)
    (candidate : LocatedName) (remaining : List LocatedName)
    (activeFrontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation", owner,
      natAtom statementPosition, locatedNameAtom candidate,
      listAtom locatedNameAtom remaining, activeFrontier]

private def fixtureActiveEntries : List ObjectOccurrence :=
  [activeOccurrenceEntry xName, activeOccurrenceEntry yName,
    activeOccurrenceEntry zName]

private def fixtureActiveFrontier : Atom :=
  objectFrontierKey fixtureActiveEntries

private def xControl : Atom :=
  dvNameValidationControlAtom fixtureOwner 0 xName [yName, zName]
    fixtureActiveFrontier

private def yControl : Atom :=
  dvNameValidationControlAtom fixtureOwner 0 yName [zName]
    fixtureActiveFrontier

private def zControl : Atom :=
  dvNameValidationControlAtom fixtureOwner 0 zName [] fixtureActiveFrontier

private def startCanaryAtoms : List Atom :=
  [validationStartRule, fixtureRequest,
    sourceCurrentAtom fixtureOwner 0 1 fixtureStatement,
    objectFrontierAtom (activeVariableLedgerOwner fixtureOwner)
      fixtureActiveFrontier]

private def startCanarySpace : Space := startCanaryAtoms.toFinset

private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel

private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms =
      [validationStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some validationStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms validationStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          validationStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

private theorem startCanary_fire_agreement :
    (cFireReflectiveSourceExecFact startCanaryAtoms
        validationStartDirective).toFinset =
      fireReflectiveSourceExecFact startCanarySpace
        validationStartDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    startCanaryAtoms validationStartDirective startCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationStartDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      startCanaryAtoms validationStartDirective startCanaryAtoms_nodup)

theorem startCanary_emits_exact_first_lookup :
    lookupAtom (activeVariableLedgerOwner fixtureOwner) xControl xName
        objectRootKey fixtureActiveFrontier ∈
      fireReflectiveSourceExecFact startCanarySpace
        validationStartDirective := by
  rw [← startCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def foundMoreCanaryAtoms : List Atom :=
  [validationFoundMoreRule,
    lookupFoundAtom (activeVariableLedgerOwner fixtureOwner) xControl xName
      (activeOccurrenceEntry xName)]

private def foundMoreCanarySpace : Space := foundMoreCanaryAtoms.toFinset

private theorem foundMoreCanaryAtoms_nodup :
    foundMoreCanaryAtoms.Nodup := by decide +kernel

private theorem foundMoreCanaryAtoms_supported :
    cSupportedSourceExecFacts foundMoreCanaryAtoms =
      [validationFoundMoreDirective] := by rfl

theorem foundMoreCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace foundMoreCanarySpace) =
      some validationFoundMoreDirective := by
  exact reflective_selects_of_computable_supported_singleton
    foundMoreCanaryAtoms validationFoundMoreDirective
    foundMoreCanaryAtoms_nodup foundMoreCanaryAtoms_supported

private theorem foundMoreCanary_fire_agreement :
    (cFireReflectiveSourceExecFact foundMoreCanaryAtoms
        validationFoundMoreDirective).toFinset =
      fireReflectiveSourceExecFact foundMoreCanarySpace
        validationFoundMoreDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    foundMoreCanaryAtoms validationFoundMoreDirective
    foundMoreCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationFoundMoreDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      foundMoreCanaryAtoms validationFoundMoreDirective
      foundMoreCanaryAtoms_nodup)

theorem foundMoreCanary_marks_current_and_requests_next :
    dvNameValidatedAtom fixtureOwner 0 xName ∈
        fireReflectiveSourceExecFact foundMoreCanarySpace
          validationFoundMoreDirective ∧
      lookupAtom (activeVariableLedgerOwner fixtureOwner) yControl yName
          objectRootKey fixtureActiveFrontier ∈
        fireReflectiveSourceExecFact foundMoreCanarySpace
          validationFoundMoreDirective := by
  rw [← foundMoreCanary_fire_agreement]
  decide +kernel

private def foundLastCanaryAtoms : List Atom :=
  [validationFoundLastRule,
    lookupFoundAtom (activeVariableLedgerOwner fixtureOwner) zControl zName
      (activeOccurrenceEntry zName)]

private def foundLastCanarySpace : Space := foundLastCanaryAtoms.toFinset

private theorem foundLastCanaryAtoms_nodup :
    foundLastCanaryAtoms.Nodup := by decide +kernel

private theorem foundLastCanaryAtoms_supported :
    cSupportedSourceExecFacts foundLastCanaryAtoms =
      [validationFoundLastDirective] := by rfl

private theorem foundLastCanary_fire_agreement :
    (cFireReflectiveSourceExecFact foundLastCanaryAtoms
        validationFoundLastDirective).toFinset =
      fireReflectiveSourceExecFact foundLastCanarySpace
        validationFoundLastDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    foundLastCanaryAtoms validationFoundLastDirective
    foundLastCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationFoundLastDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      foundLastCanaryAtoms validationFoundLastDirective
      foundLastCanaryAtoms_nodup)

theorem foundLastCanary_marks_current_and_completes :
    dvNameValidatedAtom fixtureOwner 0 zName ∈
        fireReflectiveSourceExecFact foundLastCanarySpace
          validationFoundLastDirective ∧
      dvNameValidationCompleteAtom fixtureOwner 0 ∈
        fireReflectiveSourceExecFact foundLastCanarySpace
          validationFoundLastDirective := by
  rw [← foundLastCanary_fire_agreement]
  decide +kernel

private def inactiveCanaryAtoms : List Atom :=
  [validationMissingRule,
    lookupMissingAtom (activeVariableLedgerOwner fixtureOwner) zControl zName]

private def inactiveCanarySpace : Space := inactiveCanaryAtoms.toFinset

private theorem inactiveCanaryAtoms_nodup :
    inactiveCanaryAtoms.Nodup := by decide +kernel

private theorem inactiveCanaryAtoms_supported :
    cSupportedSourceExecFacts inactiveCanaryAtoms =
      [validationMissingDirective] := by rfl

private theorem inactiveCanary_fire_agreement :
    (cFireReflectiveSourceExecFact inactiveCanaryAtoms
        validationMissingDirective).toFinset =
      fireReflectiveSourceExecFact inactiveCanarySpace
        validationMissingDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    inactiveCanaryAtoms validationMissingDirective inactiveCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationMissingDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      inactiveCanaryAtoms validationMissingDirective inactiveCanaryAtoms_nodup)

theorem inactiveCanary_emits_fault_not_completion :
    dvNameValidationFaultAtom fixtureOwner 0 "inactive-variable" ∈
        fireReflectiveSourceExecFact inactiveCanarySpace
          validationMissingDirective ∧
      dvNameValidationCompleteAtom fixtureOwner 0 ∉
        fireReflectiveSourceExecFact inactiveCanarySpace
          validationMissingDirective := by
  rw [← inactiveCanary_fire_agreement]
  decide +kernel

private def wrongKindCanaryAtoms : List Atom :=
  [validationConstantRule,
    lookupFoundAtom (activeVariableLedgerOwner fixtureOwner) zControl zName
      { kind := .constant, occurrence := zName }]

private def wrongKindCanarySpace : Space := wrongKindCanaryAtoms.toFinset

private theorem wrongKindCanaryAtoms_nodup :
    wrongKindCanaryAtoms.Nodup := by decide +kernel

private theorem wrongKindCanaryAtoms_supported :
    cSupportedSourceExecFacts wrongKindCanaryAtoms =
      [validationConstantDirective] := by rfl

private theorem wrongKindCanary_fire_agreement :
    (cFireReflectiveSourceExecFact wrongKindCanaryAtoms
        validationConstantDirective).toFinset =
      fireReflectiveSourceExecFact wrongKindCanarySpace
        validationConstantDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    wrongKindCanaryAtoms validationConstantDirective
    wrongKindCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationConstantDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      wrongKindCanaryAtoms validationConstantDirective
      wrongKindCanaryAtoms_nodup)

theorem wrongKindCanary_emits_fault_not_completion :
    dvNameValidationFaultAtom fixtureOwner 0 "wrong-active-kind" ∈
        fireReflectiveSourceExecFact wrongKindCanarySpace
          validationConstantDirective ∧
      dvNameValidationCompleteAtom fixtureOwner 0 ∉
        fireReflectiveSourceExecFact wrongKindCanarySpace
          validationConstantDirective := by
  rw [← wrongKindCanary_fire_agreement]
  decide +kernel

private def singletonStatement : RawStatement :=
  .djDecl (fixtureSpan 0 2) [xName] (fixtureSpan 5 7)

private def singletonCanaryAtoms : List Atom :=
  [validationAritySingleRule, fixtureRequest,
    sourceCurrentAtom fixtureOwner 0 1 singletonStatement]

private def singletonCanarySpace : Space := singletonCanaryAtoms.toFinset

private theorem singletonCanaryAtoms_nodup :
    singletonCanaryAtoms.Nodup := by decide +kernel

private theorem singletonCanaryAtoms_supported :
    cSupportedSourceExecFacts singletonCanaryAtoms =
      [validationAritySingleDirective] := by rfl

private theorem singletonCanary_fire_agreement :
    (cFireReflectiveSourceExecFact singletonCanaryAtoms
        validationAritySingleDirective).toFinset =
      fireReflectiveSourceExecFact singletonCanarySpace
        validationAritySingleDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    singletonCanaryAtoms validationAritySingleDirective
    singletonCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationAritySingleDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      singletonCanaryAtoms validationAritySingleDirective
      singletonCanaryAtoms_nodup)

theorem singletonCanary_emits_arity_fault :
    dvNameValidationFaultAtom fixtureOwner 0 "arity" ∈
      fireReflectiveSourceExecFact singletonCanarySpace
        validationAritySingleDirective := by
  rw [← singletonCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

section AxiomAudit

#print axioms dvNameValidationRequestAtom_not_proofNeutral
#print axioms dvNameValidatedAtom_not_proofNeutral
#print axioms extract_validationStartRule_exact
#print axioms extract_validationArityEmptyRule_exact
#print axioms extract_validationAritySingleRule_exact
#print axioms extract_validationFoundMoreRule_exact
#print axioms extract_validationFoundLastRule_exact
#print axioms extract_validationMissingRule_exact
#print axioms extract_validationConstantRule_exact
#print axioms extract_validationLabelRule_exact
#print axioms extract_validationReloadRule_exact
#print axioms validationRules_extract_exact
#print axioms validationRuleRow_not_proofNeutral
#print axioms startCanary_selects_directive
#print axioms startCanary_inhabits_target_native_type
#print axioms startCanary_emits_exact_first_lookup
#print axioms foundMoreCanary_selects_directive
#print axioms foundMoreCanary_marks_current_and_requests_next
#print axioms foundLastCanary_marks_current_and_completes
#print axioms inactiveCanary_emits_fault_not_completion
#print axioms wrongKindCanary_emits_fault_not_completion
#print axioms singletonCanary_emits_arity_fault

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVNameValidation
