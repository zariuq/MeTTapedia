import Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution
import Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchWitness

/-!
# Source-derived floating declarations in ordinary MM2

A Metamath `$f` declaration is accepted only after four source-owned lookups:

1. its label is absent from the global object history;
2. its typecode is a declared constant;
3. its variable is active in the current scope; and
4. its historical typecode is absent or has the same name.

The successful continuation changes all durable ledgers in one MM2
transition.  A first typecode assignment extends the historical ledger; a
compatible repeated assignment reuses it.  Neither rejection path changes a
durable frontier or advances the source cursor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
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

/-! ## Source GSLT, OSLF, and exact native type -/

/-- An accepted source `$f` step is interpreted by the authored source-state
GSLT, passed through OSLF, and classified by the exact target native type. -/
theorem floatingDeclaration_inhabits_source_native_type
    {before after : SourceState} {label typecode variableName : String}
    (declared :
      declareFloating? before label typecode variableName = some after) :
    (gsltOSLF SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact declareFloating_inhabits_source_native_type declared

/-! ## Exact source-owned rows -/

def floatingRequestAtom (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (label typecode variableName : LocatedName) :
    Atom :=
  .expression
    [.symbol "mm-source-floating-request", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement, locatedNameAtom label,
      stringAtom label.name, locatedNameAtom typecode, stringAtom typecode.name,
      locatedNameAtom variableName, stringAtom variableName.name]

def floatingLabelOccurrence (label : LocatedName) : ObjectOccurrence :=
  { kind := .label, occurrence := label }

def floatingRuntimeRow (owner : Atom) (label typecode variableName : String) :
    Atom :=
  hypothesisLookupRow owner (.floating label typecode variableName)

/-! ## Ordinary MM2 protocol -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-floating-start"
private def labelOccupiedLocation :=
  location "03" "mm-source-floating-label-occupied"
private def labelMissingLocation :=
  location "03" "mm-source-floating-label-missing"
private def typecodeConstantLocation :=
  location "04" "mm-source-floating-typecode-constant"
private def typecodeWrongLocation :=
  location "05" "mm-source-floating-typecode-wrong-kind"
private def typecodeMissingLocation :=
  location "05" "mm-source-floating-typecode-missing"
private def variableActiveLocation :=
  location "06" "mm-source-floating-variable-active"
private def variableWrongLocation :=
  location "07" "mm-source-floating-variable-wrong-kind"
private def variableMissingLocation :=
  location "07" "mm-source-floating-variable-inactive"
private def historyReuseLocation :=
  location "08" "mm-source-floating-history-reuse"
private def historyConflictLocation :=
  location "09" "mm-source-floating-history-conflict"
private def historyFreshLocation :=
  location "08" "mm-source-floating-history-fresh"

private def labelTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "label-span", .var "label-name"]

private def typecodeTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "typecode-span", .var "typecode-name"]

private def variableTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "variable-span", .var "variable-name"]

private def statementTemplate : Atom :=
  .expression
    [.symbol "mm-source-floating", .var "declaration-site", labelTemplate,
      typecodeTemplate, variableTemplate, .var "declaration-terminator"]

private def currentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", statementTemplate, .var "dispatch-input",
      .var "dispatch-output"]

private def requestEmissionTemplate : Atom :=
  .expression
    [.symbol "mm-source-floating-request", .var "source", .var "position",
      .var "next-position", statementTemplate, labelTemplate,
      .var "label-name", typecodeTemplate, .var "typecode-name",
      variableTemplate, .var "variable-name"]

private def requestTemplate : Atom :=
  .expression
    [.symbol "mm-source-floating-request", .var "source", .var "position",
      .var "next-position", .var "statement", .var "label",
      .var "label-name", .var "typecode", .var "typecode-name",
      .var "variable", .var "variable-name"]

private def objectFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source",
      .var "object-frontier"]

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", .var "source"]

private def activeFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", activeOwnerTemplate,
      .var "active-frontier"]

private def historyOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-variable-typecode-ledger", .var "source"]

private def historyFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", historyOwnerTemplate,
      .var "history-frontier"]

private def hypothesisOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]

private def hypothesisFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate,
      .var "hypothesis-frontier"]

private def lookupTemplate (request owner candidate cursor frontier : Atom) :
    Atom :=
  .expression
    [.symbol "mm-source-object-lookup", owner, request, candidate,
      cursor, frontier]

private def globalLabelLookupEmissionTemplate : Atom :=
  lookupTemplate requestEmissionTemplate (.var "source") labelTemplate
    objectRootKey (.var "object-frontier")

private def globalTypecodeLookupTemplate : Atom :=
  lookupTemplate requestTemplate (.var "source") (.var "typecode") objectRootKey
    (.var "object-frontier")

private def activeVariableLookupTemplate : Atom :=
  lookupTemplate requestTemplate activeOwnerTemplate (.var "variable") objectRootKey
    (.var "active-frontier")

private def historyLookupTemplate : Atom :=
  lookupTemplate requestTemplate historyOwnerTemplate (.var "variable") objectRootKey
    (.var "history-frontier")

private def reloadTriggerTemplate (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", owner]

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

private def foundTemplate (owner candidate occupied : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-found", owner, requestTemplate, candidate,
      occupied]

private def missingTemplate (owner candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", owner, requestTemplate, candidate]

private def occupiedTemplate (kind name : Atom) : Atom :=
  .expression [.symbol "mm-source-object-entry", kind, name]

private def rejectedTemplate (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source", .var "position",
      .var "statement", reason, evidence]

private def startSelf := selfTemplate startLocation "floating-start"
private def startPatterns : List Atom :=
  [startSelf, currentTemplate, objectFrontierTemplate, activeFrontierTemplate,
   historyFrontierTemplate, hypothesisFrontierTemplate]
private def startSinks : List Sink :=
  [.add startSelf, .remove currentTemplate,
   .add globalLabelLookupEmissionTemplate,
   .add (reloadTriggerTemplate (.var "source"))]

def floatingStartRule : Atom :=
  mkRule startLocation startPatterns startSinks
def floatingStartDirective : SourceExecFact :=
  mkDirective floatingStartRule startLocation 2 "mm-source-floating-start"
    startPatterns startSinks

private def labelFoundTemplate : Atom :=
  foundTemplate (.var "source") (.var "label") (.var "occupied-object")
private def labelOccupiedSelf :=
  selfTemplate labelOccupiedLocation "floating-label-occupied"
private def labelOccupiedPatterns : List Atom :=
  [labelOccupiedSelf, labelFoundTemplate]
private def labelOccupiedSinks : List Sink :=
  [.add labelOccupiedSelf, .remove labelFoundTemplate,
   .add (rejectedTemplate (.symbol "occupied-floating-label")
      (.var "occupied-object"))]

def floatingLabelOccupiedRule : Atom :=
  mkRule labelOccupiedLocation labelOccupiedPatterns labelOccupiedSinks
def floatingLabelOccupiedDirective : SourceExecFact :=
  mkDirective floatingLabelOccupiedRule labelOccupiedLocation 3
    "mm-source-floating-label-occupied" labelOccupiedPatterns
    labelOccupiedSinks

private def labelMissingTemplate : Atom :=
  missingTemplate (.var "source") (.var "label")
private def labelMissingSelf :=
  selfTemplate labelMissingLocation "floating-label-missing"
private def labelMissingPatterns : List Atom :=
  [labelMissingSelf, labelMissingTemplate, objectFrontierTemplate]
private def labelMissingSinks : List Sink :=
  [.add labelMissingSelf, .remove labelMissingTemplate,
   .add globalTypecodeLookupTemplate,
   .add (reloadTriggerTemplate (.var "source"))]

def floatingLabelMissingRule : Atom :=
  mkRule labelMissingLocation labelMissingPatterns labelMissingSinks
def floatingLabelMissingDirective : SourceExecFact :=
  mkDirective floatingLabelMissingRule labelMissingLocation 3
    "mm-source-floating-label-missing" labelMissingPatterns labelMissingSinks

private def typecodeConstantEntry : Atom :=
  occupiedTemplate (.symbol "mm-source-object-constant")
    (.expression
      [.symbol "mm-source-name", .var "declared-typecode-span",
        .var "typecode-name"])
private def typecodeFoundConstantTemplate : Atom :=
  foundTemplate (.var "source") (.var "typecode") typecodeConstantEntry
private def typecodeFoundAnyTemplate : Atom :=
  foundTemplate (.var "source") (.var "typecode") (.var "occupied-object")
private def typecodeConstantSelf :=
  selfTemplate typecodeConstantLocation "floating-typecode-constant"
private def typecodeConstantPatterns : List Atom :=
  [typecodeConstantSelf, typecodeFoundConstantTemplate, activeFrontierTemplate]
private def typecodeConstantSinks : List Sink :=
  [.add typecodeConstantSelf, .remove typecodeFoundConstantTemplate,
   .add activeVariableLookupTemplate,
   .add (reloadTriggerTemplate activeOwnerTemplate)]

def floatingTypecodeConstantRule : Atom :=
  mkRule typecodeConstantLocation typecodeConstantPatterns
    typecodeConstantSinks
def floatingTypecodeConstantDirective : SourceExecFact :=
  mkDirective floatingTypecodeConstantRule typecodeConstantLocation 4
    "mm-source-floating-typecode-constant" typecodeConstantPatterns
    typecodeConstantSinks

private def typecodeWrongSelf :=
  selfTemplate typecodeWrongLocation "floating-typecode-wrong-kind"
private def typecodeWrongPatterns : List Atom :=
  [typecodeWrongSelf, typecodeFoundAnyTemplate]
private def typecodeWrongSinks : List Sink :=
  [.add typecodeWrongSelf, .remove typecodeFoundAnyTemplate,
   .add (rejectedTemplate (.symbol "floating-typecode-not-constant")
      (.var "occupied-object"))]

def floatingTypecodeWrongRule : Atom :=
  mkRule typecodeWrongLocation typecodeWrongPatterns typecodeWrongSinks
def floatingTypecodeWrongDirective : SourceExecFact :=
  mkDirective floatingTypecodeWrongRule typecodeWrongLocation 5
    "mm-source-floating-typecode-wrong-kind" typecodeWrongPatterns
    typecodeWrongSinks

private def typecodeMissingTemplate : Atom :=
  missingTemplate (.var "source") (.var "typecode")
private def typecodeMissingSelf :=
  selfTemplate typecodeMissingLocation "floating-typecode-missing"
private def typecodeMissingPatterns : List Atom :=
  [typecodeMissingSelf, typecodeMissingTemplate]
private def typecodeMissingSinks : List Sink :=
  [.add typecodeMissingSelf, .remove typecodeMissingTemplate,
   .add (rejectedTemplate (.symbol "undeclared-floating-typecode")
      (.var "typecode"))]

def floatingTypecodeMissingRule : Atom :=
  mkRule typecodeMissingLocation typecodeMissingPatterns typecodeMissingSinks
def floatingTypecodeMissingDirective : SourceExecFact :=
  mkDirective floatingTypecodeMissingRule typecodeMissingLocation 5
    "mm-source-floating-typecode-missing" typecodeMissingPatterns
    typecodeMissingSinks

private def activeVariableEntry : Atom :=
  occupiedTemplate (.symbol "mm-source-object-variable")
    (.expression
      [.symbol "mm-source-name", .var "declared-variable-span",
        .var "variable-name"])
private def activeFoundVariableTemplate : Atom :=
  foundTemplate activeOwnerTemplate (.var "variable") activeVariableEntry
private def activeFoundAnyTemplate : Atom :=
  foundTemplate activeOwnerTemplate (.var "variable") (.var "occupied-object")
private def variableActiveSelf :=
  selfTemplate variableActiveLocation "floating-variable-active"
private def variableActivePatterns : List Atom :=
  [variableActiveSelf, activeFoundVariableTemplate, historyFrontierTemplate]
private def variableActiveSinks : List Sink :=
  [.add variableActiveSelf, .remove activeFoundVariableTemplate,
   .add historyLookupTemplate,
   .add (reloadTriggerTemplate historyOwnerTemplate)]

def floatingVariableActiveRule : Atom :=
  mkRule variableActiveLocation variableActivePatterns variableActiveSinks
def floatingVariableActiveDirective : SourceExecFact :=
  mkDirective floatingVariableActiveRule variableActiveLocation 6
    "mm-source-floating-variable-active" variableActivePatterns
    variableActiveSinks

private def variableWrongSelf :=
  selfTemplate variableWrongLocation "floating-variable-wrong-kind"
private def variableWrongPatterns : List Atom :=
  [variableWrongSelf, activeFoundAnyTemplate]
private def variableWrongSinks : List Sink :=
  [.add variableWrongSelf, .remove activeFoundAnyTemplate,
   .add (rejectedTemplate (.symbol "active-floating-name-not-variable")
      (.var "occupied-object"))]

def floatingVariableWrongRule : Atom :=
  mkRule variableWrongLocation variableWrongPatterns variableWrongSinks
def floatingVariableWrongDirective : SourceExecFact :=
  mkDirective floatingVariableWrongRule variableWrongLocation 7
    "mm-source-floating-variable-wrong-kind" variableWrongPatterns
    variableWrongSinks

private def variableMissingTemplate : Atom :=
  missingTemplate activeOwnerTemplate (.var "variable")
private def variableMissingSelf :=
  selfTemplate variableMissingLocation "floating-variable-inactive"
private def variableMissingPatterns : List Atom :=
  [variableMissingSelf, variableMissingTemplate]
private def variableMissingSinks : List Sink :=
  [.add variableMissingSelf, .remove variableMissingTemplate,
   .add (rejectedTemplate (.symbol "inactive-floating-variable")
      (.var "variable"))]

def floatingVariableMissingRule : Atom :=
  mkRule variableMissingLocation variableMissingPatterns variableMissingSinks
def floatingVariableMissingDirective : SourceExecFact :=
  mkDirective floatingVariableMissingRule variableMissingLocation 7
    "mm-source-floating-variable-inactive" variableMissingPatterns
    variableMissingSinks

private def historicalObjectTemplate : Atom :=
  occupiedTemplate (.symbol "mm-source-object-variable")
    (.var "historical-variable")

private def historicalPayloadTemplate (historicalTypecode : Atom) : Atom :=
  .expression
    [.symbol "mm-source-variable-typecode-payload",
      .var "historical-position", .var "historical-label",
      historicalTypecode]

private def historicalSameTypecodeTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "historical-typecode-span",
      .var "typecode-name"]

private def historicalFoundSameTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-found", .var "source",
      requestTemplate, .var "variable", historicalObjectTemplate,
      historicalPayloadTemplate historicalSameTypecodeTemplate]

private def historicalFoundAnyTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-found", .var "source",
      requestTemplate, .var "variable", .var "historical-object",
      .var "historical-payload"]

private def historicalMissingTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-missing", .var "source",
      requestTemplate, .var "variable"]

private def labelEntryTemplate : Atom :=
  occupiedTemplate (.symbol "mm-source-object-label") (.var "label")

private def appendedLabelLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "object-frontier",
      .var "label", labelEntryTemplate]

private def appendedLabelFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source", .var "label"]

private def historicalVariableEntryTemplate : Atom :=
  occupiedTemplate (.symbol "mm-source-object-variable") (.var "variable")

private def appendedHistoryLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", historyOwnerTemplate,
      .var "history-frontier", .var "variable",
      historicalVariableEntryTemplate]

private def appendedHistoryFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", historyOwnerTemplate,
      .var "variable"]

private def appendedHistoryBindingTemplate : Atom :=
  .expression
    [.symbol "mm-source-variable-typecode-binding", .var "source",
      historicalVariableEntryTemplate,
      .expression
        [.symbol "mm-source-variable-typecode-payload", .var "position",
          .var "label", .var "typecode"]]

private def formulaTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "typecode-name",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .expression [.symbol "mm-nil"]]]

private def runtimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "source", .var "label-name",
      formulaTemplate]

private def floatingHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-floating", .var "label-name", .var "typecode-name",
      .var "variable-name"]

private def appendedHypothesisLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", hypothesisOwnerTemplate,
      .var "hypothesis-frontier", .var "label",
      floatingHypothesisTemplate, runtimeRowTemplate]

private def appendedHypothesisFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", hypothesisOwnerTemplate,
      .var "label"]

private def nextSourceControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def statementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source", .var "position",
      .var "statement"]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-floating-reload",
      .var "source-verifier-reload-rule"]

def floatingSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-floating-reload", sourceVerifierReloadRule]

private def durableCommitPatterns (observation : Atom) : List Atom :=
  [observation, objectFrontierTemplate, hypothesisFrontierTemplate,
   sourceReloadCaptureTemplate]

private def durableCommitRemovals (observation : Atom) : List Sink :=
  [.remove observation, .remove objectFrontierTemplate,
   .remove hypothesisFrontierTemplate]

private def durableCommitAdds : List Sink :=
  [.add appendedLabelLinkTemplate, .add appendedLabelFrontierTemplate,
   .add runtimeRowTemplate,
   .add appendedHypothesisLinkTemplate,
   .add appendedHypothesisFrontierTemplate,
   .add nextSourceControlTemplate, .add statementAppliedTemplate,
   .add sourceReloadTemplate, .add (.var "source-verifier-reload-rule")]

private def durableCommitSinks (observation : Atom) : List Sink :=
  durableCommitRemovals observation ++ durableCommitAdds

private def historyReusePatterns : List Atom :=
  durableCommitPatterns historicalFoundSameTemplate
private def historyReuseSinks : List Sink :=
  durableCommitSinks historicalFoundSameTemplate

def floatingHistoryReuseRule : Atom :=
  mkRule historyReuseLocation historyReusePatterns historyReuseSinks
def floatingHistoryReuseDirective : SourceExecFact :=
  mkDirective floatingHistoryReuseRule historyReuseLocation 8
    "mm-source-floating-history-reuse" historyReusePatterns historyReuseSinks

private def historyConflictPatterns : List Atom :=
  [historicalFoundAnyTemplate]
private def historyConflictSinks : List Sink :=
  [.remove historicalFoundAnyTemplate,
   .add (rejectedTemplate (.symbol "incompatible-floating-typecode")
      (.expression
        [.symbol "mm-source-historical-typecode-evidence",
          .var "historical-object", .var "historical-payload"]))]

def floatingHistoryConflictRule : Atom :=
  mkRule historyConflictLocation historyConflictPatterns historyConflictSinks
def floatingHistoryConflictDirective : SourceExecFact :=
  mkDirective floatingHistoryConflictRule historyConflictLocation 9
    "mm-source-floating-history-conflict" historyConflictPatterns
    historyConflictSinks

private def historyFreshPatterns : List Atom :=
  durableCommitPatterns historicalMissingTemplate ++
    [historyFrontierTemplate]
private def historyFreshSinks : List Sink :=
  (durableCommitRemovals historicalMissingTemplate ++
    [.remove historyFrontierTemplate]) ++
    (durableCommitAdds ++
      [.add appendedHistoryLinkTemplate,
     .add appendedHistoryFrontierTemplate,
     .add appendedHistoryBindingTemplate])

def floatingHistoryFreshRule : Atom :=
  mkRule historyFreshLocation historyFreshPatterns historyFreshSinks
def floatingHistoryFreshDirective : SourceExecFact :=
  mkDirective floatingHistoryFreshRule historyFreshLocation 8
    "mm-source-floating-history-fresh" historyFreshPatterns historyFreshSinks

/-! ## Rule inventory and verifier-owned reload rows -/

def floatingDeclarationOwnRules : List Atom :=
  [floatingStartRule, floatingLabelOccupiedRule, floatingLabelMissingRule,
   floatingTypecodeConstantRule, floatingTypecodeWrongRule,
   floatingTypecodeMissingRule, floatingVariableActiveRule,
   floatingVariableWrongRule, floatingVariableMissingRule,
   floatingHistoryReuseRule, floatingHistoryConflictRule,
   floatingHistoryFreshRule]

def floatingDeclarationOwnDirectives : List SourceExecFact :=
  [floatingStartDirective, floatingLabelOccupiedDirective,
   floatingLabelMissingDirective, floatingTypecodeConstantDirective,
   floatingTypecodeWrongDirective, floatingTypecodeMissingDirective,
   floatingVariableActiveDirective, floatingVariableWrongDirective,
   floatingVariableMissingDirective, floatingHistoryReuseDirective,
   floatingHistoryConflictDirective, floatingHistoryFreshDirective]

def floatingDeclarationRules : List Atom :=
  floatingDeclarationOwnRules ++ lookupRules ++ variableTypecodeLookupRules

def floatingDeclarationDirectives : List SourceExecFact :=
  floatingDeclarationOwnDirectives ++ lookupDirectives ++
    variableTypecodeLookupDirectives

def floatingLookupContinuationRules : List Atom :=
  floatingDeclarationOwnRules.drop 1 ++ variableTypecodeLookupRules

def floatingLookupStaticRows : List Atom :=
  floatingLookupContinuationRules.map objectLookupRuleRow

def floatingDeclarationStaticRows : List Atom :=
  floatingLookupStaticRows ++ [floatingSourceReloadCaptureRow]

theorem floatingDeclarationRules_extract_exact :
    floatingDeclarationRules.filterMap extractSupportedSourceExecFact =
      floatingDeclarationDirectives := by
  rfl

theorem floatingLookupStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ floatingLookupStaticRows) :
    isProofNeutralInitialAtom row = false := by
  rw [floatingLookupStaticRows, List.mem_map] at member
  obtain ⟨rule, _, rfl⟩ := member
  exact objectLookupRuleRow_not_proofNeutral rule

@[simp] theorem floatingSourceReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom floatingSourceReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-floating-reload" [sourceVerifierReloadRule]
      (by decide)

/-! ## Bounded positive and negative controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "floating.mm", start, stop }

private def fixtureSite : LocatedByteSpan := fixtureSpan 0 2
private def fixtureLabel : LocatedName :=
  { span := fixtureSpan 3 5, name := "wx" }
private def fixtureTypecode : LocatedName :=
  { span := fixtureSpan 6 9, name := "wff" }
private def fixtureVariable : LocatedName :=
  { span := fixtureSpan 10 11, name := "x" }
private def fixtureTerminator : LocatedByteSpan := fixtureSpan 12 14
private def fixtureStatement : RawStatement :=
  .floating fixtureSite fixtureLabel fixtureTypecode fixtureVariable
    fixtureTerminator
private def fixtureOwner : Atom := .symbol "floating-source"
private def fixtureDispatchInput : Atom := .symbol "dispatch-input"
private def fixtureDispatchOutput : Atom := .symbol "dispatch-output"
private def fixtureRequest : Atom :=
  floatingRequestAtom fixtureOwner 2 3 fixtureStatement fixtureLabel
    fixtureTypecode fixtureVariable
private def fixtureLabelEntry : ObjectOccurrence :=
  floatingLabelOccurrence fixtureLabel
private def fixtureHistoryOccurrence : VariableTypecodeOccurrence :=
  { statementPosition := 2
    label := fixtureLabel
    typecode := fixtureTypecode
    variableName := fixtureVariable }
private def fixtureRuntimeRow : Atom :=
  floatingRuntimeRow fixtureOwner fixtureLabel.name fixtureTypecode.name
    fixtureVariable.name
private def fixtureHypothesis : HypothesisView :=
  .floating fixtureLabel.name fixtureTypecode.name fixtureVariable.name

private def startCanaryAtoms : List Atom :=
  [floatingStartRule,
   .expression
     [.symbol "mm-source-current", fixtureOwner, natAtom 2, natAtom 3,
      rawStatementAtom fixtureStatement, fixtureDispatchInput,
      fixtureDispatchOutput],
   objectFrontierAtom fixtureOwner objectRootKey,
   objectFrontierAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey,
   objectFrontierAtom (variableTypecodeLedgerOwner fixtureOwner) objectRootKey,
   sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
     objectRootKey]

private def startCanarySpace : Space := startCanaryAtoms.toFinset
private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  simp [startCanaryAtoms, floatingStartRule, mkRule, fixtureOwner,
    objectFrontierAtom, activeVariableLedgerOwner,
    variableTypecodeLedgerOwner, sourceActivityFrontierAtom,
    activeHypothesisLedgerOwner]
private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms = [floatingStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some floatingStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms floatingStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies
      startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          floatingStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

private def freshObservation : Atom :=
  variableTypecodeMissingAtom fixtureOwner fixtureRequest fixtureVariable
private def freshObjectFrontier : Atom :=
  objectFrontierAtom fixtureOwner objectRootKey
private def freshHypothesisFrontier : Atom :=
  sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
    objectRootKey
private def freshHistoryFrontier : Atom :=
  objectFrontierAtom (variableTypecodeLedgerOwner fixtureOwner) objectRootKey
private def freshCanaryData : List Atom :=
  [freshObservation, freshObjectFrontier, freshHypothesisFrontier,
   floatingSourceReloadCaptureRow, freshHistoryFrontier]
private def freshCanaryAtoms : List Atom :=
  floatingHistoryFreshRule :: freshCanaryData

private def freshCanarySpace : Space := freshCanaryAtoms.toFinset
private theorem freshCanaryAtoms_nodup : freshCanaryAtoms.Nodup := by
  simp [freshCanaryAtoms, freshCanaryData, floatingHistoryFreshRule, mkRule,
    freshObservation, variableTypecodeMissingAtom,
    freshObjectFrontier, freshHypothesisFrontier, freshHistoryFrontier,
    objectFrontierAtom, sourceActivityFrontierAtom,
    floatingSourceReloadCaptureRow, fixtureOwner,
    variableTypecodeLedgerOwner]
private theorem freshCanaryAtoms_supported :
    cSupportedSourceExecFacts freshCanaryAtoms =
      [floatingHistoryFreshDirective] := by
  rfl

theorem freshCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace freshCanarySpace) =
      some floatingHistoryFreshDirective := by
  exact reflective_selects_of_computable_supported_singleton
    freshCanaryAtoms floatingHistoryFreshDirective freshCanaryAtoms_nodup
    freshCanaryAtoms_supported

private theorem freshCanary_fire_agreement :
    (cFireReflectiveSourceExecFact freshCanaryAtoms
        floatingHistoryFreshDirective).toFinset =
      fireReflectiveSourceExecFact freshCanarySpace
        floatingHistoryFreshDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    freshCanaryAtoms floatingHistoryFreshDirective freshCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      floatingHistoryFreshDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      freshCanaryAtoms floatingHistoryFreshDirective freshCanaryAtoms_nodup)

private def freshSubst1 : Subst :=
  (cmatchAtom [] historicalMissingTemplate freshObservation).getD []
private def freshSubst2 : Subst :=
  (cmatchAtom freshSubst1 objectFrontierTemplate freshObjectFrontier).getD []
private def freshSubst3 : Subst :=
  (cmatchAtom freshSubst2 hypothesisFrontierTemplate
    freshHypothesisFrontier).getD []
private def freshSubst4 : Subst :=
  (cmatchAtom freshSubst3 sourceReloadCaptureTemplate
    floatingSourceReloadCaptureRow).getD []
private def freshSubst5 : Subst :=
  (cmatchAtom freshSubst4 historyFrontierTemplate
    freshHistoryFrontier).getD []

private theorem fresh_match_path :
    MatchWitnessPath freshCanaryAtoms historyFreshPatterns [] [] freshSubst5
      [freshHistoryFrontier, floatingSourceReloadCaptureRow,
       freshHypothesisFrontier, freshObjectFrontier, freshObservation] := by
  apply MatchWitnessPath.cons (witness := freshObservation)
    (after := freshSubst1) (by simp [freshCanaryAtoms, freshCanaryData])
      (by decide +kernel)
  apply MatchWitnessPath.cons (witness := freshObjectFrontier)
    (after := freshSubst2) (by simp [freshCanaryAtoms, freshCanaryData])
      (by decide +kernel)
  apply MatchWitnessPath.cons (witness := freshHypothesisFrontier)
    (after := freshSubst3) (by simp [freshCanaryAtoms, freshCanaryData])
      (by decide +kernel)
  apply MatchWitnessPath.cons (witness := floatingSourceReloadCaptureRow)
    (after := freshSubst4) (by simp [freshCanaryAtoms, freshCanaryData])
      (by decide +kernel)
  apply MatchWitnessPath.cons (witness := freshHistoryFrontier)
    (after := freshSubst5) (by simp [freshCanaryAtoms, freshCanaryData])
      (by decide +kernel)
  exact MatchWitnessPath.nil _ _

private theorem fresh_match_row :
    freshSubst5 ∈
      (cmatchInputSpec []
        (floatingHistoryFreshDirective.atom ::
          freshCanaryAtoms.erase floatingHistoryFreshDirective.atom)
        floatingHistoryFreshDirective.rule.input).map Prod.fst := by
  have member := matchWitnessPath_mem_cmatchInputSpec fresh_match_path
  have eraseExact :
      freshCanaryAtoms.erase floatingHistoryFreshRule = freshCanaryData := by
    rfl
  rw [show floatingHistoryFreshDirective.atom =
      floatingHistoryFreshRule by rfl,
    show floatingHistoryFreshDirective.rule.input =
      .compat { atoms := historyFreshPatterns } by rfl,
    eraseExact]
  simpa only [freshCanaryAtoms] using member

private def freshCommitAdds : List Sink :=
  durableCommitAdds ++
    [.add appendedHistoryLinkTemplate,
     .add appendedHistoryFrontierTemplate,
     .add appendedHistoryBindingTemplate]

private theorem freshCommitAdds_all_add
    (sink : Sink) (member : sink ∈ freshCommitAdds) :
    ∃ atom, sink = .add atom := by
  simp [freshCommitAdds, durableCommitAdds] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem freshCanary_emits_add
    (authored candidate : Atom)
    (authoredMember : .add authored ∈ freshCommitAdds)
    (instantiates :
      instantiateTemplateAtom? freshSubst5 authored = some candidate) :
    candidate ∈ cFireReflectiveSourceExecFact freshCanaryAtoms
      floatingHistoryFreshDirective := by
  apply mem_cFireReflectiveSourceExecFact_of_add_only_suffix_member
    freshCanaryAtoms floatingHistoryFreshDirective
    (durableCommitRemovals historicalMissingTemplate ++
      [.remove historyFrontierTemplate])
    freshCommitAdds authored candidate (substitution := freshSubst5)
  · rfl
  · exact fresh_match_row
  · exact instantiates
  · exact freshCommitAdds_all_add
  · exact authoredMember

private def expectedLabelLink : Atom :=
  objectLinkAtom fixtureOwner objectRootKey (locatedNameAtom fixtureLabel)
    fixtureLabelEntry
private def expectedHistoryLink : Atom :=
  objectLinkAtom (variableTypecodeLedgerOwner fixtureOwner) objectRootKey
    (locatedNameAtom fixtureVariable)
    (variableTypecodeObjectOccurrence fixtureHistoryOccurrence)
private def expectedHistoryBinding : Atom :=
  variableTypecodeBindingAtom fixtureOwner fixtureHistoryOccurrence
private def expectedHypothesisLink : Atom :=
  activeHypothesisLinkAtom fixtureOwner objectRootKey
    (locatedNameAtom fixtureLabel) fixtureHypothesis

theorem freshCanary_commits_exact_rows :
    expectedLabelLink ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective /\
      expectedHistoryLink ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective /\
      expectedHistoryBinding ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective /\
      fixtureRuntimeRow ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective /\
      expectedHypothesisLink ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective /\
      sourceControlAtom fixtureOwner 3 ∈
        fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective := by
  have labelMember := freshCanary_emits_add appendedLabelLinkTemplate
    expectedLabelLink (by simp [freshCommitAdds, durableCommitAdds])
      (by decide +kernel)
  have historyMember := freshCanary_emits_add appendedHistoryLinkTemplate
    expectedHistoryLink (by simp [freshCommitAdds]) (by decide +kernel)
  have bindingMember := freshCanary_emits_add appendedHistoryBindingTemplate
    expectedHistoryBinding (by simp [freshCommitAdds]) (by decide +kernel)
  have runtimeMember := freshCanary_emits_add runtimeRowTemplate
    fixtureRuntimeRow (by simp [freshCommitAdds, durableCommitAdds])
      (by decide +kernel)
  have hypothesisMember := freshCanary_emits_add appendedHypothesisLinkTemplate
    expectedHypothesisLink (by simp [freshCommitAdds, durableCommitAdds])
      (by decide +kernel)
  have controlMember := freshCanary_emits_add nextSourceControlTemplate
    (sourceControlAtom fixtureOwner 3)
    (by simp [freshCommitAdds, durableCommitAdds]) (by decide +kernel)
  have promote {atom : Atom}
      (member : atom ∈ cFireReflectiveSourceExecFact freshCanaryAtoms
        floatingHistoryFreshDirective) :
      atom ∈ fireReflectiveSourceExecFact freshCanarySpace
        floatingHistoryFreshDirective := by
    rw [← freshCanary_fire_agreement]
    simpa using member
  exact ⟨promote labelMember, promote historyMember, promote bindingMember,
    promote runtimeMember, promote hypothesisMember, promote controlMember⟩

theorem freshCanary_inhabits_target_native_type :
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies
      freshCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact freshCanarySpace
          floatingHistoryFreshDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected freshCanary_selects_directive)

private def priorTypecode : LocatedName :=
  { span := fixtureSpan 20 23, name := "class" }
private def priorLabel : LocatedName :=
  { span := fixtureSpan 17 19, name := "vx" }
private def conflictOccurrence : VariableTypecodeOccurrence :=
  { statementPosition := 1
    label := priorLabel
    typecode := priorTypecode
    variableName := fixtureVariable }
private def conflictObservation : Atom :=
  variableTypecodeFoundAtom fixtureOwner fixtureRequest fixtureVariable
    conflictOccurrence

private def conflictCanaryAtoms : List Atom :=
  [floatingHistoryConflictRule, conflictObservation]
private def conflictCanarySpace : Space := conflictCanaryAtoms.toFinset
private theorem conflictCanaryAtoms_nodup : conflictCanaryAtoms.Nodup := by
  simp [conflictCanaryAtoms, floatingHistoryConflictRule, mkRule,
    conflictObservation, variableTypecodeFoundAtom]
private theorem conflictCanaryAtoms_supported :
    cSupportedSourceExecFacts conflictCanaryAtoms =
      [floatingHistoryConflictDirective] := by
  rfl

theorem conflictCanary_selects_rejection :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace conflictCanarySpace) =
      some floatingHistoryConflictDirective := by
  exact reflective_selects_of_computable_supported_singleton
    conflictCanaryAtoms floatingHistoryConflictDirective
    conflictCanaryAtoms_nodup conflictCanaryAtoms_supported

private theorem conflictCanary_fire_agreement :
    (cFireReflectiveSourceExecFact conflictCanaryAtoms
        floatingHistoryConflictDirective).toFinset =
      fireReflectiveSourceExecFact conflictCanarySpace
        floatingHistoryConflictDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    conflictCanaryAtoms floatingHistoryConflictDirective
    conflictCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      floatingHistoryConflictDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      conflictCanaryAtoms floatingHistoryConflictDirective
      conflictCanaryAtoms_nodup)

def incompatibleTypecodeRejectedAtom : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 2,
      rawStatementAtom fixtureStatement,
      .symbol "incompatible-floating-typecode",
      .expression
        [.symbol "mm-source-historical-typecode-evidence",
          objectOccurrenceAtom
            (variableTypecodeObjectOccurrence conflictOccurrence),
          .expression
            [.symbol "mm-source-variable-typecode-payload", natAtom 1,
              locatedNameAtom priorLabel, locatedNameAtom priorTypecode]]]

theorem conflictCanary_rejects_without_durable_effects :
    incompatibleTypecodeRejectedAtom ∈
        fireReflectiveSourceExecFact conflictCanarySpace
          floatingHistoryConflictDirective /\
      objectLinkAtom fixtureOwner objectRootKey (locatedNameAtom fixtureLabel)
          fixtureLabelEntry ∉
        fireReflectiveSourceExecFact conflictCanarySpace
          floatingHistoryConflictDirective /\
      fixtureRuntimeRow ∉
        fireReflectiveSourceExecFact conflictCanarySpace
          floatingHistoryConflictDirective /\
      sourceControlAtom fixtureOwner 3 ∉
        fireReflectiveSourceExecFact conflictCanarySpace
          floatingHistoryConflictDirective := by
  rw [← conflictCanary_fire_agreement]
  decide +kernel

section AxiomAudit

#print axioms floatingDeclaration_inhabits_source_native_type
#print axioms floatingDeclarationRules_extract_exact
#print axioms floatingLookupStaticRows_not_proofNeutral
#print axioms floatingSourceReloadCaptureRow_not_proofNeutral
#print axioms startCanary_inhabits_target_native_type
#print axioms freshCanary_commits_exact_rows
#print axioms freshCanary_inhabits_target_native_type
#print axioms conflictCanary_rejects_without_durable_effects

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration
