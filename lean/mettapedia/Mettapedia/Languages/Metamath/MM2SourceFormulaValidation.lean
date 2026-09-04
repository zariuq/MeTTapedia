import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration

/-!
# Source-formula validation in ordinary MM2

This module checks an untrusted tagged formula against the exact located names
of a source statement and the live source-owned object ledgers.  The typecode
must be a declared constant.  Every body occurrence must agree simultaneously
with its raw source name, its proposed constant/variable tag, and either the
permanent constant inventory or the active-variable inventory.

The validator does not construct a formula and does not authorize a source
declaration.  It turns a candidate into a verifier-owned completion
observation that declaration coordinators may consume together with their
independent source controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceFormulaValidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Protected protocol atoms -/

def formulaValidationRequestAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName) (body : List LocatedName)
    (candidateFormula : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-request", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula]

def formulaTypecodeControlAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName) (body : List LocatedName)
    (candidateFormula globalFrontier activeFrontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-typecode-control", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula, globalFrontier,
      activeFrontier]

def formulaBodyControlAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName)
    (originalBody : List LocatedName)
    (candidateFormula : Atom) (candidate : LocatedName)
    (remaining : List LocatedName) (encodedCandidate encodedRemaining : Atom)
    (globalFrontier activeFrontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-body-control", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom originalBody, candidateFormula,
      locatedNameAtom candidate, listAtom locatedNameAtom remaining,
      encodedCandidate, encodedRemaining, globalFrontier, activeFrontier]

def formulaTypecodeValidatedAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName)
    (originalBody : List LocatedName) (candidateFormula : Atom)
    (currentBody : List LocatedName) (currentEncodedBody globalFrontier
      activeFrontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-typecode-validated", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom originalBody, candidateFormula,
      listAtom locatedNameAtom currentBody, currentEncodedBody,
      globalFrontier, activeFrontier]

def formulaSymbolValidatedAtom (control : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-symbol-validated", control]

def formulaValidationCompleteAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName) (body : List LocatedName)
    (candidateFormula : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-complete", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula]

def formulaValidationFaultAtom (owner : Atom) (statementPosition : Nat)
    (continuationKey : Atom) (typecode : LocatedName) (body : List LocatedName)
    (candidateFormula : Atom) (reason : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-fault", owner,
      natAtom statementPosition, continuationKey, locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula, .symbol reason]

def formulaValidationCompleteContinuationRow (key rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-continuation",
      .symbol "complete", key, rule]

def formulaValidationFaultContinuationRow (key rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-continuation",
      .symbol "fault", key, rule]

@[simp] theorem formulaValidationCompleteContinuationRow_not_proofNeutral
    (key rule : Atom) :
    isProofNeutralInitialAtom
      (formulaValidationCompleteContinuationRow key rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-formula-validation-continuation"
      [.symbol "complete", key, rule] (by decide)

@[simp] theorem formulaValidationFaultContinuationRow_not_proofNeutral
    (key rule : Atom) :
    isProofNeutralInitialAtom
      (formulaValidationFaultContinuationRow key rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-formula-validation-continuation"
      [.symbol "fault", key, rule] (by decide)

@[simp] theorem formulaValidationRequestAtom_not_proofNeutral
    (owner : Atom) (statementPosition : Nat) (typecode : LocatedName)
    (continuationKey : Atom) (body : List LocatedName)
    (candidateFormula : Atom) :
    isProofNeutralInitialAtom
      (formulaValidationRequestAtom owner statementPosition continuationKey
        typecode body candidateFormula) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-formula-validation-request"
    [owner, natAtom statementPosition, continuationKey,
      locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula] (by decide)

@[simp] theorem formulaValidationCompleteAtom_not_proofNeutral
    (owner : Atom) (statementPosition : Nat) (typecode : LocatedName)
    (continuationKey : Atom) (body : List LocatedName)
    (candidateFormula : Atom) :
    isProofNeutralInitialAtom
      (formulaValidationCompleteAtom owner statementPosition continuationKey
        typecode body candidateFormula) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-formula-validation-complete"
    [owner, natAtom statementPosition, continuationKey,
      locatedNameAtom typecode,
      listAtom locatedNameAtom body, candidateFormula] (by decide)

/-! ## Ordinary MM2 templates -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def typecodeTemplate : Atom := locatedNameTemplate "typecode"
private def candidateTemplate : Atom := locatedNameTemplate "candidate"
private def nextTemplate : Atom := locatedNameTemplate "next"

private def encodedConstTemplate (name : Atom) : Atom :=
  .expression [.symbol "mm-const", name]

private def encodedVariableTemplate (name : Atom) : Atom :=
  .expression [.symbol "mm-variable", name]

private def exactFormulaTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "typecode-name", .var "encoded-body"]

private def exactRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-request", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate]

private def anyRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-request", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", .var "candidate-formula"]

private def globalFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source",
      .var "global-frontier"]

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", .var "source"]

private def activeFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", activeOwnerTemplate,
      .var "active-frontier"]

private def typecodeControlTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-typecode-control", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate, .var "global-frontier",
      .var "active-frontier"]

private def bodyControlTemplate (candidate remaining encodedCandidate
    encodedRemaining : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-body-control", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate, candidate, remaining,
      encodedCandidate, encodedRemaining, .var "global-frontier",
      .var "active-frontier"]

private def anyBodyControlTemplate : Atom :=
  bodyControlTemplate candidateTemplate (.var "remaining-body")
    (.var "encoded-candidate") (.var "encoded-remaining")

private def bodyMoreControlTemplate (nextEncoded : Atom) : Atom :=
  bodyControlTemplate candidateTemplate
    (.expression [.symbol "mm-cons", nextTemplate, .var "after-next"])
    (.var "encoded-candidate")
    (.expression
      [.symbol "mm-cons", nextEncoded, .var "encoded-after-next"])

private def bodyLastControlTemplate : Atom :=
  bodyControlTemplate candidateTemplate nilTemplate
    (.var "encoded-candidate") nilTemplate

private def nextBodyControlTemplate (nextEncoded : Atom) : Atom :=
  bodyControlTemplate nextTemplate (.var "after-next")
    nextEncoded (.var "encoded-after-next")

private def typecodeValidatedTemplate (rawBody encodedBody : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-typecode-validated", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate, rawBody, encodedBody,
      .var "global-frontier", .var "active-frontier"]

private def exactTypecodeValidatedTemplate : Atom :=
  typecodeValidatedTemplate (.var "original-body") (.var "encoded-body")

private def symbolValidatedTemplate (control : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-symbol-validated", control]

private def completeTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-complete", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate]

private def faultTemplate (reason : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-fault", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", exactFormulaTemplate, .symbol reason]

private def completeContinuationTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-continuation",
      .symbol "complete", .var "validation-key",
      .var "formula-validation-continuation-rule"]

private def faultContinuationTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-continuation",
      .symbol "fault", .var "validation-key",
      .var "formula-validation-continuation-rule"]

private def continuationSink : Sink :=
  .add (.var "formula-validation-continuation-rule")

private def malformedRequestFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-fault", .var "source",
      .var "statement-position", .var "validation-key", typecodeTemplate,
      .var "original-body", .var "candidate-formula",
      .symbol "formula-encoding"]

private def lookupTemplate (owner key request candidate frontier : Atom) :
    Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", owner, key, request,
      candidate, objectRootKey, frontier]

private def typecodeLookupKey : Atom :=
  .symbol "mm-source-formula-typecode-lookup"

private def bodyConstantLookupKey : Atom :=
  .symbol "mm-source-formula-body-constant-lookup"

private def bodyVariableLookupKey : Atom :=
  .symbol "mm-source-formula-body-variable-lookup"

private def activeVariableLookupKey : Atom :=
  .symbol "mm-source-formula-active-variable-lookup"

private def foundTemplate (owner request candidate kind : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-found", owner, request, candidate,
      .expression
        [.symbol "mm-source-object-entry", kind,
          .expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "candidate-name"]]]

private def missingTemplate (owner request candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", owner, request, candidate]

private def globalTypecodeLookupTemplate : Atom :=
  lookupTemplate (.var "source") typecodeLookupKey typecodeControlTemplate
    typecodeTemplate (.var "global-frontier")

private def globalBodyLookupTemplate (key control candidate : Atom) : Atom :=
  lookupTemplate (.var "source") key control candidate
    (.var "global-frontier")

private def activeBodyLookupTemplate (control candidate : Atom) : Atom :=
  lookupTemplate activeOwnerTemplate activeVariableLookupKey control candidate
    (.var "active-frontier")

private def globalReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", .var "source"]

private def activeReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", activeOwnerTemplate]

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

private def persistentRule (priority : Nat) (name : String)
    (patterns : List Atom) (sinks : List Sink) : Atom × SourceExecFact :=
  let loc := location (if priority < 10 then "0" ++ toString priority else
    toString priority) name
  let self := selfTemplate loc name
  let allPatterns := self :: patterns
  let allSinks := .add self :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc priority name allPatterns allSinks)

/-! Continuations are captured from protected verifier rows at the stage that
needs them.  This keeps the object walker generic while making each formula
stage's finite continuation set deterministic. -/

private def capturedRuleTemplate (slot variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-rule", .symbol slot,
      .var variableName]

private def capturedRuleSink (variableName : String) : Sink :=
  .add (.var variableName)

/-! ## Request and typecode stages -/

private def startPair : Atom × SourceExecFact :=
  persistentRule 3 "mm-source-formula-validation-start"
    [exactRequestTemplate, globalFrontierTemplate, activeFrontierTemplate]
    [.remove exactRequestTemplate,
      .add globalTypecodeLookupTemplate, .add globalReloadTemplate]

def validationStartRule : Atom := startPair.1
def validationStartDirective : SourceExecFact := startPair.2

private def malformedRequestPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-validation-malformed-request"
    [anyRequestTemplate,
      faultContinuationTemplate]
    [.remove anyRequestTemplate, .add malformedRequestFaultTemplate,
      continuationSink]

def validationMalformedRequestRule : Atom := malformedRequestPair.1
def validationMalformedRequestDirective : SourceExecFact :=
  malformedRequestPair.2

private def typecodeFound (kind : ObjectKind) : Atom :=
  foundTemplate (.var "source") typecodeControlTemplate typecodeTemplate
    (objectKindAtom kind)

private def typecodeFoundConstantPair : Atom × SourceExecFact :=
  persistentRule 3 "mm-source-formula-typecode-constant"
    [typecodeFound .constant,
      capturedRuleTemplate "typecode-empty" "typecode-empty-rule",
      capturedRuleTemplate "typecode-begin-constant"
        "typecode-begin-constant-rule",
      capturedRuleTemplate "typecode-begin-variable"
        "typecode-begin-variable-rule",
      capturedRuleTemplate "typecode-shape-fault" "typecode-shape-fault-rule"]
    [.remove (typecodeFound .constant),
      .add exactTypecodeValidatedTemplate,
      capturedRuleSink "typecode-empty-rule",
      capturedRuleSink "typecode-begin-constant-rule",
      capturedRuleSink "typecode-begin-variable-rule",
      capturedRuleSink "typecode-shape-fault-rule"]

def validationTypecodeConstantRule : Atom := typecodeFoundConstantPair.1
def validationTypecodeConstantDirective : SourceExecFact :=
  typecodeFoundConstantPair.2

private def typecodeFaultPair (kind : ObjectKind) (name reason : String) :
    Atom × SourceExecFact :=
  persistentRule 4 name
    [typecodeFound kind, faultContinuationTemplate]
    [.remove (typecodeFound kind), .add (faultTemplate reason),
      continuationSink]

def validationTypecodeVariableRule : Atom :=
  (typecodeFaultPair .variable "mm-source-formula-typecode-variable"
    "typecode-not-constant").1
def validationTypecodeVariableDirective : SourceExecFact :=
  (typecodeFaultPair .variable "mm-source-formula-typecode-variable"
    "typecode-not-constant").2

def validationTypecodeLabelRule : Atom :=
  (typecodeFaultPair .label "mm-source-formula-typecode-label"
    "typecode-not-constant").1
def validationTypecodeLabelDirective : SourceExecFact :=
  (typecodeFaultPair .label "mm-source-formula-typecode-label"
    "typecode-not-constant").2

private def typecodeMissingTemplate : Atom :=
  missingTemplate (.var "source") typecodeControlTemplate typecodeTemplate

private def typecodeMissingPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-typecode-missing"
    [typecodeMissingTemplate,
      faultContinuationTemplate]
    [.remove typecodeMissingTemplate,
      .add (faultTemplate "undeclared-typecode"), continuationSink]

def validationTypecodeMissingRule : Atom := typecodeMissingPair.1
def validationTypecodeMissingDirective : SourceExecFact :=
  typecodeMissingPair.2

private def typecodeEmptyValidatedTemplate : Atom :=
  typecodeValidatedTemplate nilTemplate nilTemplate

private def typecodeBeginValidatedTemplate (encodedCandidate : Atom) : Atom :=
  typecodeValidatedTemplate
    (.expression
      [.symbol "mm-cons", candidateTemplate, .var "remaining-body"])
    (.expression
      [.symbol "mm-cons", encodedCandidate, .var "encoded-remaining"])

private def initialBodyControlTemplate (encodedCandidate : Atom) : Atom :=
  bodyControlTemplate candidateTemplate (.var "remaining-body")
    encodedCandidate (.var "encoded-remaining")

private def typecodeEmptyPair : Atom × SourceExecFact :=
  persistentRule 3 "mm-source-formula-empty-body"
    [typecodeEmptyValidatedTemplate, completeContinuationTemplate]
    [.remove typecodeEmptyValidatedTemplate, .add completeTemplate,
      continuationSink]

def validationTypecodeEmptyRule : Atom := typecodeEmptyPair.1
def validationTypecodeEmptyDirective : SourceExecFact := typecodeEmptyPair.2

private def typecodeBeginPair (encodedCandidate key : Atom)
    (name : String) : Atom × SourceExecFact :=
  let validated := typecodeBeginValidatedTemplate encodedCandidate
  persistentRule 3 name [validated]
    [.remove validated,
      .add (globalBodyLookupTemplate key
        (initialBodyControlTemplate encodedCandidate) candidateTemplate),
      .add globalReloadTemplate]

def validationTypecodeBeginConstantRule : Atom :=
  (typecodeBeginPair (encodedConstTemplate (.var "candidate-name"))
    bodyConstantLookupKey "mm-source-formula-body-begin-constant").1
def validationTypecodeBeginConstantDirective : SourceExecFact :=
  (typecodeBeginPair (encodedConstTemplate (.var "candidate-name"))
    bodyConstantLookupKey "mm-source-formula-body-begin-constant").2

def validationTypecodeBeginVariableRule : Atom :=
  (typecodeBeginPair (encodedVariableTemplate (.var "candidate-name"))
    bodyVariableLookupKey "mm-source-formula-body-begin-variable").1
def validationTypecodeBeginVariableDirective : SourceExecFact :=
  (typecodeBeginPair (encodedVariableTemplate (.var "candidate-name"))
    bodyVariableLookupKey "mm-source-formula-body-begin-variable").2

private def typecodeShapeFaultPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-body-shape-fault"
    [exactTypecodeValidatedTemplate,
      faultContinuationTemplate]
    [.remove exactTypecodeValidatedTemplate,
      .add (faultTemplate "body-shape-mismatch"), continuationSink]

def validationTypecodeShapeFaultRule : Atom := typecodeShapeFaultPair.1
def validationTypecodeShapeFaultDirective : SourceExecFact :=
  typecodeShapeFaultPair.2

/-! ## Body-symbol classification -/

private def globalBodyFound (kind : ObjectKind) (control : Atom) : Atom :=
  foundTemplate (.var "source") control candidateTemplate
    (objectKindAtom kind)

private def bodyConstControlTemplate : Atom :=
  bodyControlTemplate candidateTemplate (.var "remaining-body")
    (encodedConstTemplate (.var "candidate-name"))
    (.var "encoded-remaining")

private def bodyVariableControlTemplate : Atom :=
  bodyControlTemplate candidateTemplate (.var "remaining-body")
    (encodedVariableTemplate (.var "candidate-name"))
    (.var "encoded-remaining")

private def bodyConstantPair : Atom × SourceExecFact :=
  let found := globalBodyFound .constant bodyConstControlTemplate
  persistentRule 3 "mm-source-formula-body-constant"
    [found,
      capturedRuleTemplate "symbol-more-constant"
        "symbol-more-constant-rule",
      capturedRuleTemplate "symbol-more-variable"
        "symbol-more-variable-rule",
      capturedRuleTemplate "symbol-last" "symbol-last-rule",
      capturedRuleTemplate "symbol-shape-fault" "symbol-shape-fault-rule"]
    [.remove found, .add (symbolValidatedTemplate bodyConstControlTemplate),
      capturedRuleSink "symbol-more-constant-rule",
      capturedRuleSink "symbol-more-variable-rule",
      capturedRuleSink "symbol-last-rule",
      capturedRuleSink "symbol-shape-fault-rule"]

def validationBodyConstantRule : Atom := bodyConstantPair.1
def validationBodyConstantDirective : SourceExecFact := bodyConstantPair.2

private def bodyVariablePair : Atom × SourceExecFact :=
  let found := globalBodyFound .variable bodyVariableControlTemplate
  persistentRule 3 "mm-source-formula-body-variable" [found]
    [.remove found,
      .add (activeBodyLookupTemplate bodyVariableControlTemplate
        candidateTemplate), .add activeReloadTemplate]

def validationBodyVariableRule : Atom := bodyVariablePair.1
def validationBodyVariableDirective : SourceExecFact := bodyVariablePair.2

private def bodyLabelFoundTemplate : Atom :=
  globalBodyFound .label anyBodyControlTemplate

private def bodyLabelPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-body-label"
    [bodyLabelFoundTemplate,
      faultContinuationTemplate]
    [.remove bodyLabelFoundTemplate, .add (faultTemplate "body-label"),
      continuationSink]

def validationBodyLabelRule : Atom := bodyLabelPair.1
def validationBodyLabelDirective : SourceExecFact := bodyLabelPair.2

private def bodyMissingObservationTemplate : Atom :=
  missingTemplate (.var "source") anyBodyControlTemplate candidateTemplate

private def bodyMissingPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-body-missing"
    [bodyMissingObservationTemplate,
      faultContinuationTemplate]
    [.remove bodyMissingObservationTemplate,
      .add (faultTemplate "undeclared-body-symbol"), continuationSink]

def validationBodyMissingRule : Atom := bodyMissingPair.1
def validationBodyMissingDirective : SourceExecFact := bodyMissingPair.2

private def bodyTagMismatchPair (kind : ObjectKind) (name : String) :
    Atom × SourceExecFact :=
  let found := globalBodyFound kind anyBodyControlTemplate
  persistentRule 5 name
    [found, faultContinuationTemplate]
    [.remove found, .add (faultTemplate "body-tag-mismatch"),
      continuationSink]

def validationBodyConstantTagMismatchRule : Atom :=
  (bodyTagMismatchPair .constant
    "mm-source-formula-body-constant-tag-mismatch").1
def validationBodyConstantTagMismatchDirective : SourceExecFact :=
  (bodyTagMismatchPair .constant
    "mm-source-formula-body-constant-tag-mismatch").2

def validationBodyVariableTagMismatchRule : Atom :=
  (bodyTagMismatchPair .variable
    "mm-source-formula-body-variable-tag-mismatch").1
def validationBodyVariableTagMismatchDirective : SourceExecFact :=
  (bodyTagMismatchPair .variable
    "mm-source-formula-body-variable-tag-mismatch").2

private def activeBodyFound (kind : ObjectKind) : Atom :=
  foundTemplate activeOwnerTemplate bodyVariableControlTemplate
    candidateTemplate (objectKindAtom kind)

private def activeVariablePair : Atom × SourceExecFact :=
  let found := activeBodyFound .variable
  persistentRule 3 "mm-source-formula-active-variable"
    [found,
      capturedRuleTemplate "symbol-more-constant"
        "symbol-more-constant-rule",
      capturedRuleTemplate "symbol-more-variable"
        "symbol-more-variable-rule",
      capturedRuleTemplate "symbol-last" "symbol-last-rule",
      capturedRuleTemplate "symbol-shape-fault" "symbol-shape-fault-rule"]
    [.remove found,
      .add (symbolValidatedTemplate bodyVariableControlTemplate),
      capturedRuleSink "symbol-more-constant-rule",
      capturedRuleSink "symbol-more-variable-rule",
      capturedRuleSink "symbol-last-rule",
      capturedRuleSink "symbol-shape-fault-rule"]

def validationActiveVariableRule : Atom := activeVariablePair.1
def validationActiveVariableDirective : SourceExecFact := activeVariablePair.2

private def activeFaultPair (kind : ObjectKind) (name : String) :
    Atom × SourceExecFact :=
  let found := activeBodyFound kind
  persistentRule 4 name
    [found, faultContinuationTemplate]
    [.remove found, .add (faultTemplate "wrong-active-kind"),
      continuationSink]

def validationActiveConstantRule : Atom :=
  (activeFaultPair .constant "mm-source-formula-active-constant").1
def validationActiveConstantDirective : SourceExecFact :=
  (activeFaultPair .constant "mm-source-formula-active-constant").2

def validationActiveLabelRule : Atom :=
  (activeFaultPair .label "mm-source-formula-active-label").1
def validationActiveLabelDirective : SourceExecFact :=
  (activeFaultPair .label "mm-source-formula-active-label").2

private def activeMissingObservationTemplate : Atom :=
  missingTemplate activeOwnerTemplate bodyVariableControlTemplate
    candidateTemplate

private def activeMissingPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-active-missing"
    [activeMissingObservationTemplate,
      faultContinuationTemplate]
    [.remove activeMissingObservationTemplate,
      .add (faultTemplate "inactive-body-variable"), continuationSink]

def validationActiveMissingRule : Atom := activeMissingPair.1
def validationActiveMissingDirective : SourceExecFact := activeMissingPair.2

/-! ## Exact list advancement -/

private def symbolMoreValidatedTemplate (nextEncoded : Atom) : Atom :=
  symbolValidatedTemplate (bodyMoreControlTemplate nextEncoded)

private def symbolLastValidatedTemplate : Atom :=
  symbolValidatedTemplate bodyLastControlTemplate

private def symbolAnyValidatedTemplate : Atom :=
  symbolValidatedTemplate anyBodyControlTemplate

private def symbolMorePair (nextEncoded key : Atom)
    (name : String) : Atom × SourceExecFact :=
  let validated := symbolMoreValidatedTemplate nextEncoded
  persistentRule 3 name [validated]
    [.remove validated,
      .add (globalBodyLookupTemplate key
        (nextBodyControlTemplate nextEncoded) nextTemplate),
      .add globalReloadTemplate]

def validationSymbolMoreConstantRule : Atom :=
  (symbolMorePair (encodedConstTemplate (.var "next-name"))
    bodyConstantLookupKey "mm-source-formula-symbol-more-constant").1
def validationSymbolMoreConstantDirective : SourceExecFact :=
  (symbolMorePair (encodedConstTemplate (.var "next-name"))
    bodyConstantLookupKey "mm-source-formula-symbol-more-constant").2

def validationSymbolMoreVariableRule : Atom :=
  (symbolMorePair (encodedVariableTemplate (.var "next-name"))
    bodyVariableLookupKey "mm-source-formula-symbol-more-variable").1
def validationSymbolMoreVariableDirective : SourceExecFact :=
  (symbolMorePair (encodedVariableTemplate (.var "next-name"))
    bodyVariableLookupKey "mm-source-formula-symbol-more-variable").2

private def symbolLastPair : Atom × SourceExecFact :=
  persistentRule 3 "mm-source-formula-symbol-last"
    [symbolLastValidatedTemplate, completeContinuationTemplate]
    [.remove symbolLastValidatedTemplate, .add completeTemplate,
      continuationSink]

def validationSymbolLastRule : Atom := symbolLastPair.1
def validationSymbolLastDirective : SourceExecFact := symbolLastPair.2

private def symbolShapeFaultPair : Atom × SourceExecFact :=
  persistentRule 4 "mm-source-formula-symbol-shape-fault"
    [symbolAnyValidatedTemplate,
      faultContinuationTemplate]
    [.remove symbolAnyValidatedTemplate,
      .add (faultTemplate "body-shape-mismatch"), continuationSink]

def validationSymbolShapeFaultRule : Atom := symbolShapeFaultPair.1
def validationSymbolShapeFaultDirective : SourceExecFact :=
  symbolShapeFaultPair.2

/-! ## Inventory and exact executable extraction -/

def formulaValidationRules : List Atom :=
  [validationStartRule, validationMalformedRequestRule,
   validationTypecodeConstantRule, validationTypecodeVariableRule,
   validationTypecodeLabelRule, validationTypecodeMissingRule,
   validationTypecodeEmptyRule, validationTypecodeBeginConstantRule,
   validationTypecodeBeginVariableRule,
   validationTypecodeShapeFaultRule, validationBodyConstantRule,
   validationBodyVariableRule, validationBodyLabelRule,
   validationBodyMissingRule, validationBodyConstantTagMismatchRule,
   validationBodyVariableTagMismatchRule, validationActiveVariableRule,
   validationActiveConstantRule, validationActiveLabelRule,
   validationActiveMissingRule, validationSymbolMoreConstantRule,
   validationSymbolMoreVariableRule,
   validationSymbolLastRule, validationSymbolShapeFaultRule]

def formulaValidationDirectives : List SourceExecFact :=
  [validationStartDirective, validationMalformedRequestDirective,
   validationTypecodeConstantDirective, validationTypecodeVariableDirective,
   validationTypecodeLabelDirective, validationTypecodeMissingDirective,
   validationTypecodeEmptyDirective, validationTypecodeBeginConstantDirective,
   validationTypecodeBeginVariableDirective,
   validationTypecodeShapeFaultDirective, validationBodyConstantDirective,
   validationBodyVariableDirective, validationBodyLabelDirective,
   validationBodyMissingDirective,
   validationBodyConstantTagMismatchDirective,
   validationBodyVariableTagMismatchDirective,
   validationActiveVariableDirective, validationActiveConstantDirective,
   validationActiveLabelDirective, validationActiveMissingDirective,
   validationSymbolMoreConstantDirective,
   validationSymbolMoreVariableDirective, validationSymbolLastDirective,
   validationSymbolShapeFaultDirective]

theorem formulaValidationRules_extract_exact :
    formulaValidationRules.filterMap extractSupportedSourceExecFact =
      formulaValidationDirectives := by
  rfl

def formulaValidationRuleCaptureRow (slot : String) (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-formula-validation-rule", .symbol slot,
      rule]

private def formulaValidationCapturedRules : List (String × Atom) :=
  [("typecode-empty", validationTypecodeEmptyRule),
   ("typecode-begin-constant", validationTypecodeBeginConstantRule),
   ("typecode-begin-variable", validationTypecodeBeginVariableRule),
   ("typecode-shape-fault", validationTypecodeShapeFaultRule),
   ("symbol-more-constant", validationSymbolMoreConstantRule),
   ("symbol-more-variable", validationSymbolMoreVariableRule),
   ("symbol-last", validationSymbolLastRule),
   ("symbol-shape-fault", validationSymbolShapeFaultRule)]

private structure FoundContinuation where
  key : Atom
  kind : ObjectKind
  rule : Atom

private structure MissingContinuation where
  key : Atom
  rule : Atom

private def formulaValidationFoundContinuations : List FoundContinuation :=
  [{ key := typecodeLookupKey, kind := .constant,
      rule := validationTypecodeConstantRule },
   { key := typecodeLookupKey, kind := .variable,
      rule := validationTypecodeVariableRule },
   { key := typecodeLookupKey, kind := .label,
      rule := validationTypecodeLabelRule },
   { key := bodyConstantLookupKey, kind := .constant,
      rule := validationBodyConstantRule },
   { key := bodyConstantLookupKey, kind := .variable,
      rule := validationBodyVariableTagMismatchRule },
   { key := bodyConstantLookupKey, kind := .label,
      rule := validationBodyLabelRule },
   { key := bodyVariableLookupKey, kind := .constant,
      rule := validationBodyConstantTagMismatchRule },
   { key := bodyVariableLookupKey, kind := .variable,
      rule := validationBodyVariableRule },
   { key := bodyVariableLookupKey, kind := .label,
      rule := validationBodyLabelRule },
   { key := activeVariableLookupKey, kind := .variable,
      rule := validationActiveVariableRule },
   { key := activeVariableLookupKey, kind := .constant,
      rule := validationActiveConstantRule },
   { key := activeVariableLookupKey, kind := .label,
      rule := validationActiveLabelRule }]

private def formulaValidationMissingContinuations :
    List MissingContinuation :=
  [{ key := typecodeLookupKey, rule := validationTypecodeMissingRule },
   { key := bodyConstantLookupKey, rule := validationBodyMissingRule },
   { key := bodyVariableLookupKey, rule := validationBodyMissingRule },
   { key := activeVariableLookupKey, rule := validationActiveMissingRule }]

def formulaValidationLookupRows : List Atom :=
  (formulaValidationFoundContinuations.map fun entry =>
    objectLookupFoundContinuationRow entry.key entry.kind entry.rule) ++
  (formulaValidationMissingContinuations.map fun entry =>
    objectLookupMissingContinuationRow entry.key entry.rule)

/-- Each stage obtains its exact finite continuation family from opaque,
verifier-owned rows.  The object walker keeps its scan family generic. -/
def formulaValidationStaticRows : List Atom :=
  (formulaValidationCapturedRules.map fun entry =>
    formulaValidationRuleCaptureRow entry.1 entry.2) ++
    formulaValidationLookupRows

theorem formulaValidationStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ formulaValidationStaticRows) :
    isProofNeutralInitialAtom row = false := by
  rw [formulaValidationStaticRows] at member
  rcases List.mem_append.mp member with captured | lookup
  · rw [List.mem_map] at captured
    obtain ⟨⟨slot, rule⟩, _, rfl⟩ := captured
    exact verifier_owned_internal_prefix_not_proofNeutral
      "mm-internal-source-formula-validation-rule" [.symbol slot, rule]
        (by decide)
  · rw [formulaValidationLookupRows, List.mem_append] at lookup
    rcases lookup with found | missing
    · rw [List.mem_map] at found
      obtain ⟨entry, _, rfl⟩ := found
      exact objectLookupFoundContinuationRow_not_proofNeutral
        entry.key entry.kind entry.rule
    · rw [List.mem_map] at missing
      obtain ⟨entry, _, rfl⟩ := missing
      exact objectLookupMissingContinuationRow_not_proofNeutral
        entry.key entry.rule

/-! ## Positive and hostile controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "formula-validation.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureOwner : Atom := .symbol "formula-validation-source"
private def fixtureValidationKey : Atom :=
  .symbol "formula-validation-caller"
private def fixtureTypecode : LocatedName := fixtureName "wff" 0 3
private def fixtureVariable : LocatedName := fixtureName "x" 4 5
private def fixtureBody : List LocatedName := [fixtureVariable]
private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [.var "x"] }
private def fixtureFormulaAtom : Atom := formulaAtom fixtureFormula
private def fixtureGlobalEntries : List ObjectOccurrence :=
  [{ kind := .constant, occurrence := fixtureTypecode },
   { kind := .variable, occurrence := fixtureVariable }]
private def fixtureActiveEntries : List ObjectOccurrence :=
  [activeOccurrenceEntry fixtureVariable]
private def fixtureGlobalFrontier : Atom :=
  objectFrontierKey fixtureGlobalEntries
private def fixtureActiveFrontier : Atom :=
  objectFrontierKey fixtureActiveEntries
private def fixtureRequest : Atom :=
  formulaValidationRequestAtom fixtureOwner 0 fixtureValidationKey
    fixtureTypecode fixtureBody fixtureFormulaAtom

private def fixtureTypecodeControl : Atom :=
  formulaTypecodeControlAtom fixtureOwner 0 fixtureValidationKey
    fixtureTypecode fixtureBody fixtureFormulaAtom fixtureGlobalFrontier
    fixtureActiveFrontier

private def fixtureBodyControl : Atom :=
  formulaBodyControlAtom fixtureOwner 0 fixtureValidationKey fixtureTypecode
    fixtureBody fixtureFormulaAtom fixtureVariable []
    (runtimeSymAtom (.var "x")) (.expression [.symbol "mm-nil"])
    fixtureGlobalFrontier fixtureActiveFrontier

private def startCanaryAtoms : List Atom :=
  [validationStartRule, fixtureRequest,
   objectFrontierAtom fixtureOwner fixtureGlobalFrontier,
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

theorem startCanary_emits_exact_typecode_lookup :
    keyedLookupAtom fixtureOwner typecodeLookupKey fixtureTypecodeControl
        fixtureTypecode
        objectRootKey fixtureGlobalFrontier ∈
      fireReflectiveSourceExecFact startCanarySpace
        validationStartDirective := by
  rw [← startCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def activeFoundCanaryAtoms : List Atom :=
  [validationActiveVariableRule,
   lookupFoundAtom (activeVariableLedgerOwner fixtureOwner)
     fixtureBodyControl fixtureVariable (activeOccurrenceEntry fixtureVariable),
   formulaValidationRuleCaptureRow "symbol-more-constant"
     validationSymbolMoreConstantRule,
   formulaValidationRuleCaptureRow "symbol-more-variable"
     validationSymbolMoreVariableRule,
   formulaValidationRuleCaptureRow "symbol-last" validationSymbolLastRule,
   formulaValidationRuleCaptureRow "symbol-shape-fault"
     validationSymbolShapeFaultRule]

private def activeFoundCanarySpace : Space := activeFoundCanaryAtoms.toFinset

private theorem activeFoundCanaryAtoms_nodup :
    activeFoundCanaryAtoms.Nodup := by decide +kernel

private theorem activeFoundCanary_fire_agreement :
    (cFireReflectiveSourceExecFact activeFoundCanaryAtoms
        validationActiveVariableDirective).toFinset =
      fireReflectiveSourceExecFact activeFoundCanarySpace
        validationActiveVariableDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    activeFoundCanaryAtoms validationActiveVariableDirective
    activeFoundCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationActiveVariableDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      activeFoundCanaryAtoms validationActiveVariableDirective
      activeFoundCanaryAtoms_nodup)

theorem activeFoundCanary_validates_exact_tagged_occurrence :
    formulaSymbolValidatedAtom fixtureBodyControl ∈
      fireReflectiveSourceExecFact activeFoundCanarySpace
        validationActiveVariableDirective := by
  rw [← activeFoundCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def wrongTaggedFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [.const "x"] }
private def wrongTaggedFormulaAtom : Atom := formulaAtom wrongTaggedFormula
private def wrongTaggedControl : Atom :=
  formulaBodyControlAtom fixtureOwner 0 fixtureValidationKey fixtureTypecode
    fixtureBody wrongTaggedFormulaAtom fixtureVariable []
    (runtimeSymAtom (.const "x")) (.expression [.symbol "mm-nil"])
    fixtureGlobalFrontier fixtureActiveFrontier

private def wrongTagCanaryAtoms : List Atom :=
  [validationBodyVariableTagMismatchRule,
   lookupFoundAtom fixtureOwner wrongTaggedControl fixtureVariable
     { kind := .variable, occurrence := fixtureVariable },
   formulaValidationFaultContinuationRow
     fixtureValidationKey
     validationMalformedRequestRule]

private def wrongTagCanarySpace : Space := wrongTagCanaryAtoms.toFinset

private theorem wrongTagCanaryAtoms_nodup :
    wrongTagCanaryAtoms.Nodup := by decide +kernel

private theorem wrongTagCanary_fire_agreement :
    (cFireReflectiveSourceExecFact wrongTagCanaryAtoms
        validationBodyVariableTagMismatchDirective).toFinset =
      fireReflectiveSourceExecFact wrongTagCanarySpace
        validationBodyVariableTagMismatchDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    wrongTagCanaryAtoms validationBodyVariableTagMismatchDirective
    wrongTagCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationBodyVariableTagMismatchDirective.rule.tmpl).1
        (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      wrongTagCanaryAtoms validationBodyVariableTagMismatchDirective
      wrongTagCanaryAtoms_nodup)

theorem wrongTagCanary_faults_without_completion :
    formulaValidationFaultAtom fixtureOwner 0 fixtureValidationKey
        fixtureTypecode fixtureBody wrongTaggedFormulaAtom
        "body-tag-mismatch" ∈
      fireReflectiveSourceExecFact wrongTagCanarySpace
        validationBodyVariableTagMismatchDirective /\
    formulaValidationCompleteAtom fixtureOwner 0 fixtureValidationKey
        fixtureTypecode fixtureBody wrongTaggedFormulaAtom ∉
      fireReflectiveSourceExecFact wrongTagCanarySpace
        validationBodyVariableTagMismatchDirective := by
  rw [← wrongTagCanary_fire_agreement]
  decide +kernel

/-! The bounded trace is a target-side execution trace whose every transition
is classified by the OSLF-derived native type of the reflective execution
GSLT. -/
def startCanary_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 1 startCanaryAtoms
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 startCanaryAtoms).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 1
    startCanaryAtoms

section AxiomAudit

#print axioms formulaValidationRequestAtom_not_proofNeutral
#print axioms formulaValidationCompleteAtom_not_proofNeutral
#print axioms formulaValidationRules_extract_exact
#print axioms formulaValidationStaticRows_not_proofNeutral
#print axioms startCanary_selects_directive
#print axioms startCanary_inhabits_target_native_type
#print axioms startCanary_emits_exact_typecode_lookup
#print axioms activeFoundCanary_validates_exact_tagged_occurrence
#print axioms wrongTagCanary_faults_without_completion
#print axioms startCanary_oslf_native_trace

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
