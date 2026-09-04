import Mettapedia.Languages.Metamath.MM2SourceDVEndpointClassification

/-!
# Native `$d` declaration execution in ordinary MM2

This module composes the source-derived pair plan, active-name validation,
pair-plan validation, endpoint classification, occurrence lookup, and pair
commit protocols into one declaration transaction.

No durable disjoint-variable row is published until every source name and
every source-derived pair has been validated and every pair has received an
endpoint status.  The commit phase then walks the same exact pair-plan chain.
Each continuation is installed through the reload inventory of the subsystem
whose observation enables it; this keeps the ordered work queue from
consuming a future continuation before its premise exists.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVDeclaration

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceStateNativeTypes
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Semantic authority -/

/-- Native execution is licensed only by the accepted `$d` transition of the
authored source-state GSLT, classified through its OSLF-derived NTT. -/
theorem disjointDeclaration_inhabits_source_native_type
    {before after : SourceState} {names : List String}
    (declared : declareDisjoint? before names = some after) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      SourceStateGSLT.theory).satisfies before
      (sourceStateExactTargetNativeType after).pred := by
  exact declareDisjoint_inhabits_source_native_type declared

/-! ## Protected transaction observations -/

abbrev DVPair := String × String

def dvClassificationCompleteAtom (owner : Atom)
    (statementPosition pairCount : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-classification-complete", owner,
      natAtom statementPosition, natAtom pairCount]

def dvCommitReadyAtom (owner : Atom)
    (statementPosition pairCount : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-commit-ready", owner,
      natAtom statementPosition, natAtom pairCount]

def dvClassificationControlAtom (owner : Atom)
    (statementPosition pairCount pairPosition nextPairPosition : Nat)
    (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-classification", owner,
      natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      natAtom nextPairPosition, stringPairAtom pair]

def dvCleanupControlAtom (owner : Atom)
    (statementPosition pairCount : Nat) (names : List LocatedName) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-cleanup", owner,
      natAtom statementPosition, natAtom pairCount,
      listAtom locatedNameAtom names]

def dvCommitControlAtom (owner : Atom)
    (statementPosition pairCount pairPosition nextPairPosition : Nat)
    (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-commit", owner,
      natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      natAtom nextPairPosition, stringPairAtom pair]

/-! ## Ordinary MM2 templates -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-dv-declaration-start"
private def namesCompleteLocation :=
  location "04" "mm-source-dv-declaration-names-complete"
private def classificationStartLocation :=
  location "05" "mm-source-dv-classification-start"
private def classificationMoreLocation :=
  location "05" "mm-source-dv-classification-more"
private def classificationLastLocation :=
  location "05" "mm-source-dv-classification-last"
private def cleanupStartLocation :=
  location "06" "mm-source-dv-cleanup-start"
private def cleanupMoreLocation :=
  location "06" "mm-source-dv-cleanup-more"
private def cleanupLastLocation :=
  location "06" "mm-source-dv-cleanup-last"
private def commitStartLocation :=
  location "07" "mm-source-dv-commit-start"
private def commitMoreLocation :=
  location "07" "mm-source-dv-commit-more"
private def commitLastLocation :=
  location "07" "mm-source-dv-commit-last"
private def nameFaultLocation :=
  location "04" "mm-source-dv-name-fault"
private def pairFaultLocation :=
  location "05" "mm-source-dv-pair-fault"
private def reloadLocation :=
  location "37" "mm-source-dv-declaration-reload"

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def firstNameTemplate : Atom := locatedNameTemplate "first"
private def secondNameTemplate : Atom := locatedNameTemplate "second"
private def cleanupNameTemplate : Atom := locatedNameTemplate "cleanup"

private def namesTemplate : Atom :=
  .expression
    [.symbol "mm-cons", firstNameTemplate,
      .expression
        [.symbol "mm-cons", secondNameTemplate,
          .var "after-second-names"]]

private def statementTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv", .var "declaration-site", namesTemplate,
      .var "declaration-terminator"]

private def currentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source",
      .var "statement-position", .var "next-statement-position",
      statementTemplate, .var "dispatch-input", .var "dispatch-output"]

private def planOwnerTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-owner", .var "source",
      .var "statement-position"]

private def planHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-header", .var "source",
      .var "statement-position", statementTemplate, .var "pair-count"]

private def pairTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-pair", .var (stem ++ "-left"),
      .var (stem ++ "-right")]

private def currentPairTemplate : Atom := pairTemplate "current-pair"
private def nextPairTemplate : Atom := pairTemplate "next-pair"

private def planLinkTemplate (position next pair : Atom) : Atom :=
  .expression
    [.symbol "mm-linked-row", planOwnerTemplate,
      .symbol "source-dv-pair-plan", position, next, pair]

private def planFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-frontier", planOwnerTemplate,
      .var "pair-count"]

private def namesCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-complete",
      .var "source", .var "statement-position"]

private def nameValidatedTemplate (name : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validated", .var "source",
      .var "statement-position", name]

private def pairValidationCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-complete",
      .var "source", .var "statement-position", .var "pair-count"]

private def pairDerivedTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-derived", .var "source",
      .var "statement-position", position, pair]

private def pairValidatedTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validated", .var "source",
      .var "statement-position", position, pair,
      .var "validated-left", .var "validated-right"]

private def endpointStatusTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-status", .var "source",
      .var "statement-position", position, pair,
      .var "endpoint-status"]

private def endpointRequestTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-request", .var "source",
      .var "statement-position", .var "pair-count", position, pair]

private def classificationControlTemplate
    (position next pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-classification", .var "source",
      .var "statement-position", .var "pair-count", position, next, pair]

private def classificationCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-classification-complete",
      .var "source", .var "statement-position", .var "pair-count"]

private def cleanupControlTemplate (names : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-cleanup", .var "source",
      .var "statement-position", .var "pair-count", names]

private def cleanupInitialControlTemplate : Atom :=
  cleanupControlTemplate namesTemplate

private def cleanupMoreControlTemplate : Atom :=
  cleanupControlTemplate
    (.expression
      [.symbol "mm-cons", cleanupNameTemplate,
        .expression
          [.symbol "mm-cons", .var "cleanup-next",
            .var "cleanup-after-next"]])

private def cleanupMoreNextControlTemplate : Atom :=
  cleanupControlTemplate
    (.expression
      [.symbol "mm-cons", .var "cleanup-next",
        .var "cleanup-after-next"])

private def cleanupLastControlTemplate : Atom :=
  cleanupControlTemplate
    (.expression [.symbol "mm-cons", cleanupNameTemplate, nilTemplate])

private def commitReadyTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-commit-ready", .var "source",
      .var "statement-position", .var "pair-count"]

private def authorizationTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-authorized", .var "source",
      .var "statement-position", position, pair,
      .var "endpoint-status"]

private def occurrenceFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-frontier", .var "source",
      .var "occurrence-frontier"]

private def occurrenceLookupTemplate (authorization pair : Atom) :
    Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-lookup", .var "source",
      authorization, pair, natAtom 0, .var "occurrence-frontier"]

private def commitControlTemplate (position next pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-commit", .var "source",
      .var "statement-position", .var "pair-count", position, next, pair]

private def committedTemplate (position pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-committed", .var "source",
      .var "statement-position", position, pair]

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-reload",
      .var "source-verifier-reload-rule"]

def dvSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-reload", sourceVerifierReloadRule]

private def nextSourceControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source",
      .var "next-statement-position"]

private def statementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source",
      .var "statement-position", statementTemplate]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def nameValidationRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-request",
      .var "source", .var "statement-position"]

private def pairValidationRequestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-request",
      .var "source", .var "statement-position"]

private def endpointReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-dv-endpoint", .var "source"]

private def occurrenceLookupReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-dv-occurrence-lookup", .var "source"]

private def ownReloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-dv-declaration", .var "source"]

def dvDeclarationReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-declaration", owner]

private def rejectedTemplate (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source",
      .var "statement-position", statementTemplate, reason, evidence]

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

/-! ## Validation and classification phase -/

private def startSelf := selfTemplate startLocation "dv-declaration-start"
private def startPatterns : List Atom :=
  [startSelf, currentTemplate, planHeaderTemplate]
private def startSinks : List Sink :=
  [.remove startSelf, .add nameValidationRequestTemplate,
    .add MM2SourceDVNameValidation.validationStartRule]

def declarationStartRule : Atom := mkRule startLocation startPatterns startSinks
def declarationStartDirective : SourceExecFact :=
  mkDirective declarationStartRule startLocation 2
    "mm-source-dv-declaration-start" startPatterns startSinks

private def namesCompleteSelf :=
  selfTemplate namesCompleteLocation "dv-declaration-names-complete"
private def namesCompletePatterns : List Atom :=
  [namesCompleteSelf, namesCompleteTemplate]
private def namesCompleteSinks : List Sink :=
  [.remove namesCompleteSelf, .add pairValidationRequestTemplate,
    .add MM2SourceDVPairValidation.validationStartRule]

def namesCompleteRule : Atom :=
  mkRule namesCompleteLocation namesCompletePatterns namesCompleteSinks
def namesCompleteDirective : SourceExecFact :=
  mkDirective namesCompleteRule namesCompleteLocation 4
    "mm-source-dv-declaration-names-complete" namesCompletePatterns
    namesCompleteSinks

private def firstPlanLinkTemplate : Atom :=
  planLinkTemplate (natAtom 0) (.var "next-pair-position")
    currentPairTemplate
private def firstDerivedTemplate : Atom :=
  pairDerivedTemplate (natAtom 0) currentPairTemplate
private def firstValidatedTemplate : Atom :=
  pairValidatedTemplate (natAtom 0) currentPairTemplate
private def firstEndpointRequestTemplate : Atom :=
  endpointRequestTemplate (natAtom 0) currentPairTemplate
private def firstClassificationControlTemplate : Atom :=
  classificationControlTemplate (natAtom 0) (.var "next-pair-position")
    currentPairTemplate

private def classificationStartSelf :=
  selfTemplate classificationStartLocation "dv-classification-start"
private def classificationStartPatterns : List Atom :=
  [classificationStartSelf, pairValidationCompleteTemplate,
    firstPlanLinkTemplate, firstDerivedTemplate, firstValidatedTemplate]
private def classificationStartSinks : List Sink :=
  [.remove classificationStartSelf, .add firstEndpointRequestTemplate,
    .add firstClassificationControlTemplate,
    .add endpointReloadTemplate]

def classificationStartRule : Atom :=
  mkRule classificationStartLocation classificationStartPatterns
    classificationStartSinks
def classificationStartDirective : SourceExecFact :=
  mkDirective classificationStartRule classificationStartLocation 5
    "mm-source-dv-classification-start" classificationStartPatterns
    classificationStartSinks

private def currentStatusTemplate : Atom :=
  endpointStatusTemplate (.var "pair-position") currentPairTemplate
private def currentClassificationControlTemplate : Atom :=
  classificationControlTemplate (.var "pair-position")
    (.var "next-pair-position") currentPairTemplate
private def lastClassificationControlTemplate : Atom :=
  classificationControlTemplate (.var "pair-position")
    (.var "pair-count") currentPairTemplate
private def nextPlanLinkTemplate : Atom :=
  planLinkTemplate (.var "next-pair-position")
    (.var "after-next-pair-position") nextPairTemplate
private def nextDerivedTemplate : Atom :=
  pairDerivedTemplate (.var "next-pair-position") nextPairTemplate
private def nextValidatedTemplate : Atom :=
  pairValidatedTemplate (.var "next-pair-position") nextPairTemplate
private def nextEndpointRequestTemplate : Atom :=
  endpointRequestTemplate (.var "next-pair-position") nextPairTemplate
private def nextClassificationControlTemplate : Atom :=
  classificationControlTemplate (.var "next-pair-position")
    (.var "after-next-pair-position") nextPairTemplate

private def classificationMoreSelf :=
  selfTemplate classificationMoreLocation "dv-classification-more"
private def classificationMorePatterns : List Atom :=
  [classificationMoreSelf, currentClassificationControlTemplate,
    currentStatusTemplate, nextPlanLinkTemplate, nextDerivedTemplate,
    nextValidatedTemplate]
private def classificationMoreSinks : List Sink :=
  [.remove classificationMoreSelf,
    .remove currentClassificationControlTemplate,
    .add nextEndpointRequestTemplate,
    .add nextClassificationControlTemplate,
    .add endpointReloadTemplate]

def classificationMoreRule : Atom :=
  mkRule classificationMoreLocation classificationMorePatterns
    classificationMoreSinks
def classificationMoreDirective : SourceExecFact :=
  mkDirective classificationMoreRule classificationMoreLocation 5
    "mm-source-dv-classification-more" classificationMorePatterns
    classificationMoreSinks

private def classificationLastSelf :=
  selfTemplate classificationLastLocation "dv-classification-last"
private def classificationLastPatterns : List Atom :=
  [classificationLastSelf, lastClassificationControlTemplate,
    currentStatusTemplate, planFrontierTemplate]
private def classificationLastSinks : List Sink :=
  [.remove classificationLastSelf,
    .remove lastClassificationControlTemplate,
    .add classificationCompleteTemplate, .add ownReloadTriggerTemplate]

def classificationLastRule : Atom :=
  mkRule classificationLastLocation classificationLastPatterns
    classificationLastSinks
def classificationLastDirective : SourceExecFact :=
  mkDirective classificationLastRule classificationLastLocation 5
    "mm-source-dv-classification-last" classificationLastPatterns
    classificationLastSinks

/-! ## Receipt cleanup -/

private def cleanupStartSelf :=
  selfTemplate cleanupStartLocation "dv-cleanup-start"
private def cleanupStartPatterns : List Atom :=
  [cleanupStartSelf, classificationCompleteTemplate,
    pairValidationCompleteTemplate, namesCompleteTemplate, currentTemplate]
private def cleanupStartSinks : List Sink :=
  [.remove cleanupStartSelf, .remove namesCompleteTemplate,
    .add cleanupInitialControlTemplate, .add ownReloadTriggerTemplate]

def cleanupStartRule : Atom :=
  mkRule cleanupStartLocation cleanupStartPatterns cleanupStartSinks
def cleanupStartDirective : SourceExecFact :=
  mkDirective cleanupStartRule cleanupStartLocation 6
    "mm-source-dv-cleanup-start" cleanupStartPatterns cleanupStartSinks

private def cleanupMoreSelf :=
  selfTemplate cleanupMoreLocation "dv-cleanup-more"
private def cleanupMorePatterns : List Atom :=
  [cleanupMoreSelf, cleanupMoreControlTemplate,
    nameValidatedTemplate cleanupNameTemplate]
private def cleanupMoreSinks : List Sink :=
  [.remove cleanupMoreSelf, .remove cleanupMoreControlTemplate,
    .remove (nameValidatedTemplate cleanupNameTemplate),
    .add cleanupMoreNextControlTemplate, .add ownReloadTriggerTemplate]

def cleanupMoreRule : Atom :=
  mkRule cleanupMoreLocation cleanupMorePatterns cleanupMoreSinks
def cleanupMoreDirective : SourceExecFact :=
  mkDirective cleanupMoreRule cleanupMoreLocation 6
    "mm-source-dv-cleanup-more" cleanupMorePatterns cleanupMoreSinks

private def cleanupLastSelf :=
  selfTemplate cleanupLastLocation "dv-cleanup-last"
private def cleanupLastPatterns : List Atom :=
  [cleanupLastSelf, cleanupLastControlTemplate,
    nameValidatedTemplate cleanupNameTemplate]
private def cleanupLastSinks : List Sink :=
  [.remove cleanupLastSelf, .remove cleanupLastControlTemplate,
    .remove (nameValidatedTemplate cleanupNameTemplate),
    .add commitReadyTemplate, .add ownReloadTriggerTemplate]

def cleanupLastRule : Atom :=
  mkRule cleanupLastLocation cleanupLastPatterns cleanupLastSinks
def cleanupLastDirective : SourceExecFact :=
  mkDirective cleanupLastRule cleanupLastLocation 6
    "mm-source-dv-cleanup-last" cleanupLastPatterns cleanupLastSinks

/-! ## Source-derived commit walk -/

private def firstStatusTemplate : Atom :=
  endpointStatusTemplate (natAtom 0) currentPairTemplate
private def firstAuthorizationTemplate : Atom :=
  authorizationTemplate (natAtom 0) currentPairTemplate
private def firstLookupTemplate : Atom :=
  occurrenceLookupTemplate firstAuthorizationTemplate currentPairTemplate
private def firstCommitControlTemplate : Atom :=
  commitControlTemplate (natAtom 0) (.var "next-pair-position")
    currentPairTemplate

private def commitStartSelf :=
  selfTemplate commitStartLocation "dv-commit-start"
private def commitStartPatterns : List Atom :=
  [commitStartSelf, commitReadyTemplate, firstPlanLinkTemplate,
    firstDerivedTemplate, firstValidatedTemplate, firstStatusTemplate,
    occurrenceFrontierTemplate]
private def commitStartSinks : List Sink :=
  [.remove commitStartSelf, .remove commitReadyTemplate,
    .remove firstDerivedTemplate, .remove firstValidatedTemplate,
    .remove firstStatusTemplate, .add firstAuthorizationTemplate,
    .add firstLookupTemplate, .add firstCommitControlTemplate,
    .add occurrenceLookupReloadTemplate]

def commitStartRule : Atom :=
  mkRule commitStartLocation commitStartPatterns commitStartSinks
def commitStartDirective : SourceExecFact :=
  mkDirective commitStartRule commitStartLocation 7
    "mm-source-dv-commit-start" commitStartPatterns commitStartSinks

private def currentCommittedTemplate : Atom :=
  committedTemplate (.var "pair-position") currentPairTemplate
private def currentCommitControlTemplate : Atom :=
  commitControlTemplate (.var "pair-position")
    (.var "next-pair-position") currentPairTemplate
private def lastCommitControlTemplate : Atom :=
  commitControlTemplate (.var "pair-position")
    (.var "pair-count") currentPairTemplate
private def nextStatusTemplate : Atom :=
  endpointStatusTemplate (.var "next-pair-position") nextPairTemplate
private def nextAuthorizationTemplate : Atom :=
  authorizationTemplate (.var "next-pair-position") nextPairTemplate
private def nextLookupTemplate : Atom :=
  occurrenceLookupTemplate nextAuthorizationTemplate nextPairTemplate
private def nextCommitControlTemplate : Atom :=
  commitControlTemplate (.var "next-pair-position")
    (.var "after-next-pair-position") nextPairTemplate

private def commitMoreSelf := selfTemplate commitMoreLocation "dv-commit-more"
private def commitMorePatterns : List Atom :=
  [commitMoreSelf, currentCommitControlTemplate, currentCommittedTemplate,
    nextPlanLinkTemplate, nextDerivedTemplate, nextValidatedTemplate,
    nextStatusTemplate, occurrenceFrontierTemplate]
private def commitMoreSinks : List Sink :=
  [.remove commitMoreSelf, .remove currentCommitControlTemplate,
    .remove currentCommittedTemplate, .remove nextDerivedTemplate,
    .remove nextValidatedTemplate, .remove nextStatusTemplate,
    .add nextAuthorizationTemplate, .add nextLookupTemplate,
    .add nextCommitControlTemplate, .add occurrenceLookupReloadTemplate]

def commitMoreRule : Atom :=
  mkRule commitMoreLocation commitMorePatterns commitMoreSinks
def commitMoreDirective : SourceExecFact :=
  mkDirective commitMoreRule commitMoreLocation 7
    "mm-source-dv-commit-more" commitMorePatterns commitMoreSinks

private def commitLastSelf := selfTemplate commitLastLocation "dv-commit-last"
private def commitLastPatterns : List Atom :=
  [commitLastSelf, lastCommitControlTemplate, currentCommittedTemplate,
    planFrontierTemplate, classificationCompleteTemplate,
    pairValidationCompleteTemplate, currentTemplate,
    sourceReloadCaptureTemplate]
private def commitLastSinks : List Sink :=
  [.remove commitLastSelf, .remove lastCommitControlTemplate,
    .remove currentCommittedTemplate, .remove classificationCompleteTemplate,
    .remove pairValidationCompleteTemplate, .remove currentTemplate,
    .add nextSourceControlTemplate, .add statementAppliedTemplate,
    .add sourceReloadTemplate, .add (.var "source-verifier-reload-rule")]

def commitLastRule : Atom :=
  mkRule commitLastLocation commitLastPatterns commitLastSinks
def commitLastDirective : SourceExecFact :=
  mkDirective commitLastRule commitLastLocation 7
    "mm-source-dv-commit-last" commitLastPatterns commitLastSinks

/-! ## Fault translation -/

private def nameFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-fault", .var "source",
      .var "statement-position", .var "fault-reason"]

private def nameFaultSelf := selfTemplate nameFaultLocation "dv-name-fault"
private def nameFaultPatterns : List Atom :=
  [nameFaultSelf, nameFaultTemplate, currentTemplate]
private def nameFaultSinks : List Sink :=
  [.remove nameFaultSelf, .remove nameFaultTemplate, .remove currentTemplate,
    .add (rejectedTemplate (.symbol "invalid-dv-name")
      (.var "fault-reason"))]

def nameFaultRule : Atom :=
  mkRule nameFaultLocation nameFaultPatterns nameFaultSinks
def nameFaultDirective : SourceExecFact :=
  mkDirective nameFaultRule nameFaultLocation 4 "mm-source-dv-name-fault"
    nameFaultPatterns nameFaultSinks

private def pairFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-fault", .var "source",
      .var "statement-position", .var "fault-pair-position",
      .var "fault-reason"]

private def pairFaultSelf := selfTemplate pairFaultLocation "dv-pair-fault"
private def pairFaultPatterns : List Atom :=
  [pairFaultSelf, pairFaultTemplate, currentTemplate]
private def pairFaultSinks : List Sink :=
  [.remove pairFaultSelf, .remove pairFaultTemplate, .remove currentTemplate,
    .add (rejectedTemplate (.symbol "invalid-dv-pair")
      (.expression
        [.symbol "mm-source-dv-pair-fault-evidence",
          .var "fault-pair-position", .var "fault-reason"]))]

def pairFaultRule : Atom :=
  mkRule pairFaultLocation pairFaultPatterns pairFaultSinks
def pairFaultDirective : SourceExecFact :=
  mkDirective pairFaultRule pairFaultLocation 5 "mm-source-dv-pair-fault"
    pairFaultPatterns pairFaultSinks

/-! ## Reload inventories -/

def dvDeclarationOwnContinuationRules : List Atom :=
  [namesCompleteRule, classificationStartRule, classificationMoreRule,
    classificationLastRule, cleanupStartRule, cleanupMoreRule,
    cleanupLastRule, commitStartRule, commitMoreRule, commitLastRule,
    nameFaultRule, pairFaultRule]

def dvDeclarationRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-declaration-rule", rule]

def dvDeclarationOwnStaticRows : List Atom :=
  [cleanupStartRule, cleanupMoreRule, cleanupLastRule, commitStartRule,
    MM2SourceDVOccurrenceLookup.lookupReloadRule].map dvDeclarationRuleRow

private def reloadSelf := selfTemplate reloadLocation "dv-declaration-reload"
private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-declaration-rule",
      .var "dv-declaration-rule"]
private def reloadPatterns : List Atom :=
  [reloadSelf, ownReloadTriggerTemplate, reloadRuleTemplate]
private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove ownReloadTriggerTemplate,
    .add (.var "dv-declaration-rule")]

def dvDeclarationReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks
def dvDeclarationReloadDirective : SourceExecFact :=
  mkDirective dvDeclarationReloadRule reloadLocation 37
    "mm-source-dv-declaration-reload" reloadPatterns reloadSinks

def dvDeclarationOwnRules : List Atom :=
  declarationStartRule :: dvDeclarationOwnContinuationRules ++
    [dvDeclarationReloadRule]

def dvDeclarationOwnDirectives : List SourceExecFact :=
  [declarationStartDirective, namesCompleteDirective,
    classificationStartDirective, classificationMoreDirective,
    classificationLastDirective, cleanupStartDirective,
    cleanupMoreDirective, cleanupLastDirective, commitStartDirective,
    commitMoreDirective, commitLastDirective, nameFaultDirective,
    pairFaultDirective, dvDeclarationReloadDirective]

/-- Rules added to a verifier that already owns the generic object-lookup
engine. -/
def dvDeclarationExtensionRules : List Atom :=
  dvDeclarationOwnRules ++
    MM2SourceDVNameValidation.validationRules ++
    MM2SourceDVPairValidation.validationRules ++
    MM2SourceActiveFloatingLookup.activeFloatingRules ++
    MM2SourceDVEndpointClassification.endpointRules ++
    MM2SourceDVOccurrenceLookup.lookupRules ++
    MM2SourceDVPairCommit.dvPairCommitRules

def dvDeclarationExtensionDirectives : List SourceExecFact :=
  dvDeclarationOwnDirectives ++
    MM2SourceDVNameValidation.validationDirectives ++
    MM2SourceDVPairValidation.validationDirectives ++
    MM2SourceActiveFloatingLookup.activeFloatingDirectives ++
    MM2SourceDVEndpointClassification.endpointDirectives ++
    MM2SourceDVOccurrenceLookup.lookupDirectives ++
    MM2SourceDVPairCommit.dvPairCommitDirectives

/-- Standalone inventory, including the generic object-lookup engine. -/
def dvDeclarationRules : List Atom :=
  MM2SourceObjectLookup.lookupRules ++ dvDeclarationExtensionRules

def dvDeclarationDirectives : List SourceExecFact :=
  MM2SourceObjectLookup.lookupDirectives ++ dvDeclarationExtensionDirectives

/-- Static rows are deliberately registered on the reload bus whose result
enables each cross-subsystem continuation. -/
def dvDeclarationExtensionStaticRows : List Atom :=
  dvDeclarationOwnStaticRows ++
    MM2SourceDVNameValidation.validationStaticRows ++
    [MM2SourceDVNameValidation.validationRuleRow
        MM2SourceObjectLookup.objectLookupReloadRule,
      MM2SourceDVNameValidation.validationRuleRow
        MM2SourceDVPairValidation.validationReloadRule,
      MM2SourceDVNameValidation.validationRuleRow namesCompleteRule,
      MM2SourceDVNameValidation.validationRuleRow nameFaultRule] ++
    MM2SourceDVPairValidation.validationStaticRows ++
    [MM2SourceDVPairValidation.validationRuleRow
        MM2SourceDVEndpointClassification.endpointReloadRule,
      MM2SourceDVPairValidation.validationRuleRow classificationStartRule,
      MM2SourceDVPairValidation.validationRuleRow pairFaultRule] ++
    MM2SourceActiveFloatingLookup.activeFloatingStaticRows ++
    (MM2SourceDVEndpointClassification.endpointStepRules ++
      [classificationMoreRule, classificationLastRule,
        dvDeclarationReloadRule]).map
          MM2SourceActiveFloatingLookup.activeFloatingRuleRow ++
    [MM2SourceDVEndpointClassification.endpointRuleRow
        MM2SourceDVEndpointClassification.endpointStartRule,
      MM2SourceDVEndpointClassification.endpointRuleRow
        MM2SourceActiveFloatingLookup.activeFloatingReloadRule] ++
    MM2SourceDVOccurrenceLookup.lookupStaticRows ++
    MM2SourceDVPairCommit.dvPairCommitCoreRules.map
      MM2SourceDVOccurrenceLookup.lookupRuleRow ++
    [MM2SourceDVOccurrenceLookup.lookupRuleRow
        MM2SourceDVPairCommit.dvPairCommitReloadRule] ++
    [MM2SourceDVPairCommit.dvPairCommitRuleRow
        MM2SourceDVOccurrenceLookup.lookupReloadRule,
      MM2SourceDVPairCommit.dvPairCommitRuleRow commitMoreRule,
      MM2SourceDVPairCommit.dvPairCommitRuleRow commitLastRule,
      dvSourceReloadCaptureRow]

def dvDeclarationStaticRows : List Atom :=
  MM2SourceObjectLookup.objectLookupStaticRows ++
    dvDeclarationExtensionStaticRows

theorem nameValidationBus_restores_objectLookupReload :
    MM2SourceDVNameValidation.validationRuleRow
        MM2SourceObjectLookup.objectLookupReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem nameValidationBus_restores_pairValidationReload :
    MM2SourceDVNameValidation.validationRuleRow
        MM2SourceDVPairValidation.validationReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem pairValidationBus_restores_endpointReload :
    MM2SourceDVPairValidation.validationRuleRow
        MM2SourceDVEndpointClassification.endpointReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem endpointBus_restores_activeFloatingReload :
    MM2SourceDVEndpointClassification.endpointRuleRow
        MM2SourceActiveFloatingLookup.activeFloatingReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem endpointBus_restores_endpointStart :
    MM2SourceDVEndpointClassification.endpointRuleRow
        MM2SourceDVEndpointClassification.endpointStartRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem activeFloatingBus_restores_endpointStep
    (rule : Atom)
    (member : rule ∈ MM2SourceDVEndpointClassification.endpointStepRules) :
    MM2SourceActiveFloatingLookup.activeFloatingRuleRow rule ∈
      dvDeclarationExtensionStaticRows := by
  have inMapped :
      MM2SourceActiveFloatingLookup.activeFloatingRuleRow rule ∈
        MM2SourceDVEndpointClassification.endpointStepRules.map
          MM2SourceActiveFloatingLookup.activeFloatingRuleRow :=
    List.mem_map_of_mem member
  simp [dvDeclarationExtensionStaticRows, inMapped]

theorem activeFloatingBus_restores_classificationMore :
    MM2SourceActiveFloatingLookup.activeFloatingRuleRow
        classificationMoreRule ∈ dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem activeFloatingBus_restores_classificationLast :
    MM2SourceActiveFloatingLookup.activeFloatingRuleRow
        classificationLastRule ∈ dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem activeFloatingBus_restores_declarationReload :
    MM2SourceActiveFloatingLookup.activeFloatingRuleRow
        dvDeclarationReloadRule ∈ dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem declarationBus_restores_occurrenceLookupReload :
    dvDeclarationRuleRow MM2SourceDVOccurrenceLookup.lookupReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows, dvDeclarationOwnStaticRows]

theorem occurrenceBus_restores_pairCommitCore
    (rule : Atom)
    (member : rule ∈ MM2SourceDVPairCommit.dvPairCommitCoreRules) :
    MM2SourceDVOccurrenceLookup.lookupRuleRow rule ∈
      dvDeclarationExtensionStaticRows := by
  have inMapped :
      MM2SourceDVOccurrenceLookup.lookupRuleRow rule ∈
        MM2SourceDVPairCommit.dvPairCommitCoreRules.map
          MM2SourceDVOccurrenceLookup.lookupRuleRow :=
    List.mem_map_of_mem member
  simp [dvDeclarationExtensionStaticRows, inMapped]

theorem occurrenceBus_restores_pairCommitReload :
    MM2SourceDVOccurrenceLookup.lookupRuleRow
        MM2SourceDVPairCommit.dvPairCommitReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

theorem pairCommitBus_restores_occurrenceLookupReload :
    MM2SourceDVPairCommit.dvPairCommitRuleRow
        MM2SourceDVOccurrenceLookup.lookupReloadRule ∈
      dvDeclarationExtensionStaticRows := by
  simp [dvDeclarationExtensionStaticRows]

/-! ## Exact rule extraction -/

theorem extract_declarationStartRule_exact :
    extractSupportedSourceExecFact declarationStartRule =
      some declarationStartDirective := by rfl
theorem extract_namesCompleteRule_exact :
    extractSupportedSourceExecFact namesCompleteRule =
      some namesCompleteDirective := by rfl
theorem extract_classificationStartRule_exact :
    extractSupportedSourceExecFact classificationStartRule =
      some classificationStartDirective := by rfl
theorem extract_classificationMoreRule_exact :
    extractSupportedSourceExecFact classificationMoreRule =
      some classificationMoreDirective := by rfl
theorem extract_classificationLastRule_exact :
    extractSupportedSourceExecFact classificationLastRule =
      some classificationLastDirective := by rfl
theorem extract_cleanupStartRule_exact :
    extractSupportedSourceExecFact cleanupStartRule =
      some cleanupStartDirective := by rfl
theorem extract_cleanupMoreRule_exact :
    extractSupportedSourceExecFact cleanupMoreRule =
      some cleanupMoreDirective := by rfl
theorem extract_cleanupLastRule_exact :
    extractSupportedSourceExecFact cleanupLastRule =
      some cleanupLastDirective := by rfl
theorem extract_commitStartRule_exact :
    extractSupportedSourceExecFact commitStartRule =
      some commitStartDirective := by rfl
theorem extract_commitMoreRule_exact :
    extractSupportedSourceExecFact commitMoreRule =
      some commitMoreDirective := by rfl
theorem extract_commitLastRule_exact :
    extractSupportedSourceExecFact commitLastRule =
      some commitLastDirective := by rfl
theorem extract_nameFaultRule_exact :
    extractSupportedSourceExecFact nameFaultRule =
      some nameFaultDirective := by rfl
theorem extract_pairFaultRule_exact :
    extractSupportedSourceExecFact pairFaultRule =
      some pairFaultDirective := by rfl
theorem extract_dvDeclarationReloadRule_exact :
    extractSupportedSourceExecFact dvDeclarationReloadRule =
      some dvDeclarationReloadDirective := by rfl

theorem dvDeclarationRules_extract_exact :
    dvDeclarationRules.filterMap extractSupportedSourceExecFact =
      dvDeclarationDirectives := by
  rfl

@[simp] theorem dvSourceReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom dvSourceReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-reload" [sourceVerifierReloadRule] (by decide)

/-! ## Small positive and negative controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "dv-declaration.mm", start, stop }
private def xName : LocatedName :=
  { span := fixtureSpan 3 4, name := "x" }
private def yName : LocatedName :=
  { span := fixtureSpan 5 6, name := "y" }
private def fixtureStatement : RawStatement :=
  .djDecl (fixtureSpan 0 2) [xName, yName] (fixtureSpan 7 9)
private def fixturePlan : SourceDVPairPlan :=
  { position := 0
    statement := fixtureStatement
    pairs := [("x", "y")] }
private def fixtureOwner : Atom := .symbol "dv-declaration-source"
private def fixtureCurrent : Atom :=
  sourceCurrentAtom fixtureOwner 0 1 fixtureStatement

private def startCanaryAtoms : List Atom :=
  [declarationStartRule, fixtureCurrent,
    sourceDVPairPlanHeaderAtom fixtureOwner fixturePlan]
private def startCanarySpace : Space := startCanaryAtoms.toFinset
private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel
private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms =
      [declarationStartDirective] := by rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some declarationStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms declarationStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          declarationStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

theorem startCanary_emits_validation_without_consuming_current :
    let final :=
      cFireReflectiveSourceExecFact startCanaryAtoms declarationStartDirective
    MM2SourceDVNameValidation.dvNameValidationRequestAtom fixtureOwner 0 ∈
        final /\
      fixtureCurrent ∈ final := by
  decide +kernel

private def wrongPlan : SourceDVPairPlan :=
  { position := 0
    statement := .djDecl (fixtureSpan 0 2) [yName, xName] (fixtureSpan 7 9)
    pairs := [("x", "y")] }

theorem startRule_rejects_mismatched_source_plan :
    (cmatchInputSpec []
      [declarationStartRule, fixtureCurrent,
        sourceDVPairPlanHeaderAtom fixtureOwner wrongPlan]
      declarationStartDirective.rule.input).isEmpty = true := by
  decide +kernel

private def commitNotReadyAtoms : List Atom :=
  [commitStartRule,
    sourceDVPairPlanLinkAtom fixtureOwner 0 0 ("x", "y"),
    MM2SourceDVPairValidation.dvPairDerivedAtom fixtureOwner 0 0 ("x", "y"),
    MM2SourceDVPairValidation.dvPairValidatedAtom fixtureOwner 0 0
      ("x", "y") xName yName,
    MM2SourceDVEndpointClassification.dvEndpointClassificationAtom
      fixtureOwner 0 0 ("x", "y") .live,
    MM2SourceDVOccurrenceLookup.dvOccurrenceFrontierAtom fixtureOwner 0]

theorem commitRule_rejects_without_statement_wide_readiness :
    (cmatchInputSpec [] commitNotReadyAtoms
      commitStartDirective.rule.input).isEmpty = true := by
  decide +kernel

section AxiomAudit

#print axioms disjointDeclaration_inhabits_source_native_type
#print axioms extract_declarationStartRule_exact
#print axioms extract_namesCompleteRule_exact
#print axioms extract_classificationStartRule_exact
#print axioms extract_classificationMoreRule_exact
#print axioms extract_classificationLastRule_exact
#print axioms extract_cleanupStartRule_exact
#print axioms extract_cleanupMoreRule_exact
#print axioms extract_cleanupLastRule_exact
#print axioms extract_commitStartRule_exact
#print axioms extract_commitMoreRule_exact
#print axioms extract_commitLastRule_exact
#print axioms extract_nameFaultRule_exact
#print axioms extract_pairFaultRule_exact
#print axioms extract_dvDeclarationReloadRule_exact
#print axioms dvDeclarationRules_extract_exact
#print axioms dvSourceReloadCaptureRow_not_proofNeutral
#print axioms nameValidationBus_restores_objectLookupReload
#print axioms nameValidationBus_restores_pairValidationReload
#print axioms pairValidationBus_restores_endpointReload
#print axioms endpointBus_restores_activeFloatingReload
#print axioms endpointBus_restores_endpointStart
#print axioms activeFloatingBus_restores_endpointStep
#print axioms activeFloatingBus_restores_classificationMore
#print axioms activeFloatingBus_restores_classificationLast
#print axioms activeFloatingBus_restores_declarationReload
#print axioms declarationBus_restores_occurrenceLookupReload
#print axioms occurrenceBus_restores_pairCommitCore
#print axioms occurrenceBus_restores_pairCommitReload
#print axioms pairCommitBus_restores_occurrenceLookupReload
#print axioms startCanary_inhabits_target_native_type
#print axioms startCanary_emits_validation_without_consuming_current
#print axioms startRule_rejects_mismatched_source_plan
#print axioms commitRule_rejects_without_statement_wide_readiness

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVDeclaration
