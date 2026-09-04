import Mettapedia.Languages.Metamath.MM2SourceDVNameValidation

/-!
# Exact `$d` pair-plan validation in ordinary MM2

The source transformation retains a passive pair plan and a passive witness
for each pair.  This module validates those rows against the exact ordered
name list in the current `$d` statement.  Its nested scan uses suffix identity:
for each current name, an inner cursor walks the original name list until it
reaches the same located occurrence.  Every earlier occurrence must have one
pair row and one witness row at the same explicit successor position.

The pair may use either orientation.  Metamath disjointness is symmetric, and
the commit kernel publishes both lookup orientations, so validation does not
need an unrelated lexical string comparator.  The resulting derived-pair row
is verifier-owned.  The name validator supplies active-variable membership
and statement-local uniqueness; this module consumes those exact occurrence
markers and also emits an occurrence-rich validated-pair certificate.  That
certificate remains separate from endpoint-liveness authorization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVPairValidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceDVNameValidation
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

abbrev DVPair := String × String

/-! ## Controls and observations -/

def dvPairValidationRequestAtom (owner : Atom)
    (statementPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-request", owner,
      natAtom statementPosition]

def dvPairDerivedAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-derived", owner,
      natAtom statementPosition, natAtom pairPosition, stringPairAtom pair]

/-- An occurrence-rich pair certificate produced only after the passive pair
plan, its source witness, and both validated source-name occurrences agree. -/
def dvPairValidatedAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (left right : LocatedName) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validated", owner,
      natAtom statementPosition, natAtom pairPosition, stringPairAtom pair,
      locatedNameAtom left, locatedNameAtom right]

def dvPairValidationCompleteAtom (owner : Atom)
    (statementPosition count : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-complete", owner,
      natAtom statementPosition, natAtom count]

def dvPairValidationFaultAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (reason : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-fault", owner,
      natAtom statementPosition, natAtom pairPosition, .symbol reason]

def dvPairValidationControlAtom (owner : Atom)
    (statementPosition planCount : Nat) (fullNames outer inner : List LocatedName)
    (pairPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation", owner,
      natAtom statementPosition, natAtom planCount,
      listAtom locatedNameAtom fullNames, listAtom locatedNameAtom outer,
      listAtom locatedNameAtom inner, natAtom pairPosition]

@[simp] theorem dvPairValidationRequestAtom_not_proofNeutral (owner : Atom)
    (statementPosition : Nat) :
    isProofNeutralInitialAtom
      (dvPairValidationRequestAtom owner statementPosition) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-pair-validation-request"
    [owner, natAtom statementPosition] (by decide)

/-! ## Nested ordered scan -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-dv-pair-validation-start"
private def boundaryMoreLocation :=
  location "03" "mm-source-dv-pair-validation-boundary-more"
private def boundaryLastLocation :=
  location "03" "mm-source-dv-pair-validation-boundary-last"
private def duplicateLocation :=
  location "03" "mm-source-dv-pair-validation-duplicate-name"
private def directLocation :=
  location "04" "mm-source-dv-pair-validation-direct"
private def reverseLocation :=
  location "04" "mm-source-dv-pair-validation-reverse"
private def reloadLocation :=
  location "36" "mm-source-dv-pair-validation-reload"

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def locatedNameTemplate (stem : String) : Atom :=
  .expression
    [.symbol "mm-source-name", .var (stem ++ "-span"),
      .var (stem ++ "-name")]

private def firstNameTemplate : Atom := locatedNameTemplate "first"
private def secondNameTemplate : Atom := locatedNameTemplate "second"
private def currentNameTemplate : Atom := locatedNameTemplate "current"
private def duplicateCurrentNameTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "current-span", .var "earlier-name"]
private def earlierNameTemplate : Atom := locatedNameTemplate "earlier"
private def nextNameTemplate : Atom := locatedNameTemplate "next"

private def currentOuterTailTemplate : Atom :=
  .var "current-outer-tail"

private def fullAfterSecondTemplate : Atom :=
  .var "full-after-second-names"

private def nonemptyOuterTailTemplate : Atom :=
  .expression
    [.symbol "mm-cons", nextNameTemplate, .var "after-next-names"]

private def outerTemplate (tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", currentNameTemplate, tail]

private def innerEarlierTemplate : Atom :=
  .expression
    [.symbol "mm-cons", earlierNameTemplate, .var "inner-tail"]

private def innerAtCurrentTemplate (tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", currentNameTemplate, tail]

private def fullNamesTemplate : Atom :=
  .expression
    [.symbol "mm-cons", firstNameTemplate,
      .expression
        [.symbol "mm-cons", secondNameTemplate,
          fullAfterSecondTemplate]]

private def statementTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv", .var "declaration-site", fullNamesTemplate,
      .var "declaration-terminator"]

private def currentStatementTemplate : Atom :=
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
      .var "statement-position", statementTemplate, .var "plan-count"]

private def requestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-request",
      .var "source", .var "statement-position"]

private def namesCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validation-complete",
      .var "source", .var "statement-position"]

private def validationControlTemplate (outer inner pairCursor : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation", .var "source",
      .var "statement-position", .var "plan-count", fullNamesTemplate,
      outer, inner, pairCursor]

private def initialOuterTemplate : Atom :=
  .expression
    [.symbol "mm-cons", secondNameTemplate, fullAfterSecondTemplate]

private def initialControlTemplate : Atom :=
  validationControlTemplate initialOuterTemplate fullNamesTemplate
    (natAtom 0)

private def currentPairControlTemplate : Atom :=
  validationControlTemplate
    (outerTemplate currentOuterTailTemplate) innerEarlierTemplate
    (.var "pair-position")

private def duplicatePairControlTemplate : Atom :=
  validationControlTemplate
    (.expression
      [.symbol "mm-cons", duplicateCurrentNameTemplate,
        currentOuterTailTemplate])
    innerEarlierTemplate (.var "pair-position")

private def nextPairControlTemplate : Atom :=
  validationControlTemplate
    (outerTemplate currentOuterTailTemplate) (.var "inner-tail")
    (.var "next-pair-position")

private def boundaryMoreControlTemplate : Atom :=
  validationControlTemplate
    (outerTemplate nonemptyOuterTailTemplate)
    (innerAtCurrentTemplate nonemptyOuterTailTemplate)
    (.var "pair-position")

private def boundaryMoreNextControlTemplate : Atom :=
  validationControlTemplate nonemptyOuterTailTemplate fullNamesTemplate
    (.var "pair-position")

private def boundaryLastControlTemplate : Atom :=
  validationControlTemplate (outerTemplate nilTemplate)
    (innerAtCurrentTemplate nilTemplate) (.var "plan-count")

private def planFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-frontier", planOwnerTemplate,
      .var "plan-count"]

private def pairDirectTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "earlier-name", .var "current-name"]

private def pairReverseTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "current-name", .var "earlier-name"]

private def pairDuplicateTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "earlier-name", .var "earlier-name"]

private def pairPlanLinkTemplate (pair : Atom) : Atom :=
  .expression
    [.symbol "mm-linked-row", planOwnerTemplate,
      .symbol "source-dv-pair-plan", .var "pair-position",
      .var "next-pair-position", pair]

private def pairWitnessLinkTemplate (pair : Atom) : Atom :=
  .expression
    [.symbol "mm-linked-row", planOwnerTemplate,
      .symbol "source-dv-pair-witness", .var "pair-position",
      .var "next-pair-position",
      .expression
        [.symbol "mm-source-dv-pair-witness", .var "earlier-name",
          .var "current-name", pair]]

private def duplicateWitnessLinkTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", planOwnerTemplate,
      .symbol "source-dv-pair-witness", .var "pair-position",
      .var "next-pair-position",
      .expression
        [.symbol "mm-source-dv-pair-witness", .var "earlier-name",
          .var "earlier-name", pairDuplicateTemplate]]

private def validatedEarlierTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validated", .var "source",
      .var "statement-position", earlierNameTemplate]

private def validatedCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-name-validated", .var "source",
      .var "statement-position", currentNameTemplate]

private def derivedPairTemplate (pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-derived", .var "source",
      .var "statement-position", .var "pair-position", pair]

private def validatedPairTemplate (pair left right : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validated", .var "source",
      .var "statement-position", .var "pair-position", pair, left, right]

private def completeTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-complete",
      .var "source", .var "statement-position", .var "plan-count"]

private def duplicateFaultTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-fault",
      .var "source", .var "statement-position", .var "pair-position",
      .symbol "duplicate-name"]

private def reloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-dv-pair-validation", .var "source"]

def dvPairValidationReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-pair-validation", owner]

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

private def startSelf : Atom :=
  selfTemplate startLocation "dv-pair-validation-start"
private def startPatterns : List Atom :=
  [startSelf, requestTemplate, namesCompleteTemplate,
    currentStatementTemplate, planHeaderTemplate]
private def startSinks : List Sink :=
  [.add startSelf, .remove requestTemplate, .add initialControlTemplate,
    .add reloadTriggerTemplate]

def validationStartRule : Atom :=
  mkRule startLocation startPatterns startSinks

def validationStartDirective : SourceExecFact where
  atom := validationStartRule
  loc := startLocation
  rule :=
    { priority := 2
      name := "mm-source-dv-pair-validation-start"
      input := .compat (mkPattern startPatterns)
      guards := []
      tmpl := mkTemplate startSinks }

private def boundaryMoreSelf : Atom :=
  selfTemplate boundaryMoreLocation "dv-pair-validation-boundary-more"
private def boundaryMorePatterns : List Atom :=
  [boundaryMoreSelf, boundaryMoreControlTemplate]
private def boundaryMoreSinks : List Sink :=
  [.add boundaryMoreSelf, .remove boundaryMoreControlTemplate,
    .add boundaryMoreNextControlTemplate, .add reloadTriggerTemplate]

def validationBoundaryMoreRule : Atom :=
  mkRule boundaryMoreLocation boundaryMorePatterns boundaryMoreSinks

def validationBoundaryMoreDirective : SourceExecFact where
  atom := validationBoundaryMoreRule
  loc := boundaryMoreLocation
  rule :=
    { priority := 3
      name := "mm-source-dv-pair-validation-boundary-more"
      input := .compat (mkPattern boundaryMorePatterns)
      guards := []
      tmpl := mkTemplate boundaryMoreSinks }

private def boundaryLastSelf : Atom :=
  selfTemplate boundaryLastLocation "dv-pair-validation-boundary-last"
private def boundaryLastPatterns : List Atom :=
  [boundaryLastSelf, boundaryLastControlTemplate, planFrontierTemplate]
private def boundaryLastSinks : List Sink :=
  [.add boundaryLastSelf, .remove boundaryLastControlTemplate,
    .add completeTemplate]

def validationBoundaryLastRule : Atom :=
  mkRule boundaryLastLocation boundaryLastPatterns boundaryLastSinks

def validationBoundaryLastDirective : SourceExecFact where
  atom := validationBoundaryLastRule
  loc := boundaryLastLocation
  rule :=
    { priority := 3
      name := "mm-source-dv-pair-validation-boundary-last"
      input := .compat (mkPattern boundaryLastPatterns)
      guards := []
      tmpl := mkTemplate boundaryLastSinks }

private def duplicateSelf : Atom :=
  selfTemplate duplicateLocation "dv-pair-validation-duplicate-name"
private def duplicatePlanLinkTemplate : Atom :=
  pairPlanLinkTemplate pairDuplicateTemplate
private def duplicatePatterns : List Atom :=
  [duplicateSelf, duplicatePairControlTemplate, duplicatePlanLinkTemplate,
    duplicateWitnessLinkTemplate]
private def duplicateSinks : List Sink :=
  [.add duplicateSelf, .remove duplicatePairControlTemplate,
    .add duplicateFaultTemplate]

def validationDuplicateRule : Atom :=
  mkRule duplicateLocation duplicatePatterns duplicateSinks

def validationDuplicateDirective : SourceExecFact where
  atom := validationDuplicateRule
  loc := duplicateLocation
  rule :=
    { priority := 3
      name := "mm-source-dv-pair-validation-duplicate-name"
      input := .compat (mkPattern duplicatePatterns)
      guards := []
      tmpl := mkTemplate duplicateSinks }

private def pairStepRuleFor (loc : Atom) (stem : String)
    (pair left right : Atom) :
    Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let planLink := pairPlanLinkTemplate pair
  let witnessLink := pairWitnessLinkTemplate pair
  let patterns :=
    [self, currentPairControlTemplate, planLink, witnessLink,
      validatedEarlierTemplate, validatedCurrentTemplate]
  let sinks : List Sink :=
    [.add self, .remove currentPairControlTemplate,
      .add nextPairControlTemplate, .add (derivedPairTemplate pair),
      .add (validatedPairTemplate pair left right),
      .add reloadTriggerTemplate]
  let atom := mkRule loc patterns sinks
  (atom,
    { atom
      loc
      rule :=
        { priority := 4
          name := stem
          input := .compat (mkPattern patterns)
          guards := []
          tmpl := mkTemplate sinks } })

def validationDirectRule : Atom :=
  (pairStepRuleFor directLocation
    "mm-source-dv-pair-validation-direct" pairDirectTemplate
    earlierNameTemplate currentNameTemplate).1

def validationDirectDirective : SourceExecFact :=
  (pairStepRuleFor directLocation
    "mm-source-dv-pair-validation-direct" pairDirectTemplate
    earlierNameTemplate currentNameTemplate).2

def validationReverseRule : Atom :=
  (pairStepRuleFor reverseLocation
    "mm-source-dv-pair-validation-reverse" pairReverseTemplate
    currentNameTemplate earlierNameTemplate).1

def validationReverseDirective : SourceExecFact :=
  (pairStepRuleFor reverseLocation
    "mm-source-dv-pair-validation-reverse" pairReverseTemplate
    currentNameTemplate earlierNameTemplate).2

theorem extract_validationStartRule_exact :
    extractSupportedSourceExecFact validationStartRule =
      some validationStartDirective := by rfl

theorem extract_validationBoundaryMoreRule_exact :
    extractSupportedSourceExecFact validationBoundaryMoreRule =
      some validationBoundaryMoreDirective := by rfl

theorem extract_validationBoundaryLastRule_exact :
    extractSupportedSourceExecFact validationBoundaryLastRule =
      some validationBoundaryLastDirective := by rfl

theorem extract_validationDuplicateRule_exact :
    extractSupportedSourceExecFact validationDuplicateRule =
      some validationDuplicateDirective := by rfl

theorem extract_validationDirectRule_exact :
    extractSupportedSourceExecFact validationDirectRule =
      some validationDirectDirective := by rfl

theorem extract_validationReverseRule_exact :
    extractSupportedSourceExecFact validationReverseRule =
      some validationReverseDirective := by rfl

def validationStepRules : List Atom :=
  [validationBoundaryMoreRule, validationBoundaryLastRule,
    validationDuplicateRule,
    validationDirectRule, validationReverseRule]

def validationStepDirectives : List SourceExecFact :=
  [validationBoundaryMoreDirective, validationBoundaryLastDirective,
    validationDuplicateDirective,
    validationDirectDirective, validationReverseDirective]

def validationRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-pair-validation-rule", rule]

@[simp] theorem validationRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (validationRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-pair-validation-rule" [rule] (by decide)

def validationStaticRows : List Atom :=
  validationStepRules.map validationRuleRow

private def reloadSelf : Atom :=
  selfTemplate reloadLocation "dv-pair-validation-reload"
private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-rule",
      .var "dv-pair-validation-rule"]
private def reloadPatterns : List Atom :=
  [reloadSelf, reloadTriggerTemplate, reloadRuleTemplate]
private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove reloadTriggerTemplate,
    .add (.var "dv-pair-validation-rule")]

def validationReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def validationReloadDirective : SourceExecFact where
  atom := validationReloadRule
  loc := reloadLocation
  rule :=
    { priority := 36
      name := "mm-source-dv-pair-validation-reload"
      input := .compat (mkPattern reloadPatterns)
      guards := []
      tmpl := mkTemplate reloadSinks }

theorem extract_validationReloadRule_exact :
    extractSupportedSourceExecFact validationReloadRule =
      some validationReloadDirective := by rfl

def validationRules : List Atom :=
  validationStartRule :: validationStepRules ++ [validationReloadRule]

def validationDirectives : List SourceExecFact :=
  validationStartDirective :: validationStepDirectives ++
    [validationReloadDirective]

theorem validationRules_extract_exact :
    validationRules.filterMap extractSupportedSourceExecFact =
      validationDirectives := by
  rfl

/-! ## Full three-name trace and mutations -/

private def fixtureOwner : Atom := .symbol "dv-pair-validation-source"

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "dv-validation.mm", start, stop }

private def fixtureName (name : String) (start : Nat) : LocatedName :=
  { span := fixtureSpan start (start + 1), name }

private def xName : LocatedName := fixtureName "x" 3
private def yName : LocatedName := fixtureName "y" 5
private def zName : LocatedName := fixtureName "z" 7

private def fixtureStatement : RawStatement :=
  .djDecl (fixtureSpan 0 2) [xName, yName, zName] (fixtureSpan 9 11)

private def fixturePlan : SourceDVPairPlan :=
  { position := 0
    statement := fixtureStatement
    pairs := [("x", "y"), ("x", "z"), ("y", "z")] }

private theorem fixturePlan_witnesses_exact :
    fixturePlan.witnesses =
      [sourceDVPairWitness "x" "y", sourceDVPairWitness "x" "z",
        sourceDVPairWitness "y" "z"] := by
  simp [SourceDVPairPlan.witnesses, fixturePlan, fixtureStatement,
    sourceDVPairWitnesses, sourceDVPairWitnessesFrom, xName, yName, zName,
    fixtureName]

private def fixtureRequest : Atom :=
  dvPairValidationRequestAtom fixtureOwner 0

private def fixtureNameValidationRows : List Atom :=
  [dvNameValidationCompleteAtom fixtureOwner 0,
    dvNameValidatedAtom fixtureOwner 0 xName,
    dvNameValidatedAtom fixtureOwner 0 yName,
    dvNameValidatedAtom fixtureOwner 0 zName]

private def fixtureProgram : List Atom :=
  validationRules ++ validationStaticRows ++
    [fixtureRequest,
      sourceCurrentAtom fixtureOwner 0 1 fixtureStatement] ++
    fixtureNameValidationRows ++ fixturePlan.rows fixtureOwner ++
      fixturePlan.witnessRows fixtureOwner

theorem fixtureProgram_validates_all_pairs_in_order :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 48 fixtureProgram).1
    dvPairDerivedAtom fixtureOwner 0 0 ("x", "y") ∈ final ∧
      dvPairDerivedAtom fixtureOwner 0 1 ("x", "z") ∈ final ∧
      dvPairDerivedAtom fixtureOwner 0 2 ("y", "z") ∈ final ∧
      dvPairValidationCompleteAtom fixtureOwner 0 3 ∈ final ∧
      fixtureRequest ∉ final := by
  decide +kernel

theorem fixtureProgram_retains_exact_pair_occurrences :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 48 fixtureProgram).1
    dvPairValidatedAtom fixtureOwner 0 0 ("x", "y") xName yName ∈ final ∧
      dvPairValidatedAtom fixtureOwner 0 1 ("x", "z") xName zName ∈ final ∧
      dvPairValidatedAtom fixtureOwner 0 2 ("y", "z") yName zName ∈ final := by
  decide +kernel

def fixtureProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 48 fixtureProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 48 fixtureProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 48 fixtureProgram

private def badFirstWitness : SourceDVPairWitness :=
  { earlier := "x", current := "z", pair := ("x", "y") }

private def badWitnessProgram : List Atom :=
  validationRules ++ validationStaticRows ++
    [fixtureRequest,
      sourceCurrentAtom fixtureOwner 0 1 fixtureStatement] ++
    fixtureNameValidationRows ++ fixturePlan.rows fixtureOwner ++
    (sourceDVPairWitnessLinkAtom fixtureOwner 0 0 badFirstWitness ::
      (fixturePlan.witnessRows fixtureOwner).drop 1)

theorem badWitnessProgram_cannot_complete :
    dvPairValidationCompleteAtom fixtureOwner 0 3 ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 48 badWitnessProgram).1 := by
  decide +kernel

private def missingMiddlePairProgram : List Atom :=
  validationRules ++ validationStaticRows ++
    [fixtureRequest,
      sourceCurrentAtom fixtureOwner 0 1 fixtureStatement] ++
    fixtureNameValidationRows ++
    (fixturePlan.rows fixtureOwner).erase
      (sourceDVPairPlanLinkAtom fixtureOwner 0 1 ("x", "z")) ++
    fixturePlan.witnessRows fixtureOwner

theorem missingMiddlePairProgram_cannot_complete :
    dvPairValidationCompleteAtom fixtureOwner 0 3 ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 48
        missingMiddlePairProgram).1 := by
  decide +kernel

private def wrongCountHeader : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-header", fixtureOwner, natAtom 0,
      rawStatementAtom fixtureStatement, natAtom 2]

private def wrongCountProgram : List Atom :=
  validationRules ++ validationStaticRows ++
    [fixtureRequest,
      sourceCurrentAtom fixtureOwner 0 1 fixtureStatement,
      wrongCountHeader] ++ fixtureNameValidationRows ++
    (fixturePlan.rows fixtureOwner).drop 1 ++
      fixturePlan.witnessRows fixtureOwner

theorem wrongCountProgram_cannot_complete :
    dvPairValidationCompleteAtom fixtureOwner 0 2 ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 48 wrongCountProgram).1 := by
  decide +kernel

private def duplicateFirst : LocatedName := fixtureName "x" 13
private def duplicateSecond : LocatedName := fixtureName "x" 15
private def duplicatePair : DVPair := ("x", "x")
private def duplicateWitness : SourceDVPairWitness :=
  { earlier := "x", current := "x", pair := duplicatePair }
private def duplicateControl : Atom :=
  dvPairValidationControlAtom fixtureOwner 4 1
    [duplicateFirst, duplicateSecond] [duplicateSecond]
    [duplicateFirst, duplicateSecond] 0
private def duplicateCanaryAtoms : List Atom :=
  [validationDuplicateRule, duplicateControl,
    sourceDVPairPlanLinkAtom fixtureOwner 4 0 duplicatePair,
    sourceDVPairWitnessLinkAtom fixtureOwner 4 0 duplicateWitness]
private def duplicateCanarySpace : Space := duplicateCanaryAtoms.toFinset
private theorem duplicateCanaryAtoms_nodup : duplicateCanaryAtoms.Nodup := by
  decide +kernel
private theorem duplicateCanaryAtoms_supported :
    cSupportedSourceExecFacts duplicateCanaryAtoms =
      [validationDuplicateDirective] := by rfl
private theorem duplicateCanary_fire_agreement :
    (cFireReflectiveSourceExecFact duplicateCanaryAtoms
        validationDuplicateDirective).toFinset =
      fireReflectiveSourceExecFact duplicateCanarySpace
        validationDuplicateDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    duplicateCanaryAtoms validationDuplicateDirective
    duplicateCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      validationDuplicateDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      duplicateCanaryAtoms validationDuplicateDirective
      duplicateCanaryAtoms_nodup)

theorem duplicateCanary_emits_fault_not_derived_pair :
    dvPairValidationFaultAtom fixtureOwner 4 0 "duplicate-name" ∈
        fireReflectiveSourceExecFact duplicateCanarySpace
          validationDuplicateDirective ∧
      dvPairDerivedAtom fixtureOwner 4 0 duplicatePair ∉
        fireReflectiveSourceExecFact duplicateCanarySpace
          validationDuplicateDirective := by
  rw [← duplicateCanary_fire_agreement]
  decide +kernel

section AxiomAudit

#print axioms dvPairValidationRequestAtom_not_proofNeutral
#print axioms extract_validationStartRule_exact
#print axioms extract_validationBoundaryMoreRule_exact
#print axioms extract_validationBoundaryLastRule_exact
#print axioms extract_validationDuplicateRule_exact
#print axioms extract_validationDirectRule_exact
#print axioms extract_validationReverseRule_exact
#print axioms extract_validationReloadRule_exact
#print axioms validationRules_extract_exact
#print axioms validationRuleRow_not_proofNeutral
#print axioms fixtureProgram_validates_all_pairs_in_order
#print axioms fixtureProgram_retains_exact_pair_occurrences
#print axioms fixtureProgram_has_oslf_native_trace
#print axioms badWitnessProgram_cannot_complete
#print axioms missingMiddlePairProgram_cannot_complete
#print axioms wrongCountProgram_cannot_complete
#print axioms duplicateCanary_emits_fault_not_derived_pair

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVPairValidation
