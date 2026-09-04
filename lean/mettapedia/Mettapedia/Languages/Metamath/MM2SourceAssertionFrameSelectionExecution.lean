import Mettapedia.Languages.Metamath.MM2SourceAssertionCertificateExecution

/-!
# Native assertion-frame selection execution

This module consumes source-derived certificate evidence and checks the
candidate assertion frame against the active source snapshots.  Essential
hypotheses are synchronized directly.  Floating hypotheses are retained
exactly when their variable occurs in the checked certificate.  Active
distinct-variable occurrences are retained exactly when both endpoints occur
in that certificate.

All membership decisions run through the shared ordinary-MM2 finite-list
machine.  Source order and repeated active `$d` occurrences are preserved.
The terminal row remains private; assertion runtime publication is a later
transaction stage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionFrameSelectionExecution

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceAssertionCertificateExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrame
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Typed finite comparison -/

structure AssertionFrameSelectionEvidence where
  context : AssertionFrameContext
deriving DecidableEq

def assertionFrameSelectionEvidenceAtom (owner : Atom)
    (evidence : AssertionFrameSelectionEvidence) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-valid", owner,
      assertionFrameContextAtom evidence.context]

def decodeAssertionFrameSelectionEvidenceAtom (owner : Atom) :
    Atom → Option AssertionFrameSelectionEvidence
  | .expression [.symbol tag, actualOwner, encodedContext] => do
      guard (tag == "mm-internal-source-assertion-frame-valid")
      guard (actualOwner == owner)
      let context <- decodeAssertionFrameContextAtom encodedContext
      pure { context }
  | _ => none

@[simp] theorem decodeAssertionFrameSelectionEvidenceAtom_encoded
    (owner : Atom) (evidence : AssertionFrameSelectionEvidence) :
    decodeAssertionFrameSelectionEvidenceAtom owner
        (assertionFrameSelectionEvidenceAtom owner evidence) =
      some evidence := by
  cases evidence
  simp [decodeAssertionFrameSelectionEvidenceAtom,
    assertionFrameSelectionEvidenceAtom]

theorem assertionFrameSelectionEvidenceAtom_injective (owner : Atom) :
    Function.Injective (assertionFrameSelectionEvidenceAtom owner) := by
  intro left right equal
  have decoded :=
    congrArg (decodeAssertionFrameSelectionEvidenceAtom owner) equal
  simpa using decoded

/-- Pure reference comparison.  It consumes no target artifact and does not
interpret the private terminal tag as authority. -/
def selectAssertionFrame?
    (certificateEvidence : AssertionCertificateEvidence) :
    Option AssertionFrameSelectionEvidence :=
  if assertionFrameChecksSnapshot
      certificateEvidence.context.certificate
      certificateEvidence.activeHypotheses
      certificateEvidence.activeDistinctVariables
      certificateEvidence.context.assertion then
    some { context := certificateEvidence.context }
  else
    none

theorem selectAssertionFrame?_eq_some_iff
    (certificateEvidence : AssertionCertificateEvidence)
    (selectionEvidence : AssertionFrameSelectionEvidence) :
    selectAssertionFrame? certificateEvidence = some selectionEvidence ↔
      assertionFrameChecksSnapshot
          certificateEvidence.context.certificate
          certificateEvidence.activeHypotheses
          certificateEvidence.activeDistinctVariables
          certificateEvidence.context.assertion = true ∧
        selectionEvidence.context = certificateEvidence.context := by
  unfold selectAssertionFrame?
  split
  next checkTrue =>
    constructor
    · intro selected
      have recordEq :
          ({ context := certificateEvidence.context } :
            AssertionFrameSelectionEvidence) = selectionEvidence :=
        Option.some.inj selected
      exact
        ⟨checkTrue,
          (congrArg AssertionFrameSelectionEvidence.context recordEq).symm⟩
    · rintro ⟨_, contextEq⟩
      cases selectionEvidence with
      | mk selectionContext =>
          change selectionContext = certificateEvidence.context at contextEq
          cases contextEq
          rfl
  next checkFalse =>
    constructor
    · intro impossible
      contradiction
    · rintro ⟨checkTrue, _⟩
      exact absurd checkTrue (by simpa using checkFalse)

/-! ## Ordinary-MM2 templates -/

private def nilTemplate : Atom := .expression [.symbol "mm-nil"]

private def consTemplate (head tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", head, tail]

private def location (name : String) : Atom :=
  .expression [.symbol "08", .symbol name]

private def reloadLocation : Atom :=
  .expression [.symbol "37", .symbol "mm-source-assertion-frame-selection-reload"]

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

private def mkDirective (atom loc : Atom) (name : String)
    (patterns : List Atom) (sinks : List Sink) : SourceExecFact :=
  { atom
    loc
    rule :=
      { priority := 8
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def selectionReloadRuleCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-selection-reloader",
      .var "assertion-frame-selection-reload-rule"]

private def rulePair (name stem : String) (patterns : List Atom)
    (sinks : List Sink) : Atom × SourceExecFact :=
  let loc := location name
  let self := selfTemplate loc stem
  let allPatterns := self :: selectionReloadRuleCaptureTemplate :: patterns
  let allSinks :=
    .add (.var "assertion-frame-selection-reload-rule") :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc name allPatterns allSinks)

/-! ## Source-bound shared fields -/

private def formulaShapeTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "selection-typecode",
      .var "selection-formula-body"]

private def frameShapeTemplate : Atom :=
  .expression
    [.symbol "mm-frame", .var "selection-candidate-distinct",
      .var "selection-candidate-labels"]

private def assertionShapeTemplate : Atom :=
  .expression
    [.symbol "mm-assertion", .var "selection-assertion-label",
      formulaShapeTemplate, frameShapeTemplate,
      .var "selection-candidate-hypotheses"]

private def contextShapeTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context",
      .var "selection-position", .var "selection-next-position",
      .var "selection-statement",
      .var "selection-assertion-position",
      .var "selection-next-assertion-position",
      .var "selection-mandatory-variables", assertionShapeTemplate]

private def certificateEvidenceTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-valid",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences"]

private def hypothesisControlTemplate
    (remaining candidateHypotheses candidateLabels : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-select-hypotheses",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences", remaining, candidateHypotheses,
      candidateLabels]

private def distinctControlTemplate
    (remaining candidateDistinct : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-select-distinct",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences", remaining, candidateDistinct]

private def floatingHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-floating", .var "selection-floating-label",
      .var "selection-floating-typecode",
      .var "selection-floating-variable"]

private def essentialHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-essential", .var "selection-essential-label",
      .var "selection-essential-formula"]

private def pairTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "selection-distinct-left",
      .var "selection-distinct-right"]

private def reloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-assertion-frame-selection",
      .var "selection-source"]

def assertionFrameSelectionReloadTriggerAtom (owner : Atom) : Atom :=
  assertionPhaseReloadTriggerAtom "frame-selection" owner

def assertionPublicationReloadCapabilityRow (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-publication-reloader", rule]

private def membershipReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-list-membership", .var "selection-source"]

private def membershipReloadRuleCaptureTemplate : Atom :=
  membershipReloadCapabilityRow (.var "membership-reload-rule")

private def membershipReturnTemplate (ticket : Atom) : Atom :=
  membershipReturnCapabilityRow (.var "selection-source") ticket
    (.var "assertion-frame-selection-reload-rule") reloadTriggerTemplate

private def membershipRequestTemplate
    (ticket target remaining : Atom) : Atom :=
  membershipRequestRawAtom (.var "selection-source") ticket target
    nilTemplate remaining

private def membershipFoundTemplate (ticket target : Atom) : Atom :=
  membershipFoundRawAtom (.var "selection-source") ticket target
    (.var "selection-membership-visited")
    (.var "selection-membership-remaining")

private def membershipMissingTemplate (ticket target : Atom) : Atom :=
  membershipMissingRawAtom (.var "selection-source") ticket target
    (.var "selection-membership-visited")

private def validTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-valid",
      .var "selection-source", contextShapeTemplate]

/-! ## Hypothesis synchronization -/

private def startPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-start"
    "assertion-frame-selection-start" [certificateEvidenceTemplate]
    [.remove certificateEvidenceTemplate,
      .add (hypothesisControlTemplate
        (.var "selection-all-hypotheses")
        (.var "selection-candidate-hypotheses")
        (.var "selection-candidate-labels")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionStartRule : Atom := startPair.1
def assertionFrameSelectionStartDirective : SourceExecFact := startPair.2

private def essentialPair : Atom × SourceExecFact :=
  let control :=
    hypothesisControlTemplate
      (consTemplate essentialHypothesisTemplate
        (.var "selection-hypothesis-tail"))
      (consTemplate essentialHypothesisTemplate
        (.var "selection-candidate-hypothesis-tail"))
      (consTemplate (.var "selection-essential-label")
        (.var "selection-candidate-label-tail"))
  rulePair "mm-source-assertion-frame-selection-essential"
    "assertion-frame-selection-essential"
    [control]
    [.remove control,
      .add (hypothesisControlTemplate
        (.var "selection-hypothesis-tail")
        (.var "selection-candidate-hypothesis-tail")
        (.var "selection-candidate-label-tail")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionEssentialRule : Atom := essentialPair.1
def assertionFrameSelectionEssentialDirective : SourceExecFact := essentialPair.2

private def floatingTicketTemplate
    (remaining candidateHypotheses candidateLabels : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-floating-ticket",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences", remaining, candidateHypotheses,
      candidateLabels, floatingHypothesisTemplate]

private def currentFloatingTicketTemplate : Atom :=
  floatingTicketTemplate (.var "selection-hypothesis-tail")
    (.var "selection-candidate-hypothesis-remaining")
    (.var "selection-candidate-label-remaining")

private def floatingFoundTicketTemplate : Atom :=
  floatingTicketTemplate (.var "selection-hypothesis-tail")
    (consTemplate floatingHypothesisTemplate
      (.var "selection-candidate-hypothesis-tail"))
    (consTemplate (.var "selection-floating-label")
      (.var "selection-candidate-label-tail"))

private def floatingLaunchPair : Atom × SourceExecFact :=
  let control :=
    hypothesisControlTemplate
      (consTemplate floatingHypothesisTemplate
        (.var "selection-hypothesis-tail"))
      (.var "selection-candidate-hypothesis-remaining")
      (.var "selection-candidate-label-remaining")
  rulePair "mm-source-assertion-frame-selection-floating-launch"
    "assertion-frame-selection-floating-launch"
    [control, membershipReloadRuleCaptureTemplate]
    [.remove control,
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentFloatingTicketTemplate
        (.var "selection-floating-variable")
        (.var "selection-mandatory-variables")),
      .add (membershipReturnTemplate currentFloatingTicketTemplate),
      .add membershipReloadTemplate]

def assertionFrameSelectionFloatingLaunchRule : Atom := floatingLaunchPair.1
def assertionFrameSelectionFloatingLaunchDirective : SourceExecFact :=
  floatingLaunchPair.2

private def floatingFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-floating-found"
    "assertion-frame-selection-floating-found"
    [membershipFoundTemplate floatingFoundTicketTemplate
      (.var "selection-floating-variable")]
    [.remove (membershipFoundTemplate floatingFoundTicketTemplate
      (.var "selection-floating-variable")),
      .add (hypothesisControlTemplate
        (.var "selection-hypothesis-tail")
        (.var "selection-candidate-hypothesis-tail")
        (.var "selection-candidate-label-tail")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionFloatingFoundRule : Atom := floatingFoundPair.1
def assertionFrameSelectionFloatingFoundDirective : SourceExecFact :=
  floatingFoundPair.2

private def floatingMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-floating-missing"
    "assertion-frame-selection-floating-missing"
    [membershipMissingTemplate currentFloatingTicketTemplate
      (.var "selection-floating-variable")]
    [.remove (membershipMissingTemplate currentFloatingTicketTemplate
      (.var "selection-floating-variable")),
      .add (hypothesisControlTemplate
        (.var "selection-hypothesis-tail")
        (.var "selection-candidate-hypothesis-remaining")
        (.var "selection-candidate-label-remaining")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionFloatingMissingRule : Atom := floatingMissingPair.1
def assertionFrameSelectionFloatingMissingDirective : SourceExecFact :=
  floatingMissingPair.2

private def hypothesesDonePair : Atom × SourceExecFact :=
  let control := hypothesisControlTemplate nilTemplate nilTemplate nilTemplate
  rulePair "mm-source-assertion-frame-selection-hypotheses-done"
    "assertion-frame-selection-hypotheses-done"
    [control]
    [.remove control,
      .add (distinctControlTemplate (.var "selection-all-distinct")
        (.var "selection-candidate-distinct")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionHypothesesDoneRule : Atom := hypothesesDonePair.1
def assertionFrameSelectionHypothesesDoneDirective : SourceExecFact :=
  hypothesesDonePair.2

/-! ## Distinct-variable synchronization -/

private def distinctLeftTicketTemplate
    (remaining candidateDistinct : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-distinct-left-ticket",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences", remaining, candidateDistinct,
      pairTemplate]

private def currentDistinctLeftTicketTemplate : Atom :=
  distinctLeftTicketTemplate (.var "selection-distinct-tail")
    (.var "selection-candidate-distinct-remaining")

private def distinctRightTicketTemplate
    (remaining candidateDistinct : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-distinct-right-ticket",
      .var "selection-source", contextShapeTemplate,
      .var "selection-all-hypotheses", .var "selection-all-distinct",
      .var "selection-occurrences", remaining, candidateDistinct,
      pairTemplate]

private def currentDistinctRightTicketTemplate : Atom :=
  distinctRightTicketTemplate (.var "selection-distinct-tail")
    (.var "selection-candidate-distinct-remaining")

private def distinctRightFoundTicketTemplate : Atom :=
  distinctRightTicketTemplate (.var "selection-distinct-tail")
    (consTemplate pairTemplate (.var "selection-candidate-distinct-tail"))

private def distinctLeftLaunchPair : Atom × SourceExecFact :=
  let control :=
    distinctControlTemplate
      (consTemplate pairTemplate (.var "selection-distinct-tail"))
      (.var "selection-candidate-distinct-remaining")
  rulePair "mm-source-assertion-frame-selection-distinct-left-launch"
    "assertion-frame-selection-distinct-left-launch"
    [control, membershipReloadRuleCaptureTemplate]
    [.remove control,
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentDistinctLeftTicketTemplate
        (.var "selection-distinct-left")
        (.var "selection-mandatory-variables")),
      .add (membershipReturnTemplate currentDistinctLeftTicketTemplate),
      .add membershipReloadTemplate]

def assertionFrameSelectionDistinctLeftLaunchRule : Atom :=
  distinctLeftLaunchPair.1
def assertionFrameSelectionDistinctLeftLaunchDirective : SourceExecFact :=
  distinctLeftLaunchPair.2

private def distinctLeftFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-distinct-left-found"
    "assertion-frame-selection-distinct-left-found"
    [membershipFoundTemplate currentDistinctLeftTicketTemplate
      (.var "selection-distinct-left"),
      membershipReloadRuleCaptureTemplate]
    [.remove (membershipFoundTemplate currentDistinctLeftTicketTemplate
      (.var "selection-distinct-left")),
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentDistinctRightTicketTemplate
        (.var "selection-distinct-right")
        (.var "selection-mandatory-variables")),
      .add (membershipReturnTemplate currentDistinctRightTicketTemplate),
      .add membershipReloadTemplate]

def assertionFrameSelectionDistinctLeftFoundRule : Atom :=
  distinctLeftFoundPair.1
def assertionFrameSelectionDistinctLeftFoundDirective : SourceExecFact :=
  distinctLeftFoundPair.2

private def distinctLeftMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-distinct-left-missing"
    "assertion-frame-selection-distinct-left-missing"
    [membershipMissingTemplate currentDistinctLeftTicketTemplate
      (.var "selection-distinct-left")]
    [.remove (membershipMissingTemplate currentDistinctLeftTicketTemplate
      (.var "selection-distinct-left")),
      .add (distinctControlTemplate (.var "selection-distinct-tail")
        (.var "selection-candidate-distinct-remaining")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionDistinctLeftMissingRule : Atom :=
  distinctLeftMissingPair.1
def assertionFrameSelectionDistinctLeftMissingDirective : SourceExecFact :=
  distinctLeftMissingPair.2

private def distinctRightFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-distinct-right-found"
    "assertion-frame-selection-distinct-right-found"
    [membershipFoundTemplate distinctRightFoundTicketTemplate
      (.var "selection-distinct-right")]
    [.remove (membershipFoundTemplate distinctRightFoundTicketTemplate
      (.var "selection-distinct-right")),
      .add (distinctControlTemplate (.var "selection-distinct-tail")
        (.var "selection-candidate-distinct-tail")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionDistinctRightFoundRule : Atom :=
  distinctRightFoundPair.1
def assertionFrameSelectionDistinctRightFoundDirective : SourceExecFact :=
  distinctRightFoundPair.2

private def distinctRightMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-frame-selection-distinct-right-missing"
    "assertion-frame-selection-distinct-right-missing"
    [membershipMissingTemplate currentDistinctRightTicketTemplate
      (.var "selection-distinct-right")]
    [.remove (membershipMissingTemplate currentDistinctRightTicketTemplate
      (.var "selection-distinct-right")),
      .add (distinctControlTemplate (.var "selection-distinct-tail")
        (.var "selection-candidate-distinct-remaining")),
      .add reloadTriggerTemplate]

def assertionFrameSelectionDistinctRightMissingRule : Atom :=
  distinctRightMissingPair.1
def assertionFrameSelectionDistinctRightMissingDirective : SourceExecFact :=
  distinctRightMissingPair.2

private def distinctDonePair : Atom × SourceExecFact :=
  let control := distinctControlTemplate nilTemplate nilTemplate
  rulePair "mm-source-assertion-frame-selection-distinct-done"
    "assertion-frame-selection-distinct-done"
    [control,
      assertionPublicationReloadCapabilityRow
        (.var "assertion-publication-reload-rule")]
    [.remove control, .add validTemplate,
      .add (.var "assertion-publication-reload-rule"),
      .add (assertionPhaseReloadTriggerAtom "publication"
        (.var "selection-source"))]

def assertionFrameSelectionDistinctDoneRule : Atom := distinctDonePair.1
def assertionFrameSelectionDistinctDoneDirective : SourceExecFact :=
  distinctDonePair.2

/-! ## Finite inventory and opaque reload -/

def assertionFrameSelectionRules : List Atom :=
  [assertionFrameSelectionStartRule,
   assertionFrameSelectionEssentialRule,
   assertionFrameSelectionFloatingLaunchRule,
   assertionFrameSelectionFloatingFoundRule,
   assertionFrameSelectionFloatingMissingRule,
   assertionFrameSelectionHypothesesDoneRule,
   assertionFrameSelectionDistinctLeftLaunchRule,
   assertionFrameSelectionDistinctLeftFoundRule,
   assertionFrameSelectionDistinctLeftMissingRule,
   assertionFrameSelectionDistinctRightFoundRule,
   assertionFrameSelectionDistinctRightMissingRule,
   assertionFrameSelectionDistinctDoneRule]

def assertionFrameSelectionDirectives : List SourceExecFact :=
  [assertionFrameSelectionStartDirective,
   assertionFrameSelectionEssentialDirective,
   assertionFrameSelectionFloatingLaunchDirective,
   assertionFrameSelectionFloatingFoundDirective,
   assertionFrameSelectionFloatingMissingDirective,
   assertionFrameSelectionHypothesesDoneDirective,
   assertionFrameSelectionDistinctLeftLaunchDirective,
   assertionFrameSelectionDistinctLeftFoundDirective,
   assertionFrameSelectionDistinctLeftMissingDirective,
   assertionFrameSelectionDistinctRightFoundDirective,
   assertionFrameSelectionDistinctRightMissingDirective,
   assertionFrameSelectionDistinctDoneDirective]

/-- Every variable authored in a frame-selection transaction sink is
inherited from that directive's input.  Selection can forward captured rows,
but it cannot introduce an unresolved data variable. -/
theorem assertionFrameSelectionDirectives_dataVariablesInherited :
    (assertionFrameSelectionDirectives.all fun directive =>
      ruleSinksVariablesInherited directive.rule.input
        directive.rule.tmpl.sinks) = true := by
  decide

theorem assertionFrameSelectionRules_extract_exact :
    assertionFrameSelectionRules.filterMap extractSupportedSourceExecFact =
      assertionFrameSelectionDirectives := by
  rfl

private def ruleKinds : List String :=
  ["start", "essential", "floating-launch", "floating-found",
   "floating-missing", "hypotheses-done", "distinct-left-launch",
   "distinct-left-found", "distinct-left-missing", "distinct-right-found",
   "distinct-right-missing", "distinct-done"]

private def ruleVariables : List String :=
  ["selection-rule-start", "selection-rule-essential",
   "selection-rule-floating-launch", "selection-rule-floating-found",
   "selection-rule-floating-missing", "selection-rule-hypotheses-done",
   "selection-rule-distinct-left-launch",
   "selection-rule-distinct-left-found",
   "selection-rule-distinct-left-missing",
   "selection-rule-distinct-right-found",
   "selection-rule-distinct-right-missing",
   "selection-rule-distinct-done"]

def assertionFrameSelectionRuleCaptureRow (kind : String)
    (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-selection-rule",
      .symbol kind, rule]

private def ruleCaptureTemplate (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-selection-rule",
      .symbol kind, .var variableName]

def assertionFrameSelectionRuleCaptureRows : List Atom :=
  List.zipWith assertionFrameSelectionRuleCaptureRow ruleKinds
    assertionFrameSelectionRules

private def reloadPatterns : List Atom :=
  reloadTriggerTemplate ::
    List.zipWith ruleCaptureTemplate ruleKinds ruleVariables

private def reloadSinks : List Sink :=
  [.remove reloadTriggerTemplate] ++
    ruleVariables.map fun variableName => .add (.var variableName)

def assertionFrameSelectionReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def assertionFrameSelectionReloadDirective : SourceExecFact :=
  { atom := assertionFrameSelectionReloadRule
    loc := reloadLocation
    rule :=
      { priority := 37
        name := "mm-source-assertion-frame-selection-reload"
        input := .compat (mkPattern reloadPatterns)
        guards := []
        tmpl := mkTemplate reloadSinks } }

theorem extract_assertionFrameSelectionReloadRule_exact :
    extractSupportedSourceExecFact assertionFrameSelectionReloadRule =
      some assertionFrameSelectionReloadDirective := by
  rfl

def assertionFrameSelectionReloadRuleCaptureRow : Atom :=
  assertionFrameSelectionReloadCapabilityRow
    assertionFrameSelectionReloadRule

/-! ## Focused executable controls -/

private def fixtureOwner : Atom := .symbol "frame-selection-source"

private def floatingX : HypothesisView := .floating "vx" "setvar" "x"
private def floatingZ : HypothesisView := .floating "vz" "setvar" "z"
private def essentialY : HypothesisView :=
  .essential "e1" { typecode := "wff", body := [.var "y"] }

private def fixtureHypotheses : List HypothesisView :=
  [floatingX, floatingZ, essentialY]

private def fixtureDistinct : List (String × String) :=
  [("x", "y"), ("x", "z"), ("x", "y")]

private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [.var "x", .var "y"] }

private def fixtureState :=
  sourceStateFromAssertionSnapshot fixtureHypotheses fixtureDistinct

private def fixtureAssertion : SourceAssertion :=
  sourceAssertionFromCertificate fixtureState "ax" fixtureFormula ["x", "y"]

private def fixtureContext : AssertionFrameContext :=
  { position := 3
    nextPosition := 4
    statement :=
      .axiomatic
        { fileId := "frame-selection.mm", start := 0, stop := 2 }
        { span := { fileId := "frame-selection.mm", start := 3, stop := 5 },
          name := "ax" }
        { span := { fileId := "frame-selection.mm", start := 6, stop := 9 },
          name := "wff" }
        [] { fileId := "frame-selection.mm", start := 10, stop := 12 }
    assertionPosition := 0
    nextAssertionPosition := 1
    certificate := ["x", "y"]
    assertion := fixtureAssertion }

private def fixtureCertificateEvidence : AssertionCertificateEvidence :=
  { context := fixtureContext
    activeHypotheses := fixtureHypotheses
    activeDistinctVariables := fixtureDistinct
    requiredOccurrences := ["y", "x"] }

private def fixtureHypothesisControl
    (remaining candidateHypotheses candidateLabels : List Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-select-hypotheses",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom fixtureHypotheses,
      listAtom stringPairAtom fixtureDistinct,
      listAtom stringAtom fixtureCertificateEvidence.requiredOccurrences,
      encodedListAtom remaining, encodedListAtom candidateHypotheses,
      encodedListAtom candidateLabels]

private def fixtureDistinctControl
    (remaining candidateDistinct : List Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-select-distinct",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom fixtureHypotheses,
      listAtom stringPairAtom fixtureDistinct,
      listAtom stringAtom fixtureCertificateEvidence.requiredOccurrences,
      encodedListAtom remaining, encodedListAtom candidateDistinct]

private def fixtureFloatingTicket (remaining candidateHypotheses
    candidateLabels : List Atom) (hypothesis : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-floating-ticket",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom fixtureHypotheses,
      listAtom stringPairAtom fixtureDistinct,
      listAtom stringAtom fixtureCertificateEvidence.requiredOccurrences,
      encodedListAtom remaining, encodedListAtom candidateHypotheses,
      encodedListAtom candidateLabels, hypothesis]

private def fixtureDistinctLeftTicket (remaining candidateDistinct : List Atom)
    (pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-distinct-left-ticket",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom fixtureHypotheses,
      listAtom stringPairAtom fixtureDistinct,
      listAtom stringAtom fixtureCertificateEvidence.requiredOccurrences,
      encodedListAtom remaining, encodedListAtom candidateDistinct, pair]

private def fixtureDistinctRightTicket (remaining candidateDistinct : List Atom)
    (pair : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-distinct-right-ticket",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom fixtureHypotheses,
      listAtom stringPairAtom fixtureDistinct,
      listAtom stringAtom fixtureCertificateEvidence.requiredOccurrences,
      encodedListAtom remaining, encodedListAtom candidateDistinct, pair]

private def startCanaryProgram : List Atom :=
  [assertionFrameSelectionStartRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   assertionCertificateEvidenceAtom fixtureOwner fixtureCertificateEvidence]

def startCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact startCanaryProgram
    assertionFrameSelectionStartDirective

theorem startCanary_emits_exact_synchronized_lists :
    fixtureHypothesisControl
        (fixtureHypotheses.map hypothesisAtom)
        (fixtureAssertion.hypotheses.map hypothesisAtom)
        (fixtureAssertion.frame.hypothesisLabels.map stringAtom) ∈
      startCanaryTarget := by
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

private def essentialCanaryProgram : List Atom :=
  [assertionFrameSelectionEssentialRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   fixtureHypothesisControl [hypothesisAtom essentialY]
     [hypothesisAtom essentialY] [stringAtom "e1"]]

theorem essentialCanary_consumes_exact_hypothesis_and_label :
    fixtureHypothesisControl [] [] [] ∈
      cFireReflectiveSourceExecFact essentialCanaryProgram
        assertionFrameSelectionEssentialDirective := by
  decide +kernel

private def floatingLaunchCanaryProgram : List Atom :=
  [assertionFrameSelectionFloatingLaunchRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipReloadRuleCaptureRow,
   fixtureHypothesisControl [hypothesisAtom floatingX]
     [hypothesisAtom floatingX] [stringAtom "vx"]]

theorem floatingLaunchCanary_queries_exact_certificate :
    ∃ request,
      membershipRequestRawAtom fixtureOwner request (stringAtom "x")
          (encodedListAtom []) (listAtom stringAtom ["x", "y"]) ∈
        cFireReflectiveSourceExecFact floatingLaunchCanaryProgram
          assertionFrameSelectionFloatingLaunchDirective := by
  refine ⟨?_, ?_⟩
  · exact
      fixtureFloatingTicket [] [hypothesisAtom floatingX]
        [stringAtom "vx"] (hypothesisAtom floatingX)
  · decide +kernel

private def floatingFoundCanaryProgram : List Atom :=
  [assertionFrameSelectionFloatingFoundRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipFoundRawAtom fixtureOwner
     (fixtureFloatingTicket [] [hypothesisAtom floatingX]
       [stringAtom "vx"] (hypothesisAtom floatingX))
     (stringAtom "x") (encodedListAtom [])
     (listAtom stringAtom ["y"])]

theorem floatingFoundCanary_consumes_exact_candidate :
    fixtureHypothesisControl [] [] [] ∈
      cFireReflectiveSourceExecFact floatingFoundCanaryProgram
        assertionFrameSelectionFloatingFoundDirective := by
  decide +kernel

private def floatingMissingCanaryProgram : List Atom :=
  [assertionFrameSelectionFloatingMissingRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipMissingRawAtom fixtureOwner
     (fixtureFloatingTicket [] [] [] (hypothesisAtom floatingZ))
     (stringAtom "z") (listAtom stringAtom ["y", "x"])]

theorem floatingMissingCanary_skips_unselected_source_entry :
    fixtureHypothesisControl [] [] [] ∈
      cFireReflectiveSourceExecFact floatingMissingCanaryProgram
        assertionFrameSelectionFloatingMissingDirective := by
  decide +kernel

private def hypothesesDoneCanaryProgram : List Atom :=
  [assertionFrameSelectionHypothesesDoneRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   fixtureHypothesisControl [] [] []]

theorem hypothesesDoneCanary_starts_exact_distinct_comparison :
    fixtureDistinctControl (fixtureDistinct.map stringPairAtom)
        (fixtureAssertion.frame.distinctVariables.map stringPairAtom) ∈
      cFireReflectiveSourceExecFact hypothesesDoneCanaryProgram
        assertionFrameSelectionHypothesesDoneDirective := by
  decide +kernel

private def xyPairAtom : Atom := stringPairAtom ("x", "y")
private def xzPairAtom : Atom := stringPairAtom ("x", "z")
private def zxPairAtom : Atom := stringPairAtom ("z", "x")

private def distinctLeftFoundCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctLeftFoundRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipReloadRuleCaptureRow,
   membershipFoundRawAtom fixtureOwner
     (fixtureDistinctLeftTicket [] [xyPairAtom] xyPairAtom)
     (stringAtom "x") (encodedListAtom [])
     (listAtom stringAtom ["y"])]

theorem distinctLeftFoundCanary_queries_right_endpoint :
    membershipRequestRawAtom fixtureOwner
        (fixtureDistinctRightTicket [] [xyPairAtom] xyPairAtom)
        (stringAtom "y") (encodedListAtom [])
        (listAtom stringAtom ["x", "y"]) ∈
      cFireReflectiveSourceExecFact distinctLeftFoundCanaryProgram
        assertionFrameSelectionDistinctLeftFoundDirective := by
  decide +kernel

private def distinctLeftMissingCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctLeftMissingRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipMissingRawAtom fixtureOwner
     (fixtureDistinctLeftTicket [] [] zxPairAtom)
     (stringAtom "z") (listAtom stringAtom ["y", "x"])]

theorem distinctLeftMissingCanary_skips_source_pair :
    fixtureDistinctControl [] [] ∈
      cFireReflectiveSourceExecFact distinctLeftMissingCanaryProgram
        assertionFrameSelectionDistinctLeftMissingDirective := by
  decide +kernel

private def distinctRightFoundCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctRightFoundRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipFoundRawAtom fixtureOwner
     (fixtureDistinctRightTicket [] [xyPairAtom] xyPairAtom)
     (stringAtom "y") (listAtom stringAtom ["x"])
     (encodedListAtom [])]

theorem distinctRightFoundCanary_consumes_exact_candidate_occurrence :
    fixtureDistinctControl [] [] ∈
      cFireReflectiveSourceExecFact distinctRightFoundCanaryProgram
        assertionFrameSelectionDistinctRightFoundDirective := by
  decide +kernel

private def distinctRightMissingCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctRightMissingRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   membershipMissingRawAtom fixtureOwner
     (fixtureDistinctRightTicket [] [] xzPairAtom)
     (stringAtom "z") (listAtom stringAtom ["y", "x"])]

theorem distinctRightMissingCanary_skips_source_pair :
    fixtureDistinctControl [] [] ∈
      cFireReflectiveSourceExecFact distinctRightMissingCanaryProgram
        assertionFrameSelectionDistinctRightMissingDirective := by
  decide +kernel

private def distinctDoneCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctDoneRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   assertionPublicationReloadCapabilityRow
     (.symbol "publication-reload-rule"),
   fixtureDistinctControl [] []]

theorem distinctDoneCanary_emits_typed_evidence :
    assertionFrameSelectionEvidenceAtom fixtureOwner
        { context := fixtureContext } ∈
      cFireReflectiveSourceExecFact distinctDoneCanaryProgram
        assertionFrameSelectionDistinctDoneDirective := by
  decide +kernel

private def wrongEssentialCanaryProgram : List Atom :=
  [assertionFrameSelectionEssentialRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   fixtureHypothesisControl [hypothesisAtom essentialY]
     [hypothesisAtom floatingX] [stringAtom "vx"]]

theorem wrongEssentialCanary_preserves_control_without_validation :
    fixtureHypothesisControl [hypothesisAtom essentialY]
        [hypothesisAtom floatingX] [stringAtom "vx"] ∈
      cFireReflectiveSourceExecFact wrongEssentialCanaryProgram
        assertionFrameSelectionEssentialDirective ∧
    assertionFrameSelectionEvidenceAtom fixtureOwner
        { context := fixtureContext } ∉
      cFireReflectiveSourceExecFact wrongEssentialCanaryProgram
        assertionFrameSelectionEssentialDirective := by
  decide +kernel

private def extraCandidateCanaryProgram : List Atom :=
  [assertionFrameSelectionDistinctDoneRule,
   assertionFrameSelectionReloadRuleCaptureRow,
   assertionPublicationReloadCapabilityRow
     (.symbol "publication-reload-rule"),
   fixtureDistinctControl [] [xyPairAtom]]

theorem extraCandidateCanary_preserves_control_without_validation :
    fixtureDistinctControl [] [xyPairAtom] ∈
      cFireReflectiveSourceExecFact extraCandidateCanaryProgram
        assertionFrameSelectionDistinctDoneDirective ∧
    assertionFrameSelectionEvidenceAtom fixtureOwner
        { context := fixtureContext } ∉
      cFireReflectiveSourceExecFact extraCandidateCanaryProgram
        assertionFrameSelectionDistinctDoneDirective := by
  decide +kernel

theorem fixture_reference_comparison_is_exact :
    selectAssertionFrame? fixtureCertificateEvidence =
      some { context := fixtureContext } := by
  decide +kernel

#print axioms decodeAssertionFrameSelectionEvidenceAtom_encoded
#print axioms assertionFrameSelectionEvidenceAtom_injective
#print axioms assertionFrameSelectionDirectives_dataVariablesInherited
#print axioms selectAssertionFrame?_eq_some_iff
#print axioms assertionFrameSelectionRules_extract_exact
#print axioms extract_assertionFrameSelectionReloadRule_exact
#print axioms startCanary_emits_exact_synchronized_lists
#print axioms startCanary_inhabits_exact_native_target
#print axioms essentialCanary_consumes_exact_hypothesis_and_label
#print axioms floatingLaunchCanary_queries_exact_certificate
#print axioms floatingFoundCanary_consumes_exact_candidate
#print axioms floatingMissingCanary_skips_unselected_source_entry
#print axioms hypothesesDoneCanary_starts_exact_distinct_comparison
#print axioms distinctLeftFoundCanary_queries_right_endpoint
#print axioms distinctLeftMissingCanary_skips_source_pair
#print axioms distinctRightFoundCanary_consumes_exact_candidate_occurrence
#print axioms distinctRightMissingCanary_skips_source_pair
#print axioms distinctDoneCanary_emits_typed_evidence
#print axioms wrongEssentialCanary_preserves_control_without_validation
#print axioms extraCandidateCanary_preserves_control_without_validation
#print axioms fixture_reference_comparison_is_exact

end Mettapedia.Languages.Metamath.MM2SourceAssertionFrameSelectionExecution
