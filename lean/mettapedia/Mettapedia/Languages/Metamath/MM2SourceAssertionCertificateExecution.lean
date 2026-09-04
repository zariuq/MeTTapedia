import Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership

/-!
# Native assertion-certificate execution

This module derives the mandatory-variable occurrence stream from the checked
assertion formula and the active-hypothesis snapshot.  It then uses the shared
ordinary-MM2 finite-membership machine in both directions:

* every derived occurrence must be present in the candidate certificate;
* every certificate entry must occur in the derived stream;
* every certificate entry must be absent from its own tail.

The last check establishes duplicate freedom.  No candidate frame or
candidate hypothesis list authorizes these checks.  A successful transaction
emits one typed private evidence row; publication of assertion runtime rows is
left to the next transaction stage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionCertificateExecution

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrame
open Mettapedia.Languages.Metamath.MM2SourceAssertionFrameExecution
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Typed terminal evidence -/

structure AssertionCertificateEvidence where
  context : AssertionFrameContext
  activeHypotheses : List HypothesisView
  activeDistinctVariables : List (String × String)
  requiredOccurrences : List String
deriving DecidableEq

def assertionCertificateEvidenceAtom (owner : Atom)
    (evidence : AssertionCertificateEvidence) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-valid", owner,
      assertionFrameContextAtom evidence.context,
      listAtom hypothesisAtom evidence.activeHypotheses,
      listAtom stringPairAtom evidence.activeDistinctVariables,
      listAtom stringAtom evidence.requiredOccurrences]

def decodeAssertionCertificateEvidenceAtom (owner : Atom) :
    Atom → Option AssertionCertificateEvidence
  | .expression
      [.symbol tag, actualOwner, encodedContext, encodedHypotheses,
        encodedDistinct, encodedOccurrences] => do
      guard (tag == "mm-internal-source-assertion-certificate-valid")
      guard (actualOwner == owner)
      let context <- decodeAssertionFrameContextAtom encodedContext
      let activeHypotheses <-
        decodeListAtom decodeHypothesisAtom encodedHypotheses
      let activeDistinctVariables <-
        decodeListAtom decodeStringPairAtom encodedDistinct
      let requiredOccurrences <-
        decodeListAtom decodeStringAtom encodedOccurrences
      pure
        { context, activeHypotheses, activeDistinctVariables,
          requiredOccurrences }
  | _ => none

@[simp] theorem decodeAssertionCertificateEvidenceAtom_encoded
    (owner : Atom) (evidence : AssertionCertificateEvidence) :
    decodeAssertionCertificateEvidenceAtom owner
        (assertionCertificateEvidenceAtom owner evidence) =
      some evidence := by
  cases evidence
  simp [decodeAssertionCertificateEvidenceAtom,
    assertionCertificateEvidenceAtom]

theorem assertionCertificateEvidenceAtom_injective (owner : Atom) :
    Function.Injective (assertionCertificateEvidenceAtom owner) := by
  intro left right equal
  have decoded :=
    congrArg (decodeAssertionCertificateEvidenceAtom owner) equal
  simpa using decoded

def assertionCertificateFaultAtom (owner : Atom)
    (context reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-fault", owner,
      context, reason, evidence]

/-! ## Ordinary-MM2 templates -/

private def nilTemplate : Atom :=
  .expression [.symbol "mm-nil"]

private def consTemplate (head tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", head, tail]

private def location (name : String) : Atom :=
  .expression [.symbol "07", .symbol name]

private def reloadLocation : Atom :=
  .expression [.symbol "36", .symbol "mm-source-assertion-certificate-reload"]

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
      { priority := 7
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def certificateReloadRuleCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-reloader",
      .var "assertion-certificate-reload-rule"]

private def rulePair (name stem : String) (patterns : List Atom)
    (sinks : List Sink) : Atom × SourceExecFact :=
  let loc := location name
  let self := selfTemplate loc stem
  let allPatterns := self :: certificateReloadRuleCaptureTemplate :: patterns
  let allSinks := .add (.var "assertion-certificate-reload-rule") :: sinks
  let atom := mkRule loc allPatterns allSinks
  (atom, mkDirective atom loc name allPatterns allSinks)

/-! ## Shared transaction fields -/

private def formulaShapeTemplate : Atom :=
  .expression
    [.symbol "mm-formula", .var "certificate-typecode",
      .var "certificate-formula-body"]

private def assertionShapeTemplate : Atom :=
  .expression
    [.symbol "mm-assertion", .var "certificate-assertion-label",
      formulaShapeTemplate, .var "certificate-candidate-frame",
      .var "certificate-candidate-hypotheses"]

private def contextShapeTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-context",
      .var "certificate-position", .var "certificate-next-position",
      .var "certificate-statement",
      .var "certificate-assertion-position",
      .var "certificate-next-assertion-position",
      .var "certificate-mandatory-variables", assertionShapeTemplate]

private def detailedSnapshotTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-snapshot",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-hypotheses", .var "certificate-distinct"]

private def formulaControlTemplate (body occurrences : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-formula",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-hypotheses", .var "certificate-distinct", body,
      occurrences, .var "certificate-mandatory-variables"]

private def hypothesisControlTemplate
    (allHypotheses hypotheses occurrences : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-hypotheses",
      .var "certificate-source", contextShapeTemplate,
      allHypotheses, hypotheses, .var "certificate-distinct", occurrences,
      .var "certificate-mandatory-variables"]

private def essentialControlTemplate (hypotheses body occurrences : Atom) :
    Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-essential",
      .var "certificate-source", contextShapeTemplate, hypotheses,
      .var "certificate-all-hypotheses", .var "certificate-distinct", body,
      occurrences, .var "certificate-mandatory-variables"]

private def requiredControlTemplate (occurrences remaining : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-required",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      occurrences, remaining, .var "certificate-mandatory-variables"]

private def certificateControlTemplate (occurrences certificate : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-entries",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      occurrences, certificate]

private def faultTemplate (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-fault",
      .var "certificate-source", contextShapeTemplate, reason,
      evidence]

private def validTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-valid",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      .var "certificate-occurrences"]

private def reloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-assertion-certificate",
      .var "certificate-source"]

def assertionCertificateReloadTriggerAtom (owner : Atom) : Atom :=
  assertionPhaseReloadTriggerAtom "certificate" owner

def assertionFrameSelectionReloadCapabilityRow (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-frame-selection-reloader", rule]

/-! ## Occurrence extraction -/

private def startPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-start"
    "assertion-certificate-start"
    [detailedSnapshotTemplate]
    [.remove detailedSnapshotTemplate,
      .add (formulaControlTemplate (.var "certificate-formula-body")
        nilTemplate),
      .add reloadTriggerTemplate]

def assertionCertificateStartRule : Atom := startPair.1
def assertionCertificateStartDirective : SourceExecFact := startPair.2

private def formulaConstHead : Atom :=
  .expression
    [.symbol constTag, .var "certificate-formula-constant"]

private def formulaVariableHead : Atom :=
  .expression
    [.symbol variableTag, .var "certificate-formula-variable"]

private def formulaConstPair : Atom × SourceExecFact :=
  let control :=
    formulaControlTemplate
      (consTemplate formulaConstHead (.var "certificate-formula-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-formula-constant"
    "assertion-certificate-formula-constant"
    [control]
    [.remove control,
      .add (formulaControlTemplate (.var "certificate-formula-tail")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateFormulaConstantRule : Atom := formulaConstPair.1
def assertionCertificateFormulaConstantDirective : SourceExecFact :=
  formulaConstPair.2

private def formulaVariablePair : Atom × SourceExecFact :=
  let control :=
    formulaControlTemplate
      (consTemplate formulaVariableHead (.var "certificate-formula-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-formula-variable"
    "assertion-certificate-formula-variable"
    [control]
    [.remove control,
      .add (formulaControlTemplate (.var "certificate-formula-tail")
        (consTemplate (.var "certificate-formula-variable")
          (.var "certificate-occurrences"))),
      .add reloadTriggerTemplate]

def assertionCertificateFormulaVariableRule : Atom := formulaVariablePair.1
def assertionCertificateFormulaVariableDirective : SourceExecFact :=
  formulaVariablePair.2

private def formulaDonePair : Atom × SourceExecFact :=
  let control :=
    formulaControlTemplate nilTemplate (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-formula-done"
    "assertion-certificate-formula-done"
    [control]
    [.remove control,
      .add (hypothesisControlTemplate (.var "certificate-hypotheses")
        (.var "certificate-hypotheses")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateFormulaDoneRule : Atom := formulaDonePair.1
def assertionCertificateFormulaDoneDirective : SourceExecFact :=
  formulaDonePair.2

private def floatingHypothesisHead : Atom :=
  .expression
    [.symbol "mm-floating", .var "certificate-floating-label",
      .var "certificate-floating-typecode",
      .var "certificate-floating-variable"]

private def essentialHypothesisHead : Atom :=
  .expression
    [.symbol "mm-essential", .var "certificate-essential-label",
      .expression
        [.symbol "mm-formula", .var "certificate-essential-typecode",
          .var "certificate-essential-body"]]

private def hypothesisFloatingPair : Atom × SourceExecFact :=
  let control :=
    hypothesisControlTemplate
      (.var "certificate-all-hypotheses")
      (consTemplate floatingHypothesisHead
        (.var "certificate-hypothesis-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-hypothesis-floating"
    "assertion-certificate-hypothesis-floating"
    [control]
    [.remove control,
      .add (hypothesisControlTemplate
        (.var "certificate-all-hypotheses")
        (.var "certificate-hypothesis-tail")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateHypothesisFloatingRule : Atom :=
  hypothesisFloatingPair.1
def assertionCertificateHypothesisFloatingDirective : SourceExecFact :=
  hypothesisFloatingPair.2

private def hypothesisEssentialPair : Atom × SourceExecFact :=
  let control :=
    hypothesisControlTemplate
      (.var "certificate-all-hypotheses")
      (consTemplate essentialHypothesisHead
        (.var "certificate-hypothesis-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-hypothesis-essential"
    "assertion-certificate-hypothesis-essential"
    [control]
    [.remove control,
      .add (essentialControlTemplate
        (.var "certificate-hypothesis-tail")
        (.var "certificate-essential-body")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateHypothesisEssentialRule : Atom :=
  hypothesisEssentialPair.1
def assertionCertificateHypothesisEssentialDirective : SourceExecFact :=
  hypothesisEssentialPair.2

private def hypothesisDonePair : Atom × SourceExecFact :=
  let control :=
    hypothesisControlTemplate (.var "certificate-all-hypotheses")
      nilTemplate (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-hypothesis-done"
    "assertion-certificate-hypothesis-done"
    [control]
    [.remove control,
      .add (requiredControlTemplate (.var "certificate-occurrences")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateHypothesisDoneRule : Atom := hypothesisDonePair.1
def assertionCertificateHypothesisDoneDirective : SourceExecFact :=
  hypothesisDonePair.2

private def essentialConstPair : Atom × SourceExecFact :=
  let control :=
    essentialControlTemplate (.var "certificate-remaining-hypotheses")
      (consTemplate formulaConstHead (.var "certificate-essential-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-essential-constant"
    "assertion-certificate-essential-constant"
    [control]
    [.remove control,
      .add (essentialControlTemplate
        (.var "certificate-remaining-hypotheses")
        (.var "certificate-essential-tail")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateEssentialConstantRule : Atom := essentialConstPair.1
def assertionCertificateEssentialConstantDirective : SourceExecFact :=
  essentialConstPair.2

private def essentialVariablePair : Atom × SourceExecFact :=
  let control :=
    essentialControlTemplate (.var "certificate-remaining-hypotheses")
      (consTemplate formulaVariableHead (.var "certificate-essential-tail"))
      (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-essential-variable"
    "assertion-certificate-essential-variable"
    [control]
    [.remove control,
      .add (essentialControlTemplate
        (.var "certificate-remaining-hypotheses")
        (.var "certificate-essential-tail")
        (consTemplate (.var "certificate-formula-variable")
          (.var "certificate-occurrences"))),
      .add reloadTriggerTemplate]

def assertionCertificateEssentialVariableRule : Atom := essentialVariablePair.1
def assertionCertificateEssentialVariableDirective : SourceExecFact :=
  essentialVariablePair.2

private def essentialDonePair : Atom × SourceExecFact :=
  let control :=
    essentialControlTemplate (.var "certificate-remaining-hypotheses")
      nilTemplate (.var "certificate-occurrences")
  rulePair "mm-source-assertion-certificate-essential-done"
    "assertion-certificate-essential-done"
    [control]
    [.remove control,
      .add (hypothesisControlTemplate
        (.var "certificate-all-hypotheses")
        (.var "certificate-remaining-hypotheses")
        (.var "certificate-occurrences")),
      .add reloadTriggerTemplate]

def assertionCertificateEssentialDoneRule : Atom := essentialDonePair.1
def assertionCertificateEssentialDoneDirective : SourceExecFact :=
  essentialDonePair.2

/-! ## Two-sided certificate checks through finite membership -/

private def requiredTicketTemplate (remaining target : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-required-ticket",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      .var "certificate-occurrences", remaining,
      .var "certificate-mandatory-variables", target]

private def currentRequiredTicketTemplate : Atom :=
  requiredTicketTemplate (.var "certificate-required-tail")
    (.var "certificate-required-name")

private def membershipRequestTemplate (ticket target remaining : Atom) : Atom :=
  membershipRequestRawAtom (.var "certificate-source") ticket target
    nilTemplate remaining

private def membershipFoundTemplate (ticket target : Atom) : Atom :=
  membershipFoundRawAtom (.var "certificate-source") ticket target
    (.var "certificate-membership-visited")
    (.var "certificate-membership-remaining")

private def membershipMissingTemplate (ticket target : Atom) : Atom :=
  membershipMissingRawAtom (.var "certificate-source") ticket target
    (.var "certificate-membership-visited")

private def membershipReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-list-membership", .var "certificate-source"]

private def membershipReloadRuleCaptureTemplate : Atom :=
  membershipReloadCapabilityRow (.var "membership-reload-rule")

private def membershipReturnTemplate (ticket : Atom) : Atom :=
  membershipReturnCapabilityRow (.var "certificate-source") ticket
    (.var "assertion-certificate-reload-rule") reloadTriggerTemplate

private def requiredLaunchPair : Atom × SourceExecFact :=
  let control :=
    requiredControlTemplate (.var "certificate-occurrences")
      (consTemplate (.var "certificate-required-name")
        (.var "certificate-required-tail"))
  rulePair "mm-source-assertion-certificate-required-launch"
    "assertion-certificate-required-launch"
    [control, membershipReloadRuleCaptureTemplate]
    [.remove control,
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentRequiredTicketTemplate
        (.var "certificate-required-name")
        (.var "certificate-mandatory-variables")),
      .add (membershipReturnTemplate currentRequiredTicketTemplate),
      .add membershipReloadTemplate]

def assertionCertificateRequiredLaunchRule : Atom := requiredLaunchPair.1
def assertionCertificateRequiredLaunchDirective : SourceExecFact :=
  requiredLaunchPair.2

private def requiredFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-required-found"
    "assertion-certificate-required-found"
    [membershipFoundTemplate currentRequiredTicketTemplate
      (.var "certificate-required-name")]
    [.remove (membershipFoundTemplate currentRequiredTicketTemplate
      (.var "certificate-required-name")),
      .add (requiredControlTemplate (.var "certificate-occurrences")
        (.var "certificate-required-tail")),
      .add reloadTriggerTemplate]

def assertionCertificateRequiredFoundRule : Atom := requiredFoundPair.1
def assertionCertificateRequiredFoundDirective : SourceExecFact :=
  requiredFoundPair.2

private def requiredMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-required-missing"
    "assertion-certificate-required-missing"
    [membershipMissingTemplate currentRequiredTicketTemplate
      (.var "certificate-required-name")]
    [.remove (membershipMissingTemplate currentRequiredTicketTemplate
      (.var "certificate-required-name")),
      .add (faultTemplate (.symbol "missing-mandatory-variable")
        (.var "certificate-required-name"))]

def assertionCertificateRequiredMissingRule : Atom := requiredMissingPair.1
def assertionCertificateRequiredMissingDirective : SourceExecFact :=
  requiredMissingPair.2

private def requiredDonePair : Atom × SourceExecFact :=
  let control :=
    requiredControlTemplate (.var "certificate-occurrences") nilTemplate
  rulePair "mm-source-assertion-certificate-required-done"
    "assertion-certificate-required-done"
    [control]
    [.remove control,
      .add (certificateControlTemplate (.var "certificate-occurrences")
        (.var "certificate-mandatory-variables")),
      .add reloadTriggerTemplate]

def assertionCertificateRequiredDoneRule : Atom := requiredDonePair.1
def assertionCertificateRequiredDoneDirective : SourceExecFact :=
  requiredDonePair.2

private def coverageTicketTemplate (tail target : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-coverage-ticket",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      .var "certificate-occurrences", tail, target]

private def currentCoverageTicketTemplate : Atom :=
  coverageTicketTemplate (.var "certificate-entry-tail")
    (.var "certificate-entry-name")

private def duplicateTicketTemplate (tail target : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-duplicate-ticket",
      .var "certificate-source", contextShapeTemplate,
      .var "certificate-all-hypotheses", .var "certificate-distinct",
      .var "certificate-occurrences", tail, target]

private def currentDuplicateTicketTemplate : Atom :=
  duplicateTicketTemplate (.var "certificate-entry-tail")
    (.var "certificate-entry-name")

private def certificateLaunchPair : Atom × SourceExecFact :=
  let control :=
    certificateControlTemplate (.var "certificate-occurrences")
      (consTemplate (.var "certificate-entry-name")
        (.var "certificate-entry-tail"))
  rulePair "mm-source-assertion-certificate-entry-launch"
    "assertion-certificate-entry-launch"
    [control, membershipReloadRuleCaptureTemplate]
    [.remove control,
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentCoverageTicketTemplate
        (.var "certificate-entry-name")
        (.var "certificate-occurrences")),
      .add (membershipReturnTemplate currentCoverageTicketTemplate),
      .add membershipReloadTemplate]

def assertionCertificateEntryLaunchRule : Atom := certificateLaunchPair.1
def assertionCertificateEntryLaunchDirective : SourceExecFact :=
  certificateLaunchPair.2

private def coverageFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-entry-covered"
    "assertion-certificate-entry-covered"
    [membershipFoundTemplate currentCoverageTicketTemplate
      (.var "certificate-entry-name"),
      membershipReloadRuleCaptureTemplate]
    [.remove (membershipFoundTemplate currentCoverageTicketTemplate
      (.var "certificate-entry-name")),
      .add (.var "membership-reload-rule"),
      .add (membershipRequestTemplate currentDuplicateTicketTemplate
        (.var "certificate-entry-name")
        (.var "certificate-entry-tail")),
      .add (membershipReturnTemplate currentDuplicateTicketTemplate),
      .add membershipReloadTemplate]

def assertionCertificateEntryCoveredRule : Atom := coverageFoundPair.1
def assertionCertificateEntryCoveredDirective : SourceExecFact :=
  coverageFoundPair.2

private def coverageMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-entry-extra"
    "assertion-certificate-entry-extra"
    [membershipMissingTemplate currentCoverageTicketTemplate
      (.var "certificate-entry-name")]
    [.remove (membershipMissingTemplate currentCoverageTicketTemplate
      (.var "certificate-entry-name")),
      .add (faultTemplate (.symbol "extra-mandatory-variable")
        (.var "certificate-entry-name"))]

def assertionCertificateEntryExtraRule : Atom := coverageMissingPair.1
def assertionCertificateEntryExtraDirective : SourceExecFact :=
  coverageMissingPair.2

private def duplicateFoundPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-entry-duplicate"
    "assertion-certificate-entry-duplicate"
    [membershipFoundTemplate currentDuplicateTicketTemplate
      (.var "certificate-entry-name")]
    [.remove (membershipFoundTemplate currentDuplicateTicketTemplate
      (.var "certificate-entry-name")),
      .add (faultTemplate (.symbol "duplicate-mandatory-variable")
        (.var "certificate-entry-name"))]

def assertionCertificateEntryDuplicateRule : Atom := duplicateFoundPair.1
def assertionCertificateEntryDuplicateDirective : SourceExecFact :=
  duplicateFoundPair.2

private def duplicateMissingPair : Atom × SourceExecFact :=
  rulePair "mm-source-assertion-certificate-entry-unique"
    "assertion-certificate-entry-unique"
    [membershipMissingTemplate currentDuplicateTicketTemplate
      (.var "certificate-entry-name")]
    [.remove (membershipMissingTemplate currentDuplicateTicketTemplate
      (.var "certificate-entry-name")),
      .add (certificateControlTemplate (.var "certificate-occurrences")
        (.var "certificate-entry-tail")),
      .add reloadTriggerTemplate]

def assertionCertificateEntryUniqueRule : Atom := duplicateMissingPair.1
def assertionCertificateEntryUniqueDirective : SourceExecFact :=
  duplicateMissingPair.2

private def certificateDonePair : Atom × SourceExecFact :=
  let control :=
    certificateControlTemplate (.var "certificate-occurrences") nilTemplate
  rulePair "mm-source-assertion-certificate-entries-done"
    "assertion-certificate-entries-done"
    [control,
      assertionFrameSelectionReloadCapabilityRow
        (.var "assertion-frame-selection-reload-rule")]
    [.remove control, .add validTemplate,
      .add (.var "assertion-frame-selection-reload-rule"),
      .add (assertionPhaseReloadTriggerAtom "frame-selection"
        (.var "certificate-source"))]

def assertionCertificateEntriesDoneRule : Atom := certificateDonePair.1
def assertionCertificateEntriesDoneDirective : SourceExecFact :=
  certificateDonePair.2

/-! ## Opaque finite rule inventory -/

def assertionCertificateRules : List Atom :=
  [assertionCertificateStartRule,
   assertionCertificateFormulaConstantRule,
   assertionCertificateFormulaVariableRule,
   assertionCertificateFormulaDoneRule,
   assertionCertificateHypothesisFloatingRule,
   assertionCertificateHypothesisEssentialRule,
   assertionCertificateHypothesisDoneRule,
   assertionCertificateEssentialConstantRule,
   assertionCertificateEssentialVariableRule,
   assertionCertificateEssentialDoneRule,
   assertionCertificateRequiredLaunchRule,
   assertionCertificateRequiredFoundRule,
   assertionCertificateRequiredMissingRule,
   assertionCertificateRequiredDoneRule,
   assertionCertificateEntryLaunchRule,
   assertionCertificateEntryCoveredRule,
   assertionCertificateEntryExtraRule,
   assertionCertificateEntryDuplicateRule,
   assertionCertificateEntryUniqueRule,
   assertionCertificateEntriesDoneRule]

def assertionCertificateDirectives : List SourceExecFact :=
  [assertionCertificateStartDirective,
   assertionCertificateFormulaConstantDirective,
   assertionCertificateFormulaVariableDirective,
   assertionCertificateFormulaDoneDirective,
   assertionCertificateHypothesisFloatingDirective,
   assertionCertificateHypothesisEssentialDirective,
   assertionCertificateHypothesisDoneDirective,
   assertionCertificateEssentialConstantDirective,
   assertionCertificateEssentialVariableDirective,
   assertionCertificateEssentialDoneDirective,
   assertionCertificateRequiredLaunchDirective,
   assertionCertificateRequiredFoundDirective,
   assertionCertificateRequiredMissingDirective,
   assertionCertificateRequiredDoneDirective,
   assertionCertificateEntryLaunchDirective,
   assertionCertificateEntryCoveredDirective,
   assertionCertificateEntryExtraDirective,
   assertionCertificateEntryDuplicateDirective,
   assertionCertificateEntryUniqueDirective,
   assertionCertificateEntriesDoneDirective]

/-- Every variable authored in a certificate-transaction sink is inherited
from that directive's input.  In particular, the threaded all-hypotheses
snapshot cannot be recreated as an output-local variable. -/
theorem assertionCertificateDirectives_dataVariablesInherited :
    (assertionCertificateDirectives.all fun directive =>
      ruleSinksVariablesInherited directive.rule.input
        directive.rule.tmpl.sinks) = true := by
  decide

theorem assertionCertificateRules_extract_exact :
    assertionCertificateRules.filterMap extractSupportedSourceExecFact =
      assertionCertificateDirectives := by
  rfl

private def ruleKinds : List String :=
  ["start", "formula-constant", "formula-variable", "formula-done",
   "hypothesis-floating", "hypothesis-essential", "hypothesis-done",
   "essential-constant", "essential-variable", "essential-done",
   "required-launch", "required-found", "required-missing",
   "required-done", "entry-launch", "entry-covered", "entry-extra",
   "entry-duplicate", "entry-unique", "entries-done"]

private def ruleVariables : List String :=
  ["certificate-rule-start", "certificate-rule-formula-constant",
   "certificate-rule-formula-variable", "certificate-rule-formula-done",
   "certificate-rule-hypothesis-floating",
   "certificate-rule-hypothesis-essential",
   "certificate-rule-hypothesis-done",
   "certificate-rule-essential-constant",
   "certificate-rule-essential-variable",
   "certificate-rule-essential-done",
   "certificate-rule-required-launch", "certificate-rule-required-found",
   "certificate-rule-required-missing", "certificate-rule-required-done",
   "certificate-rule-entry-launch", "certificate-rule-entry-covered",
   "certificate-rule-entry-extra", "certificate-rule-entry-duplicate",
   "certificate-rule-entry-unique", "certificate-rule-entries-done"]

def assertionCertificateRuleCaptureRow (kind : String) (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-rule",
      .symbol kind, rule]

private def assertionCertificateRuleCaptureTemplate
    (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-rule",
      .symbol kind, .var variableName]

def assertionCertificateRuleCaptureRows : List Atom :=
  List.zipWith assertionCertificateRuleCaptureRow ruleKinds
    assertionCertificateRules

private def reloadPatterns : List Atom :=
  reloadTriggerTemplate ::
    List.zipWith assertionCertificateRuleCaptureTemplate ruleKinds
      ruleVariables

private def reloadSinks : List Sink :=
  [.remove reloadTriggerTemplate] ++
    ruleVariables.map fun variableName => .add (.var variableName)

def assertionCertificateReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def assertionCertificateReloadDirective : SourceExecFact :=
  { atom := assertionCertificateReloadRule
    loc := reloadLocation
    rule :=
      { priority := 36
        name := "mm-source-assertion-certificate-reload"
        input := .compat (mkPattern reloadPatterns)
        guards := []
        tmpl := mkTemplate reloadSinks } }

theorem extract_assertionCertificateReloadRule_exact :
    extractSupportedSourceExecFact assertionCertificateReloadRule =
      some assertionCertificateReloadDirective := by
  rfl

def assertionCertificateReloadRuleCaptureRow : Atom :=
  assertionCertificateReloadCapabilityRow assertionCertificateReloadRule

/-! ## Focused semantic and executable controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "assertion-certificate.mm", start, stop }

private def fixtureName (name : String) (start stop : Nat) : LocatedName :=
  { span := fixtureSpan start stop, name }

private def fixtureStatement : RawStatement :=
  .axiomatic (fixtureSpan 0 2) (fixtureName "ax" 3 5)
    (fixtureName "wff" 6 9)
    [fixtureName "x" 10 11] (fixtureSpan 12 14)

private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff", body := [.var "x"] }

private def fixtureHypothesis : HypothesisView :=
  .essential "e1" { typecode := "wff", body := [.var "y"] }

private def fixtureAssertion : SourceAssertion :=
  { label := "ax"
    formula := fixtureFormula
    frame := { distinctVariables := [], hypothesisLabels := ["e1"] }
    hypotheses := [fixtureHypothesis] }

private def fixtureContext : AssertionFrameContext :=
  { position := 2
    nextPosition := 3
    statement := fixtureStatement
    assertionPosition := 0
    nextAssertionPosition := 1
    certificate := ["x", "y"]
    assertion := fixtureAssertion }

private def fixtureOwner : Atom := .symbol "assertion-certificate-source"

private def fixtureSnapshot : Atom :=
  assertionFrameSnapshotAtom fixtureOwner
    (listAtom hypothesisAtom [fixtureHypothesis])
    (listAtom stringPairAtom []) fixtureContext

private def fixtureFormulaControl (body occurrences : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-formula",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom [fixtureHypothesis], listAtom stringPairAtom [],
      body, occurrences, listAtom stringAtom fixtureContext.certificate]

private def fixtureRequiredControl (occurrences remaining : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-required",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom [fixtureHypothesis], listAtom stringPairAtom [],
      occurrences, remaining, listAtom stringAtom fixtureContext.certificate]

private def fixtureCertificateControl
    (occurrences certificate : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-entries",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom [fixtureHypothesis], listAtom stringPairAtom [],
      occurrences, certificate]

private def fixtureRequiredTicket (remaining target : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-required-ticket",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom [fixtureHypothesis], listAtom stringPairAtom [],
      listAtom stringAtom ["x", "y"], remaining,
      listAtom stringAtom fixtureContext.certificate, target]

private def fixtureDuplicateTicket (tail target : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-duplicate-ticket",
      fixtureOwner, assertionFrameContextAtom fixtureContext,
      listAtom hypothesisAtom [fixtureHypothesis], listAtom stringPairAtom [],
      listAtom stringAtom ["x", "y"], tail, target]

private def fixtureFault (reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-assertion-certificate-fault",
      fixtureOwner, assertionFrameContextAtom fixtureContext, reason, evidence]

private def startCanaryProgram : List Atom :=
  [assertionCertificateStartRule, assertionCertificateReloadRuleCaptureRow,
   fixtureSnapshot]

def startCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact startCanaryProgram
    assertionCertificateStartDirective

theorem startCanary_begins_from_checked_formula :
    fixtureFormulaControl (listAtom runtimeSymAtom fixtureFormula.body)
        nilTemplate ∈ startCanaryTarget := by
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

private def formulaVariableCanaryProgram : List Atom :=
  [assertionCertificateFormulaVariableRule,
   assertionCertificateReloadRuleCaptureRow,
   fixtureFormulaControl (listAtom runtimeSymAtom [.var "x"])
     nilTemplate]

theorem formulaVariableCanary_retains_occurrence :
    fixtureFormulaControl nilTemplate
        (listAtom stringAtom ["x"]) ∈
      cFireReflectiveSourceExecFact formulaVariableCanaryProgram
        assertionCertificateFormulaVariableDirective := by
  decide +kernel

private def requiredLaunchCanaryProgram : List Atom :=
  [assertionCertificateRequiredLaunchRule,
   assertionCertificateReloadRuleCaptureRow,
   membershipReloadRuleCaptureRow,
   fixtureRequiredControl (listAtom stringAtom ["x", "y"])
     (listAtom stringAtom ["x", "y"])]

theorem requiredLaunchCanary_queries_exact_certificate :
    membershipRequestRawAtom fixtureOwner
        (fixtureRequiredTicket (listAtom stringAtom ["y"])
          (stringAtom "x"))
        (stringAtom "x") nilTemplate
        (listAtom stringAtom ["x", "y"]) ∈
      cFireReflectiveSourceExecFact requiredLaunchCanaryProgram
        assertionCertificateRequiredLaunchDirective := by
  decide +kernel

private def duplicateTicketCanary : Atom :=
  fixtureDuplicateTicket (listAtom stringAtom ["x"])
    (stringAtom "x")

private def duplicateFoundCanaryProgram : List Atom :=
  [assertionCertificateEntryDuplicateRule,
   assertionCertificateReloadRuleCaptureRow,
   membershipFoundRawAtom fixtureOwner duplicateTicketCanary
     (stringAtom "x") nilTemplate nilTemplate]

theorem duplicateFoundCanary_emits_fault :
    fixtureFault (.symbol "duplicate-mandatory-variable")
        (stringAtom "x") ∈
      cFireReflectiveSourceExecFact duplicateFoundCanaryProgram
        assertionCertificateEntryDuplicateDirective := by
  decide +kernel

private def fixtureEvidence : AssertionCertificateEvidence :=
  { context := fixtureContext
    activeHypotheses := [fixtureHypothesis]
    activeDistinctVariables := []
    requiredOccurrences := ["y", "x"] }

private def doneCanaryProgram : List Atom :=
  [assertionCertificateEntriesDoneRule,
   assertionCertificateReloadRuleCaptureRow,
   assertionFrameSelectionReloadCapabilityRow
     (.symbol "frame-selection-reload-rule"),
   fixtureCertificateControl
     (listAtom stringAtom fixtureEvidence.requiredOccurrences) nilTemplate]

theorem doneCanary_emits_typed_evidence :
    assertionCertificateEvidenceAtom fixtureOwner fixtureEvidence ∈
      cFireReflectiveSourceExecFact doneCanaryProgram
        assertionCertificateEntriesDoneDirective := by
  decide +kernel

private def fixtureSemanticState : SourceState :=
  { initialState with activeHypotheses := [fixtureHypothesis] }

theorem fixture_finite_check_is_exact_certificate :
    certificateChecksOccurrences fixtureContext.certificate
        (requiredVariableOccurrences fixtureFormula
          fixtureSemanticState.activeHypotheses) = true /\
      MandatoryVariableCertificate fixtureSemanticState fixtureFormula
        fixtureContext.certificate := by
  constructor
  · decide +kernel
  · exact
      (certificateChecksRequiredOccurrences_iff fixtureSemanticState
        fixtureFormula fixtureContext.certificate).mp (by decide +kernel)

#print axioms decodeAssertionCertificateEvidenceAtom_encoded
#print axioms assertionCertificateEvidenceAtom_injective
#print axioms assertionCertificateDirectives_dataVariablesInherited
#print axioms assertionCertificateRules_extract_exact
#print axioms extract_assertionCertificateReloadRule_exact
#print axioms startCanary_begins_from_checked_formula
#print axioms startCanary_inhabits_exact_native_target
#print axioms formulaVariableCanary_retains_occurrence
#print axioms requiredLaunchCanary_queries_exact_certificate
#print axioms duplicateFoundCanary_emits_fault
#print axioms doneCanary_emits_typed_evidence
#print axioms fixture_finite_check_is_exact_certificate

end Mettapedia.Languages.Metamath.MM2SourceAssertionCertificateExecution
