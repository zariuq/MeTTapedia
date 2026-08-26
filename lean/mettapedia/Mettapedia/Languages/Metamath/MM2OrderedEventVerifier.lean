import Mettapedia.Languages.Metamath.MM2SourceEventTransformation
import Mettapedia.Languages.Metamath.MM2Target
import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Ordered Metamath event ingestion in ordinary MM2

This module begins the verifier-facing consumer of the source-data
transformation.  The first directive advances only from an exact linked
statement occurrence at the current source position.  It retains the complete
untrusted statement payload and the dispatch rule's captured bytes for the
later declaration/proof phase to validate and restart.

No source database row is trusted or pre-expanded here.  Statement-specific
rules extend this scheduled boundary and must re-establish the generic
dispatcher only after their checks finish.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2OrderedEventVerifier

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private def sourceBootstrapLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-source-bootstrap"]

private def sourceDispatchLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-source-event-dispatch"]

private def sourceTheoremStartLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-theorem-start"]

private def sourceTheoremSuccessLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-source-theorem-proof-success"]

private def sourceTheoremCommitLocation : Atom :=
  .expression [.symbol "34", .symbol "mm-source-theorem-commit"]

private def sourceBootstrapPatternAtoms : List Atom :=
  [.expression
      [.symbol "exec", sourceBootstrapLocation,
        .var "bootstrap-input", .var "bootstrap-output"],
   .expression [.symbol "mm-source-start", .var "source"]]

private def sourceBootstrapInput : Atom :=
  .expression (.symbol "," :: sourceBootstrapPatternAtoms)

private def sourceBootstrapStartTemplate : Atom :=
  .expression [.symbol "mm-source-start", .var "source"]

private def sourceBootstrapControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", natAtom 0]

private def sourceBootstrapEnvironmentTemplate : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "source",
      listAtom id [], natAtom 0, natAtom 0]

private def sourceBootstrapSinks : List Sink :=
  [.remove sourceBootstrapStartTemplate,
   .add sourceBootstrapControlTemplate,
   .add sourceBootstrapEnvironmentTemplate]

private def sourceBootstrapOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", sourceBootstrapStartTemplate],
      .expression [.symbol "+", sourceBootstrapControlTemplate],
      .expression [.symbol "+", sourceBootstrapEnvironmentTemplate]]

/-- The database-independent start marker to ordered-control transition. -/
def sourceEventBootstrapRule : Atom :=
  .expression
    [.symbol "exec", sourceBootstrapLocation,
      sourceBootstrapInput, sourceBootstrapOutput]

def sourceEventBootstrapDirective : SourceExecFact where
  atom := sourceEventBootstrapRule
  loc := sourceBootstrapLocation
  rule :=
    { priority := 0
      name := "mm-source-bootstrap"
      input := .compat (mkPattern sourceBootstrapPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceBootstrapSinks }

theorem extract_sourceEventBootstrapRule_exact :
    extractSupportedSourceExecFact sourceEventBootstrapRule =
      some sourceEventBootstrapDirective := by
  rfl

private def sourceDispatchPatternAtoms : List Atom :=
  [.expression
      [.symbol "exec", sourceDispatchLocation,
        .var "dispatch-input", .var "dispatch-output"],
   .expression
      [.symbol "mm-source-control", .var "source", .var "position"],
   .expression
      [.symbol "mm-linked-row", stringAtom "source-statement",
        .var "source", .var "position", .var "next-position",
        .var "statement"]]

private def sourceDispatchInput : Atom :=
  .expression (.symbol "," :: sourceDispatchPatternAtoms)

private def sourceDispatchControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "position"]

private def sourceCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", .var "statement",
      .var "dispatch-input", .var "dispatch-output"]

private def sourceDispatchSinks : List Sink :=
  [.remove sourceDispatchControlTemplate, .add sourceCurrentTemplate]

private def sourceDispatchOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", sourceDispatchControlTemplate],
      .expression [.symbol "+", sourceCurrentTemplate]]

/-- The database-independent ordered-event dispatcher. -/
def sourceEventDispatchRule : Atom :=
  .expression
    [.symbol "exec", sourceDispatchLocation,
      sourceDispatchInput, sourceDispatchOutput]

def sourceEventDispatchDirective : SourceExecFact where
  atom := sourceEventDispatchRule
  loc := sourceDispatchLocation
  rule :=
    { priority := 1
      name := "mm-source-event-dispatch"
      input := .compat (mkPattern sourceDispatchPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceDispatchSinks }

theorem extract_sourceEventDispatchRule_exact :
    extractSupportedSourceExecFact sourceEventDispatchRule =
      some sourceEventDispatchDirective := by
  rfl

/-! ## Conditional theorem admission -/

private def sourceTheoremStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem", .var "theorem-site",
      .var "theorem-label", .var "theorem-typecode",
      .var "theorem-body", .var "theorem-proof",
      .var "theorem-separator", .var "theorem-terminator"]

private def sourceTheoremCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", sourceTheoremStatementTemplate,
      .var "theorem-dispatch-input", .var "theorem-dispatch-output"]

private def sourceTheoremPendingTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-pending", .var "source",
      .var "position", .var "next-position",
      sourceTheoremStatementTemplate,
      .var "theorem-dispatch-input", .var "theorem-dispatch-output"]

private def sourceTheoremProofRequestTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", .var "source",
      .var "position", .var "next-position",
      sourceTheoremStatementTemplate]

private def sourceTheoremPreparedTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-prepared", .var "source",
      .var "position", .var "next-position",
      sourceTheoremStatementTemplate, .var "proof-owner",
      .var "proof-theorem-label", .var "proof-expected"]

private def sourceTheoremProofContextTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-context", .var "source",
      .var "position", .var "proof-owner", .var "proof-theorem-label",
      .var "proof-expected"]

private def sourceTheoremStartSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceTheoremStartLocation,
      .var "theorem-start-input", .var "theorem-start-output"]

private def sourceTheoremStartPatternAtoms : List Atom :=
  [sourceTheoremStartSelfTemplate, sourceTheoremCurrentTemplate,
   sourceTheoremPreparedTemplate]

private def sourceTheoremStartInput : Atom :=
  .expression (.symbol "," :: sourceTheoremStartPatternAtoms)

private def sourceTheoremStartSinks : List Sink :=
  [.add sourceTheoremStartSelfTemplate,
   .remove sourceTheoremCurrentTemplate,
   .remove sourceTheoremPreparedTemplate,
   .add sourceTheoremPendingTemplate,
   .add sourceTheoremProofRequestTemplate,
   .add sourceTheoremProofContextTemplate]

private def sourceTheoremStartOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceTheoremStartSelfTemplate],
      .expression [.symbol "-", sourceTheoremCurrentTemplate],
      .expression [.symbol "-", sourceTheoremPreparedTemplate],
      .expression [.symbol "+", sourceTheoremPendingTemplate],
      .expression [.symbol "+", sourceTheoremProofRequestTemplate],
      .expression [.symbol "+", sourceTheoremProofContextTemplate]]

/-- A `$p` occurrence becomes pending proof work only when its exact
proof-neutral prepared row is present.  This transition creates the private
proof context, but publishes no assertion index or source successor control. -/
def sourceTheoremStartRule : Atom :=
  .expression
    [.symbol "exec", sourceTheoremStartLocation,
      sourceTheoremStartInput, sourceTheoremStartOutput]

def sourceTheoremStartDirective : SourceExecFact where
  atom := sourceTheoremStartRule
  loc := sourceTheoremStartLocation
  rule :=
    { priority := 2
      name := "mm-source-theorem-start"
      input := .compat (mkPattern sourceTheoremStartPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceTheoremStartSinks }

theorem extract_sourceTheoremStartRule_exact :
    extractSupportedSourceExecFact sourceTheoremStartRule =
      some sourceTheoremStartDirective := by
  rfl

/-! ### Normal-proof success continuation -/

private def sourceTheoremSuccessSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceTheoremSuccessLocation,
      .var "theorem-success-input", .var "theorem-success-output"]

private def sourceTheoremAcceptedTemplate : Atom :=
  .expression
    [.symbol "mm-accepted", .var "source", .var "proof-owner",
      .var "proof-theorem-label", .var "proof-expected",
      .var "proof-occurrence"]

private def sourceTheoremSuccessTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-succeeded", .var "source",
      .var "position", .var "proof-occurrence"]

private def sourceTheoremSuccessPatternAtoms : List Atom :=
  [sourceTheoremSuccessSelfTemplate, sourceTheoremProofContextTemplate,
   sourceTheoremAcceptedTemplate]

private def sourceTheoremSuccessInput : Atom :=
  .expression (.symbol "," :: sourceTheoremSuccessPatternAtoms)

private def sourceTheoremSuccessSinks : List Sink :=
  [.add sourceTheoremSuccessSelfTemplate,
   .remove sourceTheoremProofContextTemplate,
   .remove sourceTheoremAcceptedTemplate,
   .add sourceTheoremSuccessTemplate]

private def sourceTheoremSuccessOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceTheoremSuccessSelfTemplate],
      .expression [.symbol "-", sourceTheoremProofContextTemplate],
      .expression [.symbol "-", sourceTheoremAcceptedTemplate],
      .expression [.symbol "+", sourceTheoremSuccessTemplate]]

/-- Bridge from the normal proof machine's exact terminal observation to the
private proof-success occurrence consumed by conditional theorem admission.
The proof context is verifier-owned and is not part of admitted source input. -/
def sourceTheoremSuccessRule : Atom :=
  .expression
    [.symbol "exec", sourceTheoremSuccessLocation,
      sourceTheoremSuccessInput, sourceTheoremSuccessOutput]

def sourceTheoremSuccessDirective : SourceExecFact where
  atom := sourceTheoremSuccessRule
  loc := sourceTheoremSuccessLocation
  rule :=
    { priority := 33
      name := "mm-source-theorem-proof-success"
      input := .compat (mkPattern sourceTheoremSuccessPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceTheoremSuccessSinks }

theorem extract_sourceTheoremSuccessRule_exact :
    extractSupportedSourceExecFact sourceTheoremSuccessRule =
      some sourceTheoremSuccessDirective := by
  rfl

private def sourceTheoremCommitSelfTemplate : Atom :=
  .expression
    [.symbol "exec", sourceTheoremCommitLocation,
      .var "theorem-commit-input", .var "theorem-commit-output"]

private def sourceTheoremSucceededTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-succeeded", .var "source",
      .var "position", .var "proof-occurrence"]

private def sourceTheoremPreparedAssertionHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-assertion-header", .var "source",
      .var "position",
      .expression
        [.symbol "mm-source-proof-owner", .var "source", .var "position"],
      .var "assertion-header"]

private def sourceTheoremAdmittedTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-admitted", .var "source",
      .var "position", sourceTheoremStatementTemplate,
      .var "proof-occurrence"]

private def sourceTheoremNextControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def sourceTheoremRestoredDispatchTemplate : Atom :=
  .expression
    [.symbol "exec", sourceDispatchLocation,
      .var "theorem-dispatch-input", .var "theorem-dispatch-output"]

private def sourceTheoremCommitPatternAtoms : List Atom :=
  [sourceTheoremCommitSelfTemplate, sourceTheoremPendingTemplate,
   sourceTheoremSucceededTemplate,
   sourceTheoremPreparedAssertionHeaderTemplate]

private def sourceTheoremCommitInput : Atom :=
  .expression (.symbol "," :: sourceTheoremCommitPatternAtoms)

private def sourceTheoremCommitSinks : List Sink :=
  [.add sourceTheoremCommitSelfTemplate,
   .remove sourceTheoremPendingTemplate,
   .remove sourceTheoremSucceededTemplate,
   .remove sourceTheoremPreparedAssertionHeaderTemplate,
   .add (.var "assertion-header"),
   .add sourceTheoremAdmittedTemplate,
   .add sourceTheoremRestoredDispatchTemplate,
   .add sourceTheoremNextControlTemplate]

private def sourceTheoremCommitOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", sourceTheoremCommitSelfTemplate],
      .expression [.symbol "-", sourceTheoremPendingTemplate],
      .expression [.symbol "-", sourceTheoremSucceededTemplate],
      .expression
        [.symbol "-", sourceTheoremPreparedAssertionHeaderTemplate],
      .expression [.symbol "+", .var "assertion-header"],
      .expression [.symbol "+", sourceTheoremAdmittedTemplate],
      .expression [.symbol "+", sourceTheoremRestoredDispatchTemplate],
      .expression [.symbol "+", sourceTheoremNextControlTemplate]]

/-- Admission is a separate continuation whose required proof-success fact
can only be produced by the proof machine in an admitted initial space. -/
def sourceTheoremCommitRule : Atom :=
  .expression
    [.symbol "exec", sourceTheoremCommitLocation,
      sourceTheoremCommitInput, sourceTheoremCommitOutput]

def sourceTheoremCommitDirective : SourceExecFact where
  atom := sourceTheoremCommitRule
  loc := sourceTheoremCommitLocation
  rule :=
    { priority := 34
      name := "mm-source-theorem-commit"
      input := .compat (mkPattern sourceTheoremCommitPatternAtoms)
      guards := []
      tmpl := mkTemplate sourceTheoremCommitSinks }

theorem extract_sourceTheoremCommitRule_exact :
    extractSupportedSourceExecFact sourceTheoremCommitRule =
      some sourceTheoremCommitDirective := by
  rfl

def sourceControlAtom (owner : Atom) (position : Nat) : Atom :=
  .expression
    [.symbol "mm-source-control", owner, natAtom position]

def sourceEnvironmentAtom (owner scopeStack : Atom)
    (nextHypothesis nextAssertion : Nat) : Atom :=
  .expression
    [.symbol "mm-source-environment", owner, scopeStack,
      natAtom nextHypothesis, natAtom nextAssertion]

def sourceInitialEnvironmentAtom (owner : Atom) : Atom :=
  sourceEnvironmentAtom owner (listAtom id []) 0 0

def sourceCurrentAtom (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) : Atom :=
  .expression
    [.symbol "mm-source-current", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement,
      sourceDispatchInput, sourceDispatchOutput]

def sourceTheoremPendingAtom (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) : Atom :=
  .expression
    [.symbol "mm-source-theorem-pending", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement,
      sourceDispatchInput, sourceDispatchOutput]

def sourceTheoremProofRequestAtom (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement]

def sourceTheoremProofSucceededAtom (owner : Atom) (position : Nat)
    (proofOccurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-succeeded", owner,
      natAtom position, proofOccurrence]

def sourceTheoremProofOwnerAtom (owner : Atom) (position : Nat) : Atom :=
  sourceProofOwnerAtom owner position

def sourceTheoremProofContextAtom (owner : Atom) (position : Nat)
    (theoremLabel expected : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-context", owner, natAtom position,
      sourceTheoremProofOwnerAtom owner position, theoremLabel, expected]

def sourceTheoremNormalAcceptedAtom (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-accepted", owner, sourceTheoremProofOwnerAtom owner position,
      theoremLabel, expected, proofOccurrence]

def sourceTheoremAdmittedAtom (owner : Atom) (position : Nat)
    (statement : RawStatement) (proofOccurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-admitted", owner, natAtom position,
      rawStatementAtom statement, proofOccurrence]

private def sourceProvableStatement (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) : RawStatement :=
  .provable site label typecode body proof separator terminator

def sourceTheoremStartPhaseAtoms (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) : List Atom :=
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  [sourceTheoremStartRule,
   sourceCurrentAtom owner position nextPosition statement,
   sourcePreparedTheoremFact owner position nextPosition statement
    (sourceTheoremProofOwnerAtom owner position) theoremLabel expected]

def sourceTheoremStartPhaseSpace (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) : Space :=
  (sourceTheoremStartPhaseAtoms owner position nextPosition site separator
    terminator label typecode body proof theoremLabel expected).toFinset

/-- The raw current theorem and executable rule without the decoder-derived
prepared row.  This is the direct-input forgery control for theorem start. -/
def sourceTheoremStartUnpreparedPhaseSpace (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) : Space :=
  ({sourceTheoremStartRule,
    sourceCurrentAtom owner position nextPosition
      (sourceProvableStatement site separator terminator label typecode body
        proof)} : Finset Atom)

def sourceTheoremSuccessPhaseAtoms (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) : List Atom :=
  [sourceTheoremSuccessRule,
   sourceTheoremProofContextAtom owner position theoremLabel expected,
   sourceTheoremNormalAcceptedAtom owner position theoremLabel expected
    proofOccurrence]

def sourceTheoremSuccessPhaseSpace (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) : Space :=
  (sourceTheoremSuccessPhaseAtoms owner position theoremLabel expected
    proofOccurrence).toFinset

def sourceTheoremCommitPhaseAtoms (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  [sourceTheoremCommitRule,
   sourceTheoremPendingAtom owner position nextPosition statement,
   sourceTheoremProofSucceededAtom owner position proofOccurrence,
   sourcePreparedAssertionHeaderFact owner position
    (assertionHeaderRow owner assertionPosition assertion)]

def sourceTheoremCommitPhaseSpace (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  (sourceTheoremCommitPhaseAtoms owner position nextPosition site separator
    terminator label typecode body proof proofOccurrence assertionPosition
    assertion).toFinset

/-- The commit continuation before proof success exists.  It deliberately
contains no proof-success atom and therefore has no complete match row. -/
def sourceTheoremCommitBlockedPhaseSpace (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  [sourceTheoremCommitRule,
    sourceTheoremPendingAtom owner position nextPosition statement,
    sourcePreparedAssertionHeaderFact owner position
      (assertionHeaderRow owner assertionPosition assertion)].toFinset

def sourceBootstrapPhaseAtoms (owner : Atom) : List Atom :=
  [sourceEventBootstrapRule, sourceEventStartRow owner]

def sourceBootstrapPhaseSpace (owner : Atom) : Space :=
  (sourceBootstrapPhaseAtoms owner).toFinset

private theorem sourceBootstrapPhaseAtoms_nodup (owner : Atom) :
    (sourceBootstrapPhaseAtoms owner).Nodup := by
  simp [sourceBootstrapPhaseAtoms, sourceEventBootstrapRule,
    sourceEventStartRow]

private theorem sourceBootstrapPhaseAtoms_supported (owner : Atom) :
    cSupportedSourceExecFacts (sourceBootstrapPhaseAtoms owner) =
      [sourceEventBootstrapDirective] := by
  rfl

theorem sourceBootstrapPhase_selects_directive (owner : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace (sourceBootstrapPhaseSpace owner)) =
      some sourceEventBootstrapDirective := by
  let atoms := sourceBootstrapPhaseAtoms owner
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some sourceEventBootstrapDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    sourceEventBootstrapDirective
    (sourceBootstrapPhaseAtoms_nodup owner)
    (sourceBootstrapPhaseAtoms_supported owner)

def sourceDispatchPhaseAtoms (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) : List Atom :=
  [sourceEventDispatchRule, sourceControlAtom owner position,
   linkedRow "source-statement" owner position nextPosition
    (rawStatementAtom statement)]

def sourceDispatchPhaseSpace (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) : Space :=
  (sourceDispatchPhaseAtoms owner position nextPosition statement).toFinset

private theorem sourceDispatchPhaseAtoms_nodup (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    (sourceDispatchPhaseAtoms owner position nextPosition statement).Nodup := by
  simp [sourceDispatchPhaseAtoms, sourceEventDispatchRule,
    sourceControlAtom, linkedRow]

private theorem sourceDispatchPhaseAtoms_supported (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    cSupportedSourceExecFacts
        (sourceDispatchPhaseAtoms owner position nextPosition statement) =
      [sourceEventDispatchDirective] := by
  rfl

theorem sourceDispatchPhase_selects_directive (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (sourceDispatchPhaseSpace owner position nextPosition statement)) =
      some sourceEventDispatchDirective := by
  let atoms := sourceDispatchPhaseAtoms owner position nextPosition statement
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some sourceEventDispatchDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    sourceEventDispatchDirective
    (sourceDispatchPhaseAtoms_nodup owner position nextPosition statement)
    (sourceDispatchPhaseAtoms_supported owner position nextPosition statement)

private theorem sourceTheoremStartPhaseAtoms_nodup (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    (sourceTheoremStartPhaseAtoms owner position nextPosition site separator
      terminator label typecode body proof theoremLabel expected).Nodup := by
  simp [sourceTheoremStartPhaseAtoms, sourceTheoremStartRule,
    sourceCurrentAtom, sourcePreparedTheoremFact, sourceTheoremProofOwnerAtom,
    sourceProofOwnerAtom, sourceProvableStatement, rawStatementAtom]

private theorem sourceTheoremStartPhaseAtoms_supported (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    cSupportedSourceExecFacts
        (sourceTheoremStartPhaseAtoms owner position nextPosition site separator
          terminator label typecode body proof theoremLabel expected) =
      [sourceTheoremStartDirective] := by
  rfl

theorem sourceTheoremStartPhase_selects_directive (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (sourceTheoremStartPhaseSpace owner position nextPosition site
            separator terminator label typecode body proof theoremLabel
            expected)) =
      some sourceTheoremStartDirective := by
  let atoms := sourceTheoremStartPhaseAtoms owner position nextPosition site
    separator terminator label typecode body proof theoremLabel expected
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some sourceTheoremStartDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    sourceTheoremStartDirective
    (sourceTheoremStartPhaseAtoms_nodup owner position nextPosition site
      separator terminator label typecode body proof theoremLabel expected)
    (sourceTheoremStartPhaseAtoms_supported owner position nextPosition site
      separator terminator label typecode body proof theoremLabel expected)

private theorem sourceTheoremSuccessPhaseAtoms_nodup (owner : Atom)
    (position : Nat) (theoremLabel expected proofOccurrence : Atom) :
    (sourceTheoremSuccessPhaseAtoms owner position theoremLabel expected
      proofOccurrence).Nodup := by
  simp [sourceTheoremSuccessPhaseAtoms, sourceTheoremSuccessRule,
    sourceTheoremProofContextAtom, sourceTheoremNormalAcceptedAtom]

private theorem sourceTheoremSuccessPhaseAtoms_supported (owner : Atom)
    (position : Nat) (theoremLabel expected proofOccurrence : Atom) :
    cSupportedSourceExecFacts
        (sourceTheoremSuccessPhaseAtoms owner position theoremLabel expected
          proofOccurrence) =
      [sourceTheoremSuccessDirective] := by
  rfl

theorem sourceTheoremSuccessPhase_selects_directive (owner : Atom)
    (position : Nat) (theoremLabel expected proofOccurrence : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (sourceTheoremSuccessPhaseSpace owner position theoremLabel expected
            proofOccurrence)) =
      some sourceTheoremSuccessDirective := by
  let atoms := sourceTheoremSuccessPhaseAtoms owner position theoremLabel
    expected proofOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some sourceTheoremSuccessDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    sourceTheoremSuccessDirective
    (sourceTheoremSuccessPhaseAtoms_nodup owner position theoremLabel expected
      proofOccurrence)
    (sourceTheoremSuccessPhaseAtoms_supported owner position theoremLabel
      expected proofOccurrence)

private theorem sourceTheoremCommitPhaseAtoms_nodup (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    (sourceTheoremCommitPhaseAtoms owner position nextPosition site separator
      terminator label typecode body proof proofOccurrence
      assertionPosition assertion).Nodup := by
  cases assertion
  simp [sourceTheoremCommitPhaseAtoms, sourceTheoremCommitRule,
    sourceTheoremPendingAtom, sourceTheoremProofSucceededAtom,
    sourcePreparedAssertionHeaderFact, sourceProofOwnerAtom, assertionHeaderRow,
    sourceProvableStatement, rawStatementAtom]

private theorem sourceTheoremCommitPhaseAtoms_supported (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (sourceTheoremCommitPhaseAtoms owner position nextPosition site
          separator terminator label typecode body proof proofOccurrence
          assertionPosition assertion) =
      [sourceTheoremCommitDirective] := by
  rfl

theorem sourceTheoremCommitPhase_selects_directive (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (sourceTheoremCommitPhaseSpace owner position nextPosition site
            separator terminator label typecode body proof proofOccurrence
            assertionPosition assertion)) =
      some sourceTheoremCommitDirective := by
  let atoms := sourceTheoremCommitPhaseAtoms owner position nextPosition site
    separator terminator label typecode body proof proofOccurrence
    assertionPosition assertion
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some sourceTheoremCommitDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    sourceTheoremCommitDirective
    (sourceTheoremCommitPhaseAtoms_nodup owner position nextPosition site
      separator terminator label typecode body proof proofOccurrence
      assertionPosition assertion)
    (sourceTheoremCommitPhaseAtoms_supported owner position nextPosition site
      separator terminator label typecode body proof proofOccurrence
      assertionPosition assertion)

private def sourceTheoremStartSubstitution (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) : Subst :=
  [("proof-expected", expected), ("proof-theorem-label", theoremLabel),
   ("proof-owner", sourceTheoremProofOwnerAtom owner position),
   ("theorem-dispatch-output", sourceDispatchOutput),
   ("theorem-dispatch-input", sourceDispatchInput),
   ("theorem-terminator", locatedByteSpanAtom terminator),
   ("theorem-separator", locatedByteSpanAtom separator),
   ("theorem-proof", proofPayloadAtom proof),
   ("theorem-body", listAtom locatedNameAtom body),
   ("theorem-typecode", locatedNameAtom typecode),
   ("theorem-label", locatedNameAtom label),
   ("theorem-site", locatedByteSpanAtom site),
   ("next-position", natAtom nextPosition),
   ("position", natAtom position), ("source", owner),
   ("theorem-start-output", sourceTheoremStartOutput),
   ("theorem-start-input", sourceTheoremStartInput)]

private theorem sourceTheoremStartMatchRow_mem (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    sourceTheoremStartSubstitution owner position nextPosition site separator
        terminator label typecode body proof theoremLabel expected ∈
      (matchInputSpec []
        (readCopyAtom
          (sourceTheoremStartPhaseSpace owner position nextPosition site
            separator terminator label typecode body proof theoremLabel
            expected)
          sourceTheoremStartRule)
        sourceTheoremStartDirective.rule.input).map Prod.fst := by
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let current := sourceCurrentAtom owner position nextPosition statement
  let prepared := sourcePreparedTheoremFact owner position nextPosition
    statement (sourceTheoremProofOwnerAtom owner position) theoremLabel expected
  let read := readCopyAtom
    (sourceTheoremStartPhaseSpace owner position nextPosition site separator
      terminator label typecode body proof theoremLabel expected)
    sourceTheoremStartRule
  let afterSelf : Subst :=
    [("theorem-start-output", sourceTheoremStartOutput),
     ("theorem-start-input", sourceTheoremStartInput)]
  let finalRow := sourceTheoremStartSubstitution owner position nextPosition
    site separator terminator label typecode body proof theoremLabel expected
  have readMember (atom : Atom)
      (member : atom ∈ sourceTheoremStartPhaseSpace owner position nextPosition
        site separator terminator label typecode body proof theoremLabel
        expected) : atom ∈ read := by
    by_cases equal : atom = sourceTheoremStartRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : sourceTheoremStartRule ∈ read := by
    apply readMember
    simp [sourceTheoremStartPhaseSpace, sourceTheoremStartPhaseAtoms]
  have currentMem : current ∈ read := by
    apply readMember
    simp [current, statement, sourceTheoremStartPhaseSpace,
      sourceTheoremStartPhaseAtoms]
  have preparedMem : prepared ∈ read := by
    apply readMember
    simp [prepared, statement, sourceTheoremStartPhaseSpace,
      sourceTheoremStartPhaseAtoms]
  have matchSelf :
      matchAtom [] sourceTheoremStartSelfTemplate sourceTheoremStartRule =
        some afterSelf := by
    simp [sourceTheoremStartSelfTemplate, sourceTheoremStartRule,
      sourceTheoremStartInput, sourceTheoremStartOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, sourceTheoremStartLocation]
  have matchCurrent :
      ∃ afterCurrent,
        matchAtom afterSelf sourceTheoremCurrentTemplate current =
          some afterCurrent ∧
        matchAtom afterCurrent sourceTheoremPreparedTemplate prepared =
          some finalRow := by
    let afterCurrent : Subst :=
      [("theorem-dispatch-output", sourceDispatchOutput),
       ("theorem-dispatch-input", sourceDispatchInput),
       ("theorem-terminator", locatedByteSpanAtom terminator),
       ("theorem-separator", locatedByteSpanAtom separator),
       ("theorem-proof", proofPayloadAtom proof),
       ("theorem-body", listAtom locatedNameAtom body),
       ("theorem-typecode", locatedNameAtom typecode),
       ("theorem-label", locatedNameAtom label),
       ("theorem-site", locatedByteSpanAtom site),
       ("next-position", natAtom nextPosition),
       ("position", natAtom position), ("source", owner),
       ("theorem-start-output", sourceTheoremStartOutput),
       ("theorem-start-input", sourceTheoremStartInput)]
    refine ⟨afterCurrent, ?_, ?_⟩
    · simp [sourceTheoremCurrentTemplate, sourceTheoremStatementTemplate,
        current, statement, sourceCurrentAtom, sourceProvableStatement,
        rawStatementAtom, afterSelf, afterCurrent, matchAtom,
        matchAtom.matchAtomList, Subst.lookup]
    · simp [sourceTheoremPreparedTemplate, prepared,
        sourcePreparedTheoremFact, sourceTheoremProofOwnerAtom,
        sourceProofOwnerAtom, sourceTheoremStatementTemplate, statement,
        sourceProvableStatement, rawStatementAtom, afterCurrent, finalRow,
        sourceTheoremStartSubstitution, matchAtom, matchAtom.matchAtomList,
        Subst.lookup]
  obtain ⟨afterCurrent, matchCurrent, matchPrepared⟩ := matchCurrent
  rw [List.mem_map]
  refine ⟨(finalRow, {sourceTheoremStartRule, current, prepared}), ?_, rfl⟩
  simp only [sourceTheoremStartDirective, matchInputSpec,
    sourceTheoremStartPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, sourceTheoremStartRule),
    matchOneInSpace_mem [] _ read sourceTheoremStartRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterCurrent, current),
    matchOneInSpace_mem afterSelf _ read current currentMem afterCurrent
      matchCurrent, ?_⟩
  refine ⟨(finalRow, prepared),
    matchOneInSpace_mem afterCurrent _ read prepared preparedMem finalRow
      matchPrepared, ?_⟩
  simp [finalRow, current, prepared]

private def sourceTheoremSuccessSubstitution (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) : Subst :=
  [("proof-occurrence", proofOccurrence), ("proof-expected", expected),
   ("proof-theorem-label", theoremLabel),
   ("proof-owner", sourceTheoremProofOwnerAtom owner position),
   ("position", natAtom position), ("source", owner),
   ("theorem-success-output", sourceTheoremSuccessOutput),
   ("theorem-success-input", sourceTheoremSuccessInput)]

private theorem sourceTheoremSuccessMatchRow_mem (owner : Atom)
    (position : Nat) (theoremLabel expected proofOccurrence : Atom) :
    sourceTheoremSuccessSubstitution owner position theoremLabel expected
        proofOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (sourceTheoremSuccessPhaseSpace owner position theoremLabel expected
            proofOccurrence)
          sourceTheoremSuccessRule)
        sourceTheoremSuccessDirective.rule.input).map Prod.fst := by
  let context := sourceTheoremProofContextAtom owner position theoremLabel
    expected
  let accepted := sourceTheoremNormalAcceptedAtom owner position theoremLabel
    expected proofOccurrence
  let read := readCopyAtom
    (sourceTheoremSuccessPhaseSpace owner position theoremLabel expected
      proofOccurrence)
    sourceTheoremSuccessRule
  let afterSelf : Subst :=
    [("theorem-success-output", sourceTheoremSuccessOutput),
     ("theorem-success-input", sourceTheoremSuccessInput)]
  let afterContext : Subst :=
    [("proof-expected", expected),
     ("proof-theorem-label", theoremLabel),
     ("proof-owner", sourceTheoremProofOwnerAtom owner position),
     ("position", natAtom position), ("source", owner),
     ("theorem-success-output", sourceTheoremSuccessOutput),
     ("theorem-success-input", sourceTheoremSuccessInput)]
  let finalRow := sourceTheoremSuccessSubstitution owner position theoremLabel
    expected proofOccurrence
  have readMember (atom : Atom)
      (member : atom ∈ sourceTheoremSuccessPhaseSpace owner position
        theoremLabel expected proofOccurrence) : atom ∈ read := by
    by_cases equal : atom = sourceTheoremSuccessRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : sourceTheoremSuccessRule ∈ read := by
    apply readMember
    simp [sourceTheoremSuccessPhaseSpace, sourceTheoremSuccessPhaseAtoms]
  have contextMem : context ∈ read := by
    apply readMember
    simp [context, sourceTheoremSuccessPhaseSpace,
      sourceTheoremSuccessPhaseAtoms]
  have acceptedMem : accepted ∈ read := by
    apply readMember
    simp [accepted, sourceTheoremSuccessPhaseSpace,
      sourceTheoremSuccessPhaseAtoms]
  have matchSelf :
      matchAtom [] sourceTheoremSuccessSelfTemplate
          sourceTheoremSuccessRule = some afterSelf := by
    simp [sourceTheoremSuccessSelfTemplate, sourceTheoremSuccessRule,
      sourceTheoremSuccessInput, sourceTheoremSuccessOutput, afterSelf,
      sourceTheoremSuccessLocation, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchContext :
      matchAtom afterSelf sourceTheoremProofContextTemplate context =
        some afterContext := by
    simp [sourceTheoremProofContextTemplate, context,
      sourceTheoremProofContextAtom, afterSelf, afterContext, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchAccepted :
      matchAtom afterContext sourceTheoremAcceptedTemplate accepted =
        some finalRow := by
    simp [sourceTheoremAcceptedTemplate, accepted,
      sourceTheoremNormalAcceptedAtom, afterContext, finalRow,
      sourceTheoremSuccessSubstitution, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {sourceTheoremSuccessRule, context, accepted}), ?_, rfl⟩
  simp only [sourceTheoremSuccessDirective, matchInputSpec,
    sourceTheoremSuccessPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, sourceTheoremSuccessRule),
    matchOneInSpace_mem [] _ read sourceTheoremSuccessRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterContext, context),
    matchOneInSpace_mem afterSelf _ read context contextMem afterContext
      matchContext, ?_⟩
  refine ⟨(finalRow, accepted),
    matchOneInSpace_mem afterContext _ read accepted acceptedMem finalRow
      matchAccepted, ?_⟩
  simp [finalRow, context, accepted]

private def sourceTheoremCommitSubstitution (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) : Subst :=
  [("assertion-header", assertionHeaderRow owner assertionPosition assertion),
   ("proof-occurrence", proofOccurrence),
   ("theorem-dispatch-output", sourceDispatchOutput),
   ("theorem-dispatch-input", sourceDispatchInput),
   ("theorem-terminator", locatedByteSpanAtom terminator),
   ("theorem-separator", locatedByteSpanAtom separator),
   ("theorem-proof", proofPayloadAtom proof),
   ("theorem-body", listAtom locatedNameAtom body),
   ("theorem-typecode", locatedNameAtom typecode),
   ("theorem-label", locatedNameAtom label),
   ("theorem-site", locatedByteSpanAtom site),
   ("next-position", natAtom nextPosition),
   ("position", natAtom position), ("source", owner),
   ("theorem-commit-output", sourceTheoremCommitOutput),
   ("theorem-commit-input", sourceTheoremCommitInput)]

private theorem sourceTheoremCommitMatchRow_mem (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    sourceTheoremCommitSubstitution owner position nextPosition site separator
        terminator label typecode body proof proofOccurrence assertionPosition
        assertion ∈
      (matchInputSpec []
        (readCopyAtom
          (sourceTheoremCommitPhaseSpace owner position nextPosition site
            separator terminator label typecode body proof proofOccurrence
            assertionPosition assertion)
          sourceTheoremCommitRule)
        sourceTheoremCommitDirective.rule.input).map Prod.fst := by
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let pending := sourceTheoremPendingAtom owner position nextPosition statement
  let succeeded := sourceTheoremProofSucceededAtom owner position proofOccurrence
  let preparedHeader := sourcePreparedAssertionHeaderFact owner position
    (assertionHeaderRow owner assertionPosition assertion)
  let read := readCopyAtom
    (sourceTheoremCommitPhaseSpace owner position nextPosition site separator
      terminator label typecode body proof proofOccurrence assertionPosition
      assertion)
    sourceTheoremCommitRule
  let afterSelf : Subst :=
    [("theorem-commit-output", sourceTheoremCommitOutput),
     ("theorem-commit-input", sourceTheoremCommitInput)]
  let afterPending : Subst :=
    [("theorem-dispatch-output", sourceDispatchOutput),
     ("theorem-dispatch-input", sourceDispatchInput),
     ("theorem-terminator", locatedByteSpanAtom terminator),
     ("theorem-separator", locatedByteSpanAtom separator),
     ("theorem-proof", proofPayloadAtom proof),
     ("theorem-body", listAtom locatedNameAtom body),
     ("theorem-typecode", locatedNameAtom typecode),
     ("theorem-label", locatedNameAtom label),
     ("theorem-site", locatedByteSpanAtom site),
     ("next-position", natAtom nextPosition),
     ("position", natAtom position), ("source", owner),
     ("theorem-commit-output", sourceTheoremCommitOutput),
     ("theorem-commit-input", sourceTheoremCommitInput)]
  let afterSucceeded : Subst :=
    [("proof-occurrence", proofOccurrence)] ++ afterPending
  let finalRow := sourceTheoremCommitSubstitution owner position nextPosition
    site separator terminator label typecode body proof proofOccurrence
    assertionPosition assertion
  have readMember (atom : Atom)
      (member : atom ∈ sourceTheoremCommitPhaseSpace owner position nextPosition
        site separator terminator label typecode body proof proofOccurrence
        assertionPosition assertion) :
      atom ∈ read := by
    by_cases equal : atom = sourceTheoremCommitRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : sourceTheoremCommitRule ∈ read := by
    apply readMember
    simp [sourceTheoremCommitPhaseSpace, sourceTheoremCommitPhaseAtoms]
  have pendingMem : pending ∈ read := by
    apply readMember
    simp [pending, statement, sourceTheoremCommitPhaseSpace,
      sourceTheoremCommitPhaseAtoms]
  have succeededMem : succeeded ∈ read := by
    apply readMember
    simp [succeeded, sourceTheoremCommitPhaseSpace,
      sourceTheoremCommitPhaseAtoms]
  have preparedHeaderMem : preparedHeader ∈ read := by
    apply readMember
    simp [preparedHeader, sourceTheoremCommitPhaseSpace,
      sourceTheoremCommitPhaseAtoms]
  have matchSelf :
      matchAtom [] sourceTheoremCommitSelfTemplate sourceTheoremCommitRule =
        some afterSelf := by
    simp [sourceTheoremCommitSelfTemplate, sourceTheoremCommitRule,
      sourceTheoremCommitInput, sourceTheoremCommitOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, sourceTheoremCommitLocation]
  have matchPending :
      matchAtom afterSelf sourceTheoremPendingTemplate pending =
        some afterPending := by
    simp [sourceTheoremPendingTemplate, sourceTheoremStatementTemplate,
      pending, statement, sourceTheoremPendingAtom, sourceProvableStatement,
      rawStatementAtom, afterSelf, afterPending, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchSucceeded :
      matchAtom afterPending sourceTheoremSucceededTemplate succeeded =
        some afterSucceeded := by
    simp [sourceTheoremSucceededTemplate, succeeded,
      sourceTheoremProofSucceededAtom, afterPending, afterSucceeded,
      matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchPreparedHeader :
      matchAtom afterSucceeded sourceTheoremPreparedAssertionHeaderTemplate
          preparedHeader = some finalRow := by
    cases assertion
    simp [sourceTheoremPreparedAssertionHeaderTemplate, preparedHeader,
      sourcePreparedAssertionHeaderFact, sourceProofOwnerAtom,
      assertionHeaderRow, afterSucceeded, afterPending, finalRow,
      sourceTheoremCommitSubstitution, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
      {sourceTheoremCommitRule, pending, succeeded, preparedHeader}), ?_, rfl⟩
  simp only [sourceTheoremCommitDirective, matchInputSpec,
    sourceTheoremCommitPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, sourceTheoremCommitRule),
    matchOneInSpace_mem [] _ read sourceTheoremCommitRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterPending, pending),
    matchOneInSpace_mem afterSelf _ read pending pendingMem afterPending
      matchPending, ?_⟩
  refine ⟨(afterSucceeded, succeeded),
    matchOneInSpace_mem afterPending _ read succeeded succeededMem
      afterSucceeded
      matchSucceeded, ?_⟩
  refine ⟨(finalRow, preparedHeader),
    matchOneInSpace_mem afterSucceeded _ read preparedHeader preparedHeaderMem
      finalRow matchPreparedHeader, ?_⟩
  simp [finalRow, pending, succeeded]

private theorem stageAdd_contains_of_row
    (rows : List Subst) (substitution : Subst) (template candidate : Atom)
    (rowMember : substitution ∈ rows)
    (instantiates : instantiateTemplateAtom? substitution template =
      some candidate) :
    candidate ∈ rows.foldl
      (stageReflectiveSupportSink (.add template)) [] := by
  have stagePreserves : ∀ (remaining : List Subst) (staged : List Atom),
      candidate ∈ staged →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged := by
    intro remaining
    induction remaining with
    | nil =>
        intro staged member
        exact member
    | cons head tail induction =>
        intro staged member
        apply induction
        simp only [stageReflectiveSupportSink, Sink.atom]
        split
        · exact member
        · simp only [insertSupport]
          split
          · exact member
          · exact List.mem_append_left _ member
  suffices containsOfRow : ∀ (remaining : List Subst) (staged : List Atom),
      substitution ∈ remaining →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged by
    exact containsOfRow rows [] rowMember
  intro remaining
  induction remaining with
  | nil =>
      intro staged member
      simp at member
  | cons head tail induction =>
      intro staged member
      simp only [List.mem_cons] at member
      simp only [List.foldl_cons]
      rcases member with rfl | member
      · apply stagePreserves tail
          (stageReflectiveSupportSink (.add template) staged substitution)
        simp only [stageReflectiveSupportSink, Sink.atom]
        rw [instantiates]
        by_cases present : candidate ∈ staged
        · simp [insertSupport, present]
        · simp [insertSupport, present]
      · exact induction
          (stageReflectiveSupportSink (.add template) staged head) member

private def sourceBootstrapSubstitution (owner : Atom) : Subst :=
  [("source", owner),
   ("bootstrap-output", sourceBootstrapOutput),
   ("bootstrap-input", sourceBootstrapInput)]

private theorem sourceBootstrapMatchRow_mem (owner : Atom) :
    sourceBootstrapSubstitution owner ∈
      (matchInputSpec []
        (readCopyAtom (sourceBootstrapPhaseSpace owner)
          sourceEventBootstrapRule)
        sourceEventBootstrapDirective.rule.input).map Prod.fst := by
  let start := sourceEventStartRow owner
  let read := readCopyAtom (sourceBootstrapPhaseSpace owner)
    sourceEventBootstrapRule
  let afterSelf : Subst :=
    [("bootstrap-output", sourceBootstrapOutput),
     ("bootstrap-input", sourceBootstrapInput)]
  let finalRow := sourceBootstrapSubstitution owner
  have readMember (atom : Atom)
      (member : atom ∈ sourceBootstrapPhaseSpace owner) : atom ∈ read := by
    by_cases equal : atom = sourceEventBootstrapRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : sourceEventBootstrapRule ∈ read := by
    apply readMember
    simp [sourceBootstrapPhaseSpace, sourceBootstrapPhaseAtoms]
  have startMem : start ∈ read := by
    apply readMember
    simp [start, sourceBootstrapPhaseSpace, sourceBootstrapPhaseAtoms]
  have matchLocation :
      matchAtom [] sourceBootstrapLocation sourceBootstrapLocation = some [] := by
    simp [sourceBootstrapLocation, matchAtom, matchAtom.matchAtomList]
  have matchSelf :
      matchAtom []
          (.expression
            [.symbol "exec", sourceBootstrapLocation,
              .var "bootstrap-input", .var "bootstrap-output"])
          sourceEventBootstrapRule = some afterSelf := by
    simp [sourceEventBootstrapRule, sourceBootstrapInput,
      sourceBootstrapOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchLocation]
  have matchStart :
      matchAtom afterSelf
          (.expression [.symbol "mm-source-start", .var "source"])
          start = some finalRow := by
    simp [afterSelf, finalRow, sourceBootstrapSubstitution, start,
      sourceEventStartRow, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {sourceEventBootstrapRule, start}), ?_, rfl⟩
  simp only [sourceEventBootstrapDirective, matchInputSpec,
    sourceBootstrapPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, sourceEventBootstrapRule),
    matchOneInSpace_mem [] _ read sourceEventBootstrapRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(finalRow, start),
    matchOneInSpace_mem afterSelf _ read start startMem finalRow matchStart, ?_⟩
  simp [finalRow, start]

/-- Bootstrapping derives ordered control from the inert source owner marker;
the source-data producer does not supply a trusted program counter. -/
theorem sourceEventBootstrapDirective_fires_control (owner : Atom) :
    sourceControlAtom owner 0 ∈
      fireReflectiveSourceExecFact
        (sourceBootstrapPhaseSpace owner) sourceEventBootstrapDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom (sourceBootstrapPhaseSpace owner)
      sourceEventBootstrapDirective.atom)
    sourceEventBootstrapDirective.rule.input).map Prod.fst
  have rowMember : sourceBootstrapSubstitution owner ∈ rows := by
    simpa [rows, sourceEventBootstrapDirective] using
      sourceBootstrapMatchRow_mem owner
  have instantiates :
      instantiateTemplateAtom? (sourceBootstrapSubstitution owner)
          sourceBootstrapControlTemplate =
        some (sourceControlAtom owner 0) := by
    rfl
  have stagedMember :
      sourceControlAtom owner 0 ∈
        rows.foldl
          (stageReflectiveSupportSink (.add sourceBootstrapControlTemplate)) [] :=
    stageAdd_contains_of_row rows (sourceBootstrapSubstitution owner)
      sourceBootstrapControlTemplate (sourceControlAtom owner 0)
      rowMember instantiates
  change sourceControlAtom owner 0 ∈
    reflectiveSupportSinkProvider.run rows
      (consumeAtom (sourceBootstrapPhaseSpace owner) sourceEventBootstrapRule)
      sourceBootstrapSinks
  simp only [BatchSinkProvider.run_cons, BatchSinkProvider.run_nil,
    BatchSinkProvider.stageAll, reflectiveSupportSinkProvider,
    finalizeSupportSink, sourceBootstrapSinks]
  exact Finset.mem_union_left _
    (Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember))

theorem sourceEventBootstrapDirective_fires_environment (owner : Atom) :
    sourceInitialEnvironmentAtom owner ∈
      fireReflectiveSourceExecFact
        (sourceBootstrapPhaseSpace owner) sourceEventBootstrapDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom (sourceBootstrapPhaseSpace owner)
      sourceEventBootstrapDirective.atom)
    sourceEventBootstrapDirective.rule.input).map Prod.fst
  have rowMember : sourceBootstrapSubstitution owner ∈ rows := by
    simpa [rows, sourceEventBootstrapDirective] using
      sourceBootstrapMatchRow_mem owner
  have instantiates :
      instantiateTemplateAtom? (sourceBootstrapSubstitution owner)
          sourceBootstrapEnvironmentTemplate =
        some (sourceInitialEnvironmentAtom owner) := by
    rfl
  have stagedMember :
      sourceInitialEnvironmentAtom owner ∈
        rows.foldl
          (stageReflectiveSupportSink (.add sourceBootstrapEnvironmentTemplate))
          [] :=
    stageAdd_contains_of_row rows (sourceBootstrapSubstitution owner)
      sourceBootstrapEnvironmentTemplate (sourceInitialEnvironmentAtom owner)
      rowMember instantiates
  change sourceInitialEnvironmentAtom owner ∈
    reflectiveSupportSinkProvider.run rows
      (consumeAtom (sourceBootstrapPhaseSpace owner) sourceEventBootstrapRule)
      sourceBootstrapSinks
  simp only [BatchSinkProvider.run_cons, BatchSinkProvider.run_nil,
    BatchSinkProvider.stageAll, reflectiveSupportSinkProvider,
    finalizeSupportSink, sourceBootstrapSinks]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

private def sourceDispatchSubstitution (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) : Subst :=
  [("statement", rawStatementAtom statement),
   ("next-position", natAtom nextPosition),
   ("position", natAtom position), ("source", owner),
   ("dispatch-output", sourceDispatchOutput),
   ("dispatch-input", sourceDispatchInput)]

private theorem sourceDispatchMatchRow_mem (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    sourceDispatchSubstitution owner position nextPosition statement ∈
      (matchInputSpec []
        (readCopyAtom
          (sourceDispatchPhaseSpace owner position nextPosition statement)
          sourceEventDispatchRule)
        sourceEventDispatchDirective.rule.input).map Prod.fst := by
  let control := sourceControlAtom owner position
  let event := linkedRow "source-statement" owner position nextPosition
    (rawStatementAtom statement)
  let read := readCopyAtom
    (sourceDispatchPhaseSpace owner position nextPosition statement)
    sourceEventDispatchRule
  let afterSelf : Subst :=
    [("dispatch-output", sourceDispatchOutput),
     ("dispatch-input", sourceDispatchInput)]
  let afterControl : Subst :=
    [("position", natAtom position), ("source", owner),
     ("dispatch-output", sourceDispatchOutput),
     ("dispatch-input", sourceDispatchInput)]
  let finalRow := sourceDispatchSubstitution owner position nextPosition statement
  have readMember (atom : Atom)
      (member : atom ∈
        sourceDispatchPhaseSpace owner position nextPosition statement) :
      atom ∈ read := by
    by_cases equal : atom = sourceEventDispatchRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : sourceEventDispatchRule ∈ read := by
    apply readMember
    simp [sourceDispatchPhaseSpace, sourceDispatchPhaseAtoms]
  have controlMem : control ∈ read := by
    apply readMember
    simp [control, sourceDispatchPhaseSpace, sourceDispatchPhaseAtoms]
  have eventMem : event ∈ read := by
    apply readMember
    simp [event, sourceDispatchPhaseSpace, sourceDispatchPhaseAtoms]
  have matchLocation :
      matchAtom [] sourceDispatchLocation sourceDispatchLocation = some [] := by
    simp [sourceDispatchLocation, matchAtom, matchAtom.matchAtomList]
  have matchSelf :
      matchAtom []
          (.expression
            [.symbol "exec", sourceDispatchLocation,
              .var "dispatch-input", .var "dispatch-output"])
          sourceEventDispatchRule = some afterSelf := by
    simp [sourceEventDispatchRule, sourceDispatchInput,
      sourceDispatchOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchLocation]
  have matchControl :
      matchAtom afterSelf
          (.expression
            [.symbol "mm-source-control", .var "source", .var "position"])
          control = some afterControl := by
    simp [afterSelf, afterControl, control, sourceControlAtom, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchFamily :
      matchAtom afterControl (stringAtom "source-statement")
          (stringAtom "source-statement") = some afterControl := by
    exact groundAtom_matchAtom_self afterControl
      (stringAtom "source-statement") (by simp)
  have matchEvent :
      matchAtom afterControl
          (.expression
            [.symbol "mm-linked-row", stringAtom "source-statement",
              .var "source", .var "position", .var "next-position",
              .var "statement"])
          event = some finalRow := by
    simp [afterControl, finalRow, sourceDispatchSubstitution, event,
      linkedRow, matchAtom, matchAtom.matchAtomList, Subst.lookup,
      matchFamily]
  rw [List.mem_map]
  refine ⟨(finalRow, {sourceEventDispatchRule, control, event}), ?_, rfl⟩
  simp only [sourceEventDispatchDirective, matchInputSpec,
    sourceDispatchPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, sourceEventDispatchRule),
    matchOneInSpace_mem [] _ read sourceEventDispatchRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterControl, control),
    matchOneInSpace_mem afterSelf _ read control controlMem afterControl
      matchControl, ?_⟩
  refine ⟨(finalRow, event),
    matchOneInSpace_mem afterControl _ read event eventMem finalRow
      matchEvent, ?_⟩
  simp [finalRow, control, event]

/-- Firing the emitted dispatcher retains the exact source statement and
occurrence edge in the verifier's current-event state. -/
theorem sourceEventDispatchDirective_fires_current (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    sourceCurrentAtom owner position nextPosition statement ∈
      fireReflectiveSourceExecFact
        (sourceDispatchPhaseSpace owner position nextPosition statement)
        sourceEventDispatchDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (sourceDispatchPhaseSpace owner position nextPosition statement)
      sourceEventDispatchDirective.atom)
    sourceEventDispatchDirective.rule.input).map Prod.fst
  have rowMember :
      sourceDispatchSubstitution owner position nextPosition statement ∈ rows := by
    simpa [rows, sourceEventDispatchDirective] using
      sourceDispatchMatchRow_mem owner position nextPosition statement
  have currentInstantiates :
      instantiateTemplateAtom?
          (sourceDispatchSubstitution owner position nextPosition statement)
          sourceCurrentTemplate =
        some (sourceCurrentAtom owner position nextPosition statement) := by
    rfl
  have stagedMember :
      sourceCurrentAtom owner position nextPosition statement ∈
        rows.foldl
          (stageReflectiveSupportSink (.add sourceCurrentTemplate)) [] :=
    stageAdd_contains_of_row rows
      (sourceDispatchSubstitution owner position nextPosition statement)
      sourceCurrentTemplate
      (sourceCurrentAtom owner position nextPosition statement)
      rowMember currentInstantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    sourceEventDispatchDirective, sourceDispatchSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- Starting a theorem consumes its exact prepared row, creates proof work and
a private proof context, but does not itself publish an assertion index. -/
theorem sourceTheoremStartDirective_fires_pending_and_request (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    let statement := sourceProvableStatement site separator terminator label
      typecode body proof
    let result := fireReflectiveSourceExecFact
      (sourceTheoremStartPhaseSpace owner position nextPosition site separator
        terminator label typecode body proof theoremLabel expected)
      sourceTheoremStartDirective
    sourceTheoremPendingAtom owner position nextPosition statement ∈ result ∧
      sourceTheoremProofRequestAtom owner position nextPosition statement ∈
        result ∧
      sourceTheoremProofContextAtom owner position theoremLabel expected ∈
        result := by
  dsimp only
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let rows := (matchInputSpec []
    (readCopyAtom
      (sourceTheoremStartPhaseSpace owner position nextPosition site separator
        terminator label typecode body proof theoremLabel expected)
      sourceTheoremStartDirective.atom)
    sourceTheoremStartDirective.rule.input).map Prod.fst
  let substitution := sourceTheoremStartSubstitution owner position
    nextPosition site separator terminator label typecode body proof
    theoremLabel expected
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, sourceTheoremStartDirective] using
      sourceTheoremStartMatchRow_mem owner position nextPosition site separator
        terminator label typecode body proof theoremLabel expected
  have pendingInstantiates :
      instantiateTemplateAtom? substitution sourceTheoremPendingTemplate =
        some (sourceTheoremPendingAtom owner position nextPosition statement) :=
    by rfl
  have requestInstantiates :
      instantiateTemplateAtom? substitution sourceTheoremProofRequestTemplate =
        some
          (sourceTheoremProofRequestAtom owner position nextPosition statement) :=
    by rfl
  have pendingStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremPendingTemplate
    (sourceTheoremPendingAtom owner position nextPosition statement)
    rowMember pendingInstantiates
  have requestStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremProofRequestTemplate
    (sourceTheoremProofRequestAtom owner position nextPosition statement)
    rowMember requestInstantiates
  have contextInstantiates :
      instantiateTemplateAtom? substitution sourceTheoremProofContextTemplate =
        some
          (sourceTheoremProofContextAtom owner position theoremLabel expected) :=
    by rfl
  have contextStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremProofContextTemplate
    (sourceTheoremProofContextAtom owner position theoremLabel expected)
    rowMember contextInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sourceTheoremStartDirective, sourceTheoremStartSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr pendingStaged)))
  · constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        sourceTheoremStartDirective, sourceTheoremStartSinks,
        reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr requestStaged))
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sourceTheoremStartDirective, sourceTheoremStartSinks,
      reflectiveSupportSinkProvider]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr contextStaged)

/-- A matching normal-machine terminal observation is converted into the
private proof-success occurrence used by theorem admission. -/
theorem sourceTheoremSuccessDirective_fires_success (owner : Atom)
    (position : Nat) (theoremLabel expected proofOccurrence : Atom) :
    sourceTheoremProofSucceededAtom owner position proofOccurrence ∈
      fireReflectiveSourceExecFact
        (sourceTheoremSuccessPhaseSpace owner position theoremLabel expected
          proofOccurrence)
        sourceTheoremSuccessDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (sourceTheoremSuccessPhaseSpace owner position theoremLabel expected
        proofOccurrence)
      sourceTheoremSuccessDirective.atom)
    sourceTheoremSuccessDirective.rule.input).map Prod.fst
  let substitution := sourceTheoremSuccessSubstitution owner position
    theoremLabel expected proofOccurrence
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, sourceTheoremSuccessDirective] using
      sourceTheoremSuccessMatchRow_mem owner position theoremLabel expected
        proofOccurrence
  have instantiates :
      instantiateTemplateAtom? substitution sourceTheoremSuccessTemplate =
        some (sourceTheoremProofSucceededAtom owner position proofOccurrence) :=
    by rfl
  have staged := stageAdd_contains_of_row rows substitution
    sourceTheoremSuccessTemplate
    (sourceTheoremProofSucceededAtom owner position proofOccurrence)
    rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    sourceTheoremSuccessDirective, sourceTheoremSuccessSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

/-- A theorem is admitted, the dispatcher restored, and source order advanced
only by the continuation that consumes explicit proof-success evidence. -/
theorem sourceTheoremCommitDirective_fires_admission (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    let statement := sourceProvableStatement site separator terminator label
      typecode body proof
    let result := fireReflectiveSourceExecFact
      (sourceTheoremCommitPhaseSpace owner position nextPosition site separator
        terminator label typecode body proof proofOccurrence assertionPosition
        assertion)
      sourceTheoremCommitDirective
    assertionHeaderRow owner assertionPosition assertion ∈ result ∧
      sourceTheoremAdmittedAtom owner position statement proofOccurrence ∈
        result ∧
      sourceEventDispatchRule ∈ result ∧
      sourceControlAtom owner nextPosition ∈ result := by
  dsimp only
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let rows := (matchInputSpec []
    (readCopyAtom
      (sourceTheoremCommitPhaseSpace owner position nextPosition site separator
        terminator label typecode body proof proofOccurrence assertionPosition
        assertion)
      sourceTheoremCommitDirective.atom)
    sourceTheoremCommitDirective.rule.input).map Prod.fst
  let substitution := sourceTheoremCommitSubstitution owner position
    nextPosition site separator terminator label typecode body proof
    proofOccurrence assertionPosition assertion
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, sourceTheoremCommitDirective] using
      sourceTheoremCommitMatchRow_mem owner position nextPosition site separator
        terminator label typecode body proof proofOccurrence assertionPosition
        assertion
  have headerInstantiates :
      instantiateTemplateAtom? substitution (.var "assertion-header") =
        some (assertionHeaderRow owner assertionPosition assertion) := by
    rfl
  have admittedInstantiates :
      instantiateTemplateAtom? substitution sourceTheoremAdmittedTemplate =
        some
          (sourceTheoremAdmittedAtom owner position statement proofOccurrence) :=
    by rfl
  have dispatchInstantiates :
      instantiateTemplateAtom? substitution
          sourceTheoremRestoredDispatchTemplate =
        some sourceEventDispatchRule := by
    rfl
  have controlInstantiates :
      instantiateTemplateAtom? substitution sourceTheoremNextControlTemplate =
        some (sourceControlAtom owner nextPosition) := by
    rfl
  have admittedStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremAdmittedTemplate
    (sourceTheoremAdmittedAtom owner position statement proofOccurrence)
    rowMember admittedInstantiates
  have headerStaged := stageAdd_contains_of_row rows substitution
    (.var "assertion-header")
    (assertionHeaderRow owner assertionPosition assertion)
    rowMember headerInstantiates
  have dispatchStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremRestoredDispatchTemplate sourceEventDispatchRule rowMember
    dispatchInstantiates
  have controlStaged := stageAdd_contains_of_row rows substitution
    sourceTheoremNextControlTemplate (sourceControlAtom owner nextPosition)
    rowMember controlInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sourceTheoremCommitDirective, sourceTheoremCommitSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr headerStaged))))
  · constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sourceTheoremCommitDirective, sourceTheoremCommitSinks,
      reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr admittedStaged)))
    · constructor
      · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
          sourceTheoremCommitDirective, sourceTheoremCommitSinks,
          reflectiveSupportSinkProvider]
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr dispatchStaged))
      · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
          sourceTheoremCommitDirective, sourceTheoremCommitSinks,
          reflectiveSupportSinkProvider]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr controlStaged)

/-- The bootstrap is an ordinary scheduled MM2 step in the supplied target's
OSLF-generated NTT, and it derives both the initial program counter and the
empty scoped environment from the inert source marker. -/
theorem sourceBootstrapPhase_inhabits_target_native_type
    (targetPresentation : MM2Target) (owner : Atom) :
    let source := sourceBootstrapPhaseSpace owner
    let result := fireReflectiveSourceExecFact source
      sourceEventBootstrapDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        targetPresentation.operational.theory).satisfies
          (targetPresentation.embedSpace source)
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
            targetPresentation.operational.theory
            (targetPresentation.embedSpace result)).pred ∧
      sourceControlAtom owner 0 ∈ result ∧
      sourceInitialEnvironmentAtom owner ∈ result := by
  dsimp only
  refine ⟨?_, sourceEventBootstrapDirective_fires_control owner,
    sourceEventBootstrapDirective_fires_environment owner⟩
  exact (targetPresentation.native_type_iff_step _ _).2 <|
    (reflectiveScheduledEvent_nonempty_iff_step _ _).1
      ⟨reflectiveEventOfSelected
        (sourceBootstrapPhase_selects_directive owner)⟩

/-- The dispatcher is an actual scheduled step of the supplied target GSLT,
observed through the NTT generated by applying OSLF to that target. -/
theorem sourceDispatchPhase_inhabits_target_native_type
    (targetPresentation : MM2Target) (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    let source := sourceDispatchPhaseSpace owner position nextPosition statement
    let result := fireReflectiveSourceExecFact source
      sourceEventDispatchDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        targetPresentation.operational.theory).satisfies
          (targetPresentation.embedSpace source)
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
            targetPresentation.operational.theory
            (targetPresentation.embedSpace result)).pred ∧
      sourceCurrentAtom owner position nextPosition statement ∈ result := by
  dsimp only
  constructor
  · exact (targetPresentation.native_type_iff_step _ _).2 <|
      (reflectiveScheduledEvent_nonempty_iff_step _ _).1
      ⟨reflectiveEventOfSelected
        (sourceDispatchPhase_selects_directive owner position nextPosition
          statement)⟩
  · exact sourceEventDispatchDirective_fires_current owner position
      nextPosition statement

/-- The theorem-start transition is one genuine scheduled MM2 step, and its
observable outputs are exactly pending proof work rather than admission. -/
theorem sourceTheoremStartPhase_inhabits_target_native_type
    (targetPresentation : MM2Target) (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (theoremLabel expected : Atom) :
    let source := sourceTheoremStartPhaseSpace owner position nextPosition site
      separator terminator label typecode body proof theoremLabel expected
    let result := fireReflectiveSourceExecFact source
      sourceTheoremStartDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        targetPresentation.operational.theory).satisfies
          (targetPresentation.embedSpace source)
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
            targetPresentation.operational.theory
            (targetPresentation.embedSpace result)).pred ∧
      sourceTheoremPendingAtom owner position nextPosition
          (sourceProvableStatement site separator terminator label typecode body
            proof) ∈ result ∧
      sourceTheoremProofRequestAtom owner position nextPosition
          (sourceProvableStatement site separator terminator label typecode body
            proof) ∈ result ∧
      sourceTheoremProofContextAtom owner position theoremLabel expected ∈
        result := by
  dsimp only
  refine ⟨?_, sourceTheoremStartDirective_fires_pending_and_request owner
    position nextPosition site separator terminator label typecode body proof
    theoremLabel expected⟩
  exact (targetPresentation.native_type_iff_step _ _).2 <|
    (reflectiveScheduledEvent_nonempty_iff_step _ _).1
      ⟨reflectiveEventOfSelected
        (sourceTheoremStartPhase_selects_directive owner position nextPosition
          site separator terminator label typecode body proof theoremLabel
          expected)⟩

/-- Normal proof completion crosses into theorem admission through one exact
scheduled MM2 step over a verifier-owned proof context. -/
theorem sourceTheoremSuccessPhase_inhabits_target_native_type
    (targetPresentation : MM2Target) (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) :
    let source := sourceTheoremSuccessPhaseSpace owner position theoremLabel
      expected proofOccurrence
    let result := fireReflectiveSourceExecFact source
      sourceTheoremSuccessDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        targetPresentation.operational.theory).satisfies
          (targetPresentation.embedSpace source)
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
            targetPresentation.operational.theory
            (targetPresentation.embedSpace result)).pred ∧
      sourceTheoremProofSucceededAtom owner position proofOccurrence ∈
        result := by
  dsimp only
  constructor
  · exact (targetPresentation.native_type_iff_step _ _).2 <|
      (reflectiveScheduledEvent_nonempty_iff_step _ _).1
      ⟨reflectiveEventOfSelected
        (sourceTheoremSuccessPhase_selects_directive owner position theoremLabel
          expected proofOccurrence)⟩
  · exact sourceTheoremSuccessDirective_fires_success owner position
      theoremLabel expected proofOccurrence

/-- Conditional admission is likewise an exact target step.  Its source
contains explicit proof-success evidence; without that evidence this theorem
does not apply. -/
theorem sourceTheoremCommitPhase_inhabits_target_native_type
    (targetPresentation : MM2Target) (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (proofOccurrence : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    let source := sourceTheoremCommitPhaseSpace owner position nextPosition site
      separator terminator label typecode body proof proofOccurrence
      assertionPosition assertion
    let result := fireReflectiveSourceExecFact source
      sourceTheoremCommitDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        targetPresentation.operational.theory).satisfies
          (targetPresentation.embedSpace source)
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
            targetPresentation.operational.theory
            (targetPresentation.embedSpace result)).pred ∧
      sourceTheoremAdmittedAtom owner position
          (sourceProvableStatement site separator terminator label typecode body
            proof) proofOccurrence ∈ result ∧
      assertionHeaderRow owner assertionPosition assertion ∈ result ∧
      sourceEventDispatchRule ∈ result ∧
      sourceControlAtom owner nextPosition ∈ result := by
  dsimp only
  refine ⟨?_, ?_⟩
  · exact (targetPresentation.native_type_iff_step _ _).2 <|
      (reflectiveScheduledEvent_nonempty_iff_step _ _).1
        ⟨reflectiveEventOfSelected
          (sourceTheoremCommitPhase_selects_directive owner position nextPosition
            site separator terminator label typecode body proof proofOccurrence
            assertionPosition assertion)⟩
  · have fired :=
      sourceTheoremCommitDirective_fires_admission owner position nextPosition
        site separator terminator label typecode body proof proofOccurrence
        assertionPosition assertion
    exact ⟨fired.2.1, fired.1, fired.2.2.1, fired.2.2.2⟩

/-! ## Negative controls -/

/-- Verifier-owned executable rules cannot cross the untrusted source-event
admission boundary, even when supplied as directly authored MM2 data. -/
example (owner : Atom) :
    admitSourceEventInput owner [sourceEventDispatchRule] = .error .encoding := by
  simp [admitSourceEventInput, validateSourceEventInput,
    decodeSourceEventRows, decodeSourceEventStartRow, sourceEventDispatchRule,
    sourceDispatchLocation]

/-- A raw `$p` current row cannot start proof execution without the exact
prepared row recomputed behind the typed admission boundary. -/
theorem sourceTheoremStart_without_prepared_has_no_match (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) :
    matchInputSpec []
        (readCopyAtom
          (sourceTheoremStartUnpreparedPhaseSpace owner position nextPosition
            site separator terminator label typecode body proof)
          sourceTheoremStartRule)
        sourceTheoremStartDirective.rule.input = [] := by
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let current := sourceCurrentAtom owner position nextPosition statement
  let blocked := sourceTheoremStartUnpreparedPhaseSpace owner position
    nextPosition site separator terminator label typecode body proof
  let read := readCopyAtom blocked sourceTheoremStartRule
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row rowMember
  simp only [sourceTheoremStartDirective, matchInputSpec,
    sourceTheoremStartPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap] at rowMember
  rcases rowMember with ⟨selfPair, selfMember, rowMember⟩
  rcases rowMember with ⟨currentPair, currentMember, rowMember⟩
  rcases rowMember with ⟨preparedPair, preparedMember, _⟩
  rcases preparedPair with ⟨preparedSubstitution, preparedAtom⟩
  have preparedSpec := matchOneInSpace_spec _ _ _ _ _ preparedMember
  rcases preparedSpec with ⟨preparedAtomMember, preparedMatches⟩
  have classified :
      preparedAtom = sourceTheoremStartRule ∨ preparedAtom = current := by
    have raw :
        preparedAtom = sourceTheoremStartRule ∨
          (preparedAtom ≠ sourceTheoremStartRule ∧ preparedAtom = current) := by
      simpa [read, blocked, current, statement, readCopyAtom, consumeAtom,
        sourceTheoremStartUnpreparedPhaseSpace] using preparedAtomMember
    exact raw.elim Or.inl (fun right => Or.inr right.2)
  rcases classified with rfl | rfl
  · have noMatch :
        matchAtom currentPair.1 sourceTheoremPreparedTemplate
            sourceTheoremStartRule = none := by
      simp [sourceTheoremPreparedTemplate, sourceTheoremStartRule,
        matchAtom, matchAtom.matchAtomList]
    rw [noMatch] at preparedMatches
    simp at preparedMatches
  · have noMatch :
        matchAtom currentPair.1 sourceTheoremPreparedTemplate current = none := by
      simp [sourceTheoremPreparedTemplate, current, statement,
        sourceCurrentAtom, matchAtom, matchAtom.matchAtomList]
    rw [noMatch] at preparedMatches
    simp at preparedMatches

/-- A pending theorem cannot be admitted merely because its commit rule is
present.  The proof-success occurrence is a load-bearing match input. -/
theorem sourceTheoremCommit_without_success_has_no_match (owner : Atom)
    (position nextPosition : Nat) (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) (assertionPosition : Nat)
    (assertion : SourceAssertion) :
    matchInputSpec []
        (readCopyAtom
          (sourceTheoremCommitBlockedPhaseSpace owner position nextPosition
            site separator terminator label typecode body proof
            assertionPosition assertion)
          sourceTheoremCommitRule)
        sourceTheoremCommitDirective.rule.input = [] := by
  let statement := sourceProvableStatement site separator terminator label
    typecode body proof
  let pending := sourceTheoremPendingAtom owner position nextPosition statement
  let preparedHeader := sourcePreparedAssertionHeaderFact owner position
    (assertionHeaderRow owner assertionPosition assertion)
  let blocked := sourceTheoremCommitBlockedPhaseSpace owner position
    nextPosition site separator terminator label typecode body proof
    assertionPosition assertion
  let read := readCopyAtom blocked sourceTheoremCommitRule
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row rowMember
  simp only [sourceTheoremCommitDirective, matchInputSpec,
    sourceTheoremCommitPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap] at rowMember
  rcases rowMember with ⟨selfPair, selfMember, rowMember⟩
  rcases rowMember with ⟨pendingPair, pendingMember, rowMember⟩
  rcases rowMember with ⟨successPair, successMember, _⟩
  rcases successPair with ⟨successSubstitution, successAtom⟩
  have successSpec := matchOneInSpace_spec _ _ _ _ _ successMember
  rcases successSpec with ⟨successAtomMember, successMatches⟩
  have classified :
      successAtom = sourceTheoremCommitRule ∨ successAtom = pending ∨
        successAtom = preparedHeader := by
    have raw :
        successAtom = sourceTheoremCommitRule ∨
          (successAtom ≠ sourceTheoremCommitRule ∧
            (successAtom = pending ∨ successAtom = preparedHeader)) := by
      simpa [read, blocked, pending, preparedHeader, statement, readCopyAtom,
        consumeAtom, sourceTheoremCommitBlockedPhaseSpace] using
        successAtomMember
    exact raw.elim Or.inl (fun right => Or.inr right.2)
  rcases classified with rfl | rfl | rfl
  · simp [sourceTheoremSucceededTemplate, sourceTheoremCommitRule,
      sourceTheoremCommitInput, sourceTheoremCommitOutput,
      sourceTheoremCommitLocation, matchAtom, matchAtom.matchAtomList] at successMatches
  · simp [sourceTheoremSucceededTemplate, pending, statement,
      sourceTheoremPendingAtom, sourceProvableStatement, rawStatementAtom,
      matchAtom, matchAtom.matchAtomList] at successMatches
  · simp [sourceTheoremSucceededTemplate, preparedHeader,
      sourcePreparedAssertionHeaderFact, sourceProofOwnerAtom,
      assertionHeaderRow, matchAtom, matchAtom.matchAtomList] at successMatches

/-- Data alone cannot invent an MM2 transition when the executable
dispatcher is absent. -/
example (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          ({sourceControlAtom owner position,
            linkedRow "source-statement" owner position nextPosition
              (rawStatementAtom statement)} : Space)) = none := by
  let atoms :=
    [sourceControlAtom owner position,
     linkedRow "source-statement" owner position nextPosition
       (rawStatementAtom statement)]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) = none
  have candidates : cSupportedSourceExecFacts atoms = [] := by
    rfl
  have agreement := cSourceWorkQueueStep_selectSupported_eq atoms
    (by simp [atoms, sourceControlAtom, linkedRow])
    (by simp [KeyInjective, candidates])
  rw [candidates] at agreement
  exact agreement.symm

#print axioms extract_sourceEventDispatchRule_exact
#print axioms extract_sourceEventBootstrapRule_exact
#print axioms sourceBootstrapPhase_selects_directive
#print axioms sourceEventBootstrapDirective_fires_control
#print axioms sourceEventBootstrapDirective_fires_environment
#print axioms sourceBootstrapPhase_inhabits_target_native_type
#print axioms sourceDispatchPhase_selects_directive
#print axioms sourceEventDispatchDirective_fires_current
#print axioms sourceDispatchPhase_inhabits_target_native_type
#print axioms sourceTheoremStartPhase_selects_directive
#print axioms extract_sourceTheoremSuccessRule_exact
#print axioms sourceTheoremSuccessPhase_selects_directive
#print axioms sourceTheoremCommitPhase_selects_directive
#print axioms sourceTheoremStartDirective_fires_pending_and_request
#print axioms sourceTheoremSuccessDirective_fires_success
#print axioms sourceTheoremCommitDirective_fires_admission
#print axioms sourceTheoremStartPhase_inhabits_target_native_type
#print axioms sourceTheoremSuccessPhase_inhabits_target_native_type
#print axioms sourceTheoremCommitPhase_inhabits_target_native_type
#print axioms sourceTheoremStart_without_prepared_has_no_match
#print axioms sourceTheoremCommit_without_success_has_no_match

end Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
