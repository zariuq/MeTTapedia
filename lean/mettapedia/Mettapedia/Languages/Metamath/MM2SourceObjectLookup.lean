import Mettapedia.GSLT.Core.FiniteOccurrenceLookup
import Mettapedia.Languages.Metamath.MM2SourceActionExecution

/-!
# Source-object lookup for the MM2 Metamath verifier

Metamath has one global namespace for constants, variables, and labels, but
the result of finding a name is policy-neutral: a constant declaration needs
freshness, while a variable declaration may reactivate a historical variable
that is no longer active.  This module therefore separates finite lookup from
the declaration policy that consumes its observation.

The lookup inventory is an occurrence-preserving linked sequence.  Its
canonical decoder checks every predecessor/successor edge and the explicit
frontier.  The ordinary MM2 rules implement exact hit, explicit frontier, and
linked advance as separate scheduled transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceObjectLookup

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Source-owned inventory and declaration policy -/

inductive ObjectKind where
  | constant
  | variable
  | label
deriving DecidableEq, Repr

structure ObjectOccurrence where
  kind : ObjectKind
  occurrence : LocatedName
deriving DecidableEq, Repr

def ObjectOccurrence.key (entry : ObjectOccurrence) : String :=
  entry.occurrence.name

def semanticEntry (entry : ObjectOccurrence) :
    Entry String ObjectOccurrence :=
  { key := entry.key, value := entry }

abbrev SemanticState :=
  FiniteOccurrenceLookup.State String ObjectOccurrence

def semanticGSLT : GSLT :=
  FiniteOccurrenceLookup.gslt String ObjectOccurrence

/-- The source lookup passes through OSLF before any native-type use. -/
def semanticLookupNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  FiniteOccurrenceLookup.lookupNTT String ObjectOccurrence

inductive DeclarationKind where
  | constant
  | variable
deriving DecidableEq, Repr

inductive DeclarationDecision where
  | insertFresh (kind : ObjectKind)
  | reactivateVariable (historical : ObjectOccurrence)
  | rejectOccupied (occupied : ObjectOccurrence)
deriving DecidableEq, Repr

/-- Interpret an exact namespace observation without conflating global
occupancy with scope-local variable activity.  The latter is a subsequent
active-variable lookup obligation. -/
def declarationDecision (kind : DeclarationKind) :
    Observation ObjectOccurrence -> DeclarationDecision
  | .missing _ =>
      .insertFresh (match kind with
        | .constant => .constant
        | .variable => .variable)
  | .found _ occupied =>
      match kind, occupied.kind with
      | .variable, .variable => .reactivateVariable occupied
      | _, _ => .rejectOccupied occupied

theorem constant_missing_inserts (position : Nat) :
    declarationDecision .constant (.missing position) =
      .insertFresh .constant := by
  rfl

theorem constant_occupied_rejects (position : Nat)
    (occupied : ObjectOccurrence) :
    declarationDecision .constant (.found position occupied) =
      .rejectOccupied occupied := by
  cases occupied.kind <;> rfl

theorem variable_historical_variable_reactivates (position : Nat)
    (occupied : ObjectOccurrence) (sameKind : occupied.kind = .variable) :
    declarationDecision .variable (.found position occupied) =
      .reactivateVariable occupied := by
  cases occupied
  simp only at sameKind
  subst sameKind
  rfl

theorem variable_other_kind_rejects (position : Nat)
    (occupied : ObjectOccurrence) (different : occupied.kind != .variable) :
    declarationDecision .variable (.found position occupied) =
      .rejectOccupied occupied := by
  cases occupied with
  | mk kind occurrence =>
      cases kind <;> simp_all [declarationDecision]

/-! ## Canonical linked representation -/

def objectKindAtom : ObjectKind -> Atom
  | .constant => .symbol "mm-source-object-constant"
  | .variable => .symbol "mm-source-object-variable"
  | .label => .symbol "mm-source-object-label"

def decodeObjectKindAtom : Atom -> Option ObjectKind
  | .symbol "mm-source-object-constant" => some .constant
  | .symbol "mm-source-object-variable" => some .variable
  | .symbol "mm-source-object-label" => some .label
  | _ => none

@[simp] theorem decodeObjectKindAtom_objectKindAtom (kind : ObjectKind) :
    decodeObjectKindAtom (objectKindAtom kind) = some kind := by
  cases kind <;> rfl

theorem objectKindAtom_injective : Function.Injective objectKindAtom := by
  intro left right equal
  have decoded := congrArg decodeObjectKindAtom equal
  simpa using decoded

def objectOccurrenceAtom (entry : ObjectOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-object-entry", objectKindAtom entry.kind,
      locatedNameAtom entry.occurrence]

def decodeObjectOccurrenceAtom : Atom -> Option ObjectOccurrence
  | .expression [.symbol "mm-source-object-entry", encodedKind, encodedName] => do
      let kind <- decodeObjectKindAtom encodedKind
      let occurrence <- decodeLocatedNameAtom encodedName
      pure { kind, occurrence }
  | _ => none

@[simp] theorem decodeObjectOccurrenceAtom_objectOccurrenceAtom
    (entry : ObjectOccurrence) :
    decodeObjectOccurrenceAtom (objectOccurrenceAtom entry) = some entry := by
  cases entry
  simp [decodeObjectOccurrenceAtom, objectOccurrenceAtom]

theorem objectOccurrenceAtom_injective :
    Function.Injective objectOccurrenceAtom := by
  intro left right equal
  have decoded := congrArg decodeObjectOccurrenceAtom equal
  simpa using decoded

def objectRootKey : Atom :=
  .expression [.symbol "mm-source-object-root"]

def objectLinkAtom (owner previous next : Atom)
    (entry : ObjectOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-object-link", owner, previous, next,
      objectOccurrenceAtom entry]

def objectFrontierAtom (owner frontier : Atom) : Atom :=
  .expression [.symbol "mm-source-object-frontier", owner, frontier]

def objectInventoryRowsFrom (owner previous : Atom) :
    List ObjectOccurrence -> List Atom
  | [] => [objectFrontierAtom owner previous]
  | entry :: rest =>
      let next := locatedNameAtom entry.occurrence
      objectLinkAtom owner previous next entry ::
        objectInventoryRowsFrom owner next rest

def objectInventoryRows (owner : Atom)
    (entries : List ObjectOccurrence) : List Atom :=
  objectInventoryRowsFrom owner objectRootKey entries

def decodeObjectLinkAtom (owner expectedPrevious : Atom) :
    Atom -> Option (Atom × ObjectOccurrence)
  | .expression
      [.symbol "mm-source-object-link", actualOwner, previous, next,
        encodedEntry] => do
      guard (actualOwner == owner)
      guard (previous == expectedPrevious)
      let entry <- decodeObjectOccurrenceAtom encodedEntry
      guard (next == locatedNameAtom entry.occurrence)
      pure (next, entry)
  | _ => none

def decodeObjectInventoryRowsFrom (owner current : Atom) :
    List Atom -> Option (List ObjectOccurrence)
  | [frontier] =>
      if frontier == objectFrontierAtom owner current then some [] else none
  | row :: rest => do
      let (next, entry) <- decodeObjectLinkAtom owner current row
      let entries <- decodeObjectInventoryRowsFrom owner next rest
      pure (entry :: entries)
  | _ => none
termination_by rows => rows.length

def decodeObjectInventoryRows (owner : Atom)
    (rows : List Atom) : Option (List ObjectOccurrence) :=
  decodeObjectInventoryRowsFrom owner objectRootKey rows

@[simp] theorem decodeObjectInventoryRowsFrom_objectInventoryRowsFrom
    (owner previous : Atom) (entries : List ObjectOccurrence) :
    decodeObjectInventoryRowsFrom owner previous
        (objectInventoryRowsFrom owner previous entries) = some entries := by
  induction entries generalizing previous with
  | nil =>
      simp [decodeObjectInventoryRowsFrom, objectInventoryRowsFrom,
        objectFrontierAtom]
  | cons entry rest induction =>
      cases rest with
      | nil =>
          simp [decodeObjectInventoryRowsFrom, objectInventoryRowsFrom,
            decodeObjectLinkAtom, objectLinkAtom, objectFrontierAtom]
      | cons next rest =>
          simp [decodeObjectInventoryRowsFrom, objectInventoryRowsFrom,
            decodeObjectLinkAtom, objectLinkAtom]
          exact induction (locatedNameAtom entry.occurrence)

@[simp] theorem decodeObjectInventoryRows_objectInventoryRows
    (owner : Atom) (entries : List ObjectOccurrence) :
    decodeObjectInventoryRows owner (objectInventoryRows owner entries) =
      some entries := by
  exact decodeObjectInventoryRowsFrom_objectInventoryRowsFrom owner
    objectRootKey entries

theorem objectInventoryRows_injective (owner : Atom) :
    Function.Injective (objectInventoryRows owner) := by
  intro left right equal
  have decoded := congrArg (decodeObjectInventoryRows owner) equal
  simpa using decoded

/-- Exact cursor reached after an occurrence prefix. -/
def objectFrontierKeyFrom (previous : Atom) :
    List ObjectOccurrence -> Atom
  | [] => previous
  | entry :: rest =>
      objectFrontierKeyFrom (locatedNameAtom entry.occurrence) rest

def objectFrontierKey (entries : List ObjectOccurrence) : Atom :=
  objectFrontierKeyFrom objectRootKey entries

@[simp] theorem objectInventoryRowsFrom_getLast?
    (owner previous : Atom) (entries : List ObjectOccurrence) :
    (objectInventoryRowsFrom owner previous entries).getLast? =
      some
        (objectFrontierAtom owner
          (objectFrontierKeyFrom previous entries)) := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry entries induction =>
      cases entries with
      | nil => rfl
      | cons next rest =>
          simpa [objectInventoryRowsFrom, objectFrontierKeyFrom] using
            induction (locatedNameAtom entry.occurrence)

@[simp] theorem objectInventoryRows_getLast?
    (owner : Atom) (entries : List ObjectOccurrence) :
    (objectInventoryRows owner entries).getLast? =
      some (objectFrontierAtom owner (objectFrontierKey entries)) := by
  exact objectInventoryRowsFrom_getLast? owner objectRootKey entries

/-- Every linked object row in a canonical inventory carries an exact source
occurrence from that inventory.  Owner and cursor fields cannot manufacture a
new payload. -/
theorem objectLink_mem_objectInventoryRowsFrom_has_entry
    (owner start previous next : Atom) (entry : ObjectOccurrence)
    (entries : List ObjectOccurrence)
    (member : objectLinkAtom owner previous next entry ∈
      objectInventoryRowsFrom owner start entries) :
    entry ∈ entries := by
  induction entries generalizing start with
  | nil =>
      simp [objectInventoryRowsFrom, objectLinkAtom,
        objectFrontierAtom] at member
  | cons head tail induction =>
      simp only [objectInventoryRowsFrom, List.mem_cons] at member
      rcases member with equal | member
      · have argumentsEqual :
            [.symbol "mm-source-object-link", owner, previous, next,
              objectOccurrenceAtom entry] =
            [.symbol "mm-source-object-link", owner, start,
              locatedNameAtom head.occurrence,
              objectOccurrenceAtom head] :=
          Atom.expression.inj equal
        have encodedEqual :
            objectOccurrenceAtom entry = objectOccurrenceAtom head := by
          simpa using congrArg List.getLast? argumentsEqual
        have entryEqual := objectOccurrenceAtom_injective encodedEqual
        subst entry
        simp
      · exact List.mem_cons_of_mem head
          (induction (locatedNameAtom head.occurrence) member)

theorem objectLink_mem_objectInventoryRows_has_entry
    (owner previous next : Atom) (entry : ObjectOccurrence)
    (entries : List ObjectOccurrence)
    (member : objectLinkAtom owner previous next entry ∈
      objectInventoryRows owner entries) :
    entry ∈ entries := by
  exact objectLink_mem_objectInventoryRowsFrom_has_entry
    owner objectRootKey previous next entry entries member

/-! ## Ordinary MM2 lookup rules -/

private def lookupHitLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-source-object-lookup-hit"]

private def lookupHitContinuationLocation : Atom :=
  .expression
    [.symbol "00", .symbol "mm-source-object-lookup-hit-continuation"]

private def lookupMissingContinuationLocation : Atom :=
  .expression
    [.symbol "00", .symbol "mm-source-object-lookup-missing-continuation"]

private def lookupAdvanceContinuationLocation : Atom :=
  .expression
    [.symbol "02", .symbol "mm-source-object-lookup-advance-continuation"]

private def lookupMissingLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-source-object-lookup-missing"]

private def lookupAdvanceLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-object-lookup-advance"]

private def objectLookupReloadLocation : Atom :=
  .expression [.symbol "35", .symbol "mm-source-object-lookup-reload"]

private def lookupTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", .var "source", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "cursor", .var "frontier"]

private def lookupAtFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", .var "source", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "frontier", .var "frontier"]

private def keyedLookupTemplate : Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", .var "source",
      .var "lookup-key", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "cursor", .var "frontier"]

private def keyedLookupAtFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", .var "source",
      .var "lookup-key", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "frontier", .var "frontier"]

private def matchingLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "cursor",
      .var "next-cursor",
      (.expression
        [.symbol "mm-source-object-entry", .var "occupied-kind",
          (.expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "candidate-name"])])]

private def anyLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "cursor",
      .var "next-cursor",
      (.expression
        [.symbol "mm-source-object-entry", .var "occupied-kind",
          (.expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "occupied-name"])])]

private def frontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source", .var "frontier"]

private def lookupFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-found", .var "source", .var "request",
      (.expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"]),
      (.expression
        [.symbol "mm-source-object-entry", .var "occupied-kind",
          (.expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "candidate-name"])])]

private def lookupMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-missing", .var "source", .var "request",
      (.expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"])]

/-- A protected consumer registration keyed only by ground protocol data.
The consumer rule is captured as one opaque atom. -/
def objectLookupFoundContinuationRow (key : Atom) (kind : ObjectKind)
    (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-continuation",
      .symbol "found", key, objectKindAtom kind, rule]

def objectLookupMissingContinuationRow (key rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-continuation",
      .symbol "missing", key, rule]

@[simp] theorem objectLookupFoundContinuationRow_not_proofNeutral
    (key : Atom) (kind : ObjectKind) (rule : Atom) :
    isProofNeutralInitialAtom
      (objectLookupFoundContinuationRow key kind rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-object-lookup-continuation"
      [.symbol "found", key, objectKindAtom kind, rule] (by decide)

@[simp] theorem objectLookupMissingContinuationRow_not_proofNeutral
    (key rule : Atom) :
    isProofNeutralInitialAtom
      (objectLookupMissingContinuationRow key rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-object-lookup-continuation"
      [.symbol "missing", key, rule] (by decide)

private def foundContinuationTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-continuation",
      .symbol "found", .var "lookup-key", .var "occupied-kind",
      .var "object-lookup-continuation-rule"]

private def missingContinuationTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-continuation",
      .symbol "missing", .var "lookup-key",
      .var "object-lookup-continuation-rule"]

private def lookupNextTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", .var "source", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "next-cursor", .var "frontier"]

private def keyedLookupNextTemplate : Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", .var "source",
      .var "lookup-key", .var "request",
      .expression
        [.symbol "mm-source-name", .var "candidate-span",
          .var "candidate-name"],
      .var "next-cursor", .var "frontier"]

/-- Source-bound request to reinstall the finite lookup rules from the
verifier-owned inventory. -/
def objectLookupReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-object-lookup", .var "source"]

def objectLookupReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", owner]

private def hitContinuationSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupHitContinuationLocation,
      .var "hit-continuation-input", .var "hit-continuation-output"]

private def hitContinuationPatternAtoms : List Atom :=
  [hitContinuationSelfTemplate, keyedLookupTemplate, matchingLinkTemplate,
   foundContinuationTemplate]

private def hitContinuationSinks : List Sink :=
  [.add hitContinuationSelfTemplate, .remove keyedLookupTemplate,
   .add lookupFoundTemplate,
   .add (.var "object-lookup-continuation-rule")]

def lookupHitContinuationRule : Atom :=
  .expression
    [.symbol "exec", lookupHitContinuationLocation,
      .expression (.symbol "," :: hitContinuationPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "+", hitContinuationSelfTemplate],
          .expression [.symbol "-", keyedLookupTemplate],
          .expression [.symbol "+", lookupFoundTemplate],
          .expression
            [.symbol "+", .var "object-lookup-continuation-rule"]]]

def lookupHitContinuationDirective : SourceExecFact where
  atom := lookupHitContinuationRule
  loc := lookupHitContinuationLocation
  rule :=
    { priority := 0
      name := "mm-source-object-lookup-hit-continuation"
      input := .compat (mkPattern hitContinuationPatternAtoms)
      guards := []
      tmpl := mkTemplate hitContinuationSinks }

theorem extract_lookupHitContinuationRule_exact :
    extractSupportedSourceExecFact lookupHitContinuationRule =
      some lookupHitContinuationDirective := by
  rfl

private def missingContinuationSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupMissingContinuationLocation,
      .var "missing-continuation-input",
      .var "missing-continuation-output"]

private def missingContinuationPatternAtoms : List Atom :=
  [missingContinuationSelfTemplate, keyedLookupAtFrontierTemplate,
   frontierTemplate, missingContinuationTemplate]

private def missingContinuationSinks : List Sink :=
  [.add missingContinuationSelfTemplate,
   .remove keyedLookupAtFrontierTemplate,
   .add lookupMissingTemplate,
   .add (.var "object-lookup-continuation-rule")]

def lookupMissingContinuationRule : Atom :=
  .expression
    [.symbol "exec", lookupMissingContinuationLocation,
      .expression (.symbol "," :: missingContinuationPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "+", missingContinuationSelfTemplate],
          .expression [.symbol "-", keyedLookupAtFrontierTemplate],
          .expression [.symbol "+", lookupMissingTemplate],
          .expression
            [.symbol "+", .var "object-lookup-continuation-rule"]]]

def lookupMissingContinuationDirective : SourceExecFact where
  atom := lookupMissingContinuationRule
  loc := lookupMissingContinuationLocation
  rule :=
    { priority := 0
      name := "mm-source-object-lookup-missing-continuation"
      input := .compat (mkPattern missingContinuationPatternAtoms)
      guards := []
      tmpl := mkTemplate missingContinuationSinks }

theorem extract_lookupMissingContinuationRule_exact :
    extractSupportedSourceExecFact lookupMissingContinuationRule =
      some lookupMissingContinuationDirective := by
  rfl

private def advanceContinuationSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupAdvanceContinuationLocation,
      .var "advance-continuation-input",
      .var "advance-continuation-output"]

private def advanceContinuationPatternAtoms : List Atom :=
  [advanceContinuationSelfTemplate, keyedLookupTemplate, anyLinkTemplate]

private def advanceContinuationSinks : List Sink :=
  [.remove keyedLookupTemplate, .add keyedLookupNextTemplate,
   .add objectLookupReloadTriggerTemplate]

def lookupAdvanceContinuationRule : Atom :=
  .expression
    [.symbol "exec", lookupAdvanceContinuationLocation,
      .expression (.symbol "," :: advanceContinuationPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "-", keyedLookupTemplate],
          .expression [.symbol "+", keyedLookupNextTemplate],
          .expression [.symbol "+", objectLookupReloadTriggerTemplate]]]

def lookupAdvanceContinuationDirective : SourceExecFact where
  atom := lookupAdvanceContinuationRule
  loc := lookupAdvanceContinuationLocation
  rule :=
    { priority := 2
      name := "mm-source-object-lookup-advance-continuation"
      input := .compat (mkPattern advanceContinuationPatternAtoms)
      guards := []
      tmpl := mkTemplate advanceContinuationSinks }

theorem extract_lookupAdvanceContinuationRule_exact :
    extractSupportedSourceExecFact lookupAdvanceContinuationRule =
      some lookupAdvanceContinuationDirective := by
  rfl

private def hitSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupHitLocation, .var "hit-input", .var "hit-output"]

private def hitPatternAtoms : List Atom :=
  [hitSelfTemplate, lookupTemplate, matchingLinkTemplate]

private def hitSinks : List Sink :=
  [.add hitSelfTemplate, .remove lookupTemplate, .add lookupFoundTemplate]

def lookupHitRule : Atom :=
  .expression
    [.symbol "exec", lookupHitLocation,
      .expression (.symbol "," :: hitPatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "+", hitSelfTemplate],
          .expression [.symbol "-", lookupTemplate],
          .expression [.symbol "+", lookupFoundTemplate]]]

def lookupHitDirective : SourceExecFact where
  atom := lookupHitRule
  loc := lookupHitLocation
  rule :=
    { priority := 0
      name := "mm-source-object-lookup-hit"
      input := .compat (mkPattern hitPatternAtoms)
      guards := []
      tmpl := mkTemplate hitSinks }

theorem extract_lookupHitRule_exact :
    extractSupportedSourceExecFact lookupHitRule = some lookupHitDirective := by
  rfl

private def missingSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupMissingLocation,
      .var "missing-input", .var "missing-output"]

private def missingPatternAtoms : List Atom :=
  [missingSelfTemplate, lookupAtFrontierTemplate, frontierTemplate]

private def missingSinks : List Sink :=
  [.add missingSelfTemplate, .remove lookupAtFrontierTemplate,
   .add lookupMissingTemplate]

def lookupMissingRule : Atom :=
  .expression
    [.symbol "exec", lookupMissingLocation,
      .expression (.symbol "," :: missingPatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "+", missingSelfTemplate],
          .expression [.symbol "-", lookupAtFrontierTemplate],
          .expression [.symbol "+", lookupMissingTemplate]]]

def lookupMissingDirective : SourceExecFact where
  atom := lookupMissingRule
  loc := lookupMissingLocation
  rule :=
    { priority := 1
      name := "mm-source-object-lookup-missing"
      input := .compat (mkPattern missingPatternAtoms)
      guards := []
      tmpl := mkTemplate missingSinks }

theorem extract_lookupMissingRule_exact :
    extractSupportedSourceExecFact lookupMissingRule =
      some lookupMissingDirective := by
  rfl

private def advanceSelfTemplate : Atom :=
  .expression
    [.symbol "exec", lookupAdvanceLocation,
      .var "advance-input", .var "advance-output"]

private def advancePatternAtoms : List Atom :=
  [advanceSelfTemplate, lookupTemplate, anyLinkTemplate]

private def advanceSinks : List Sink :=
  [.remove lookupTemplate, .add lookupNextTemplate,
   .add objectLookupReloadTriggerTemplate]

def lookupAdvanceRule : Atom :=
  .expression
    [.symbol "exec", lookupAdvanceLocation,
      .expression (.symbol "," :: advancePatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "-", lookupTemplate],
          .expression [.symbol "+", lookupNextTemplate],
          .expression [.symbol "+", objectLookupReloadTriggerTemplate]]]

def lookupAdvanceDirective : SourceExecFact where
  atom := lookupAdvanceRule
  loc := lookupAdvanceLocation
  rule :=
    { priority := 2
      name := "mm-source-object-lookup-advance"
      input := .compat (mkPattern advancePatternAtoms)
      guards := []
      tmpl := mkTemplate advanceSinks }

theorem extract_lookupAdvanceRule_exact :
    extractSupportedSourceExecFact lookupAdvanceRule =
      some lookupAdvanceDirective := by
  rfl

def lookupScanRules : List Atom :=
  [lookupHitContinuationRule, lookupMissingContinuationRule,
   lookupAdvanceContinuationRule, lookupHitRule, lookupMissingRule,
   lookupAdvanceRule]

def lookupScanDirectives : List SourceExecFact :=
  [lookupHitContinuationDirective, lookupMissingContinuationDirective,
   lookupAdvanceContinuationDirective, lookupHitDirective,
   lookupMissingDirective, lookupAdvanceDirective]

/-! ## Verifier-owned finite rule reinstallation -/

/-- Passive opaque code row.  The inner executable rule is captured as one
atom, so an outer declaration match cannot substitute its local variables. -/
def objectLookupRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-object-lookup-rule", rule]

private def objectLookupScanRuleTemplate (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-scan-rule", .symbol kind,
      .var variableName]

private def objectLookupHitCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "hit" "object-lookup-hit-rule"

private def objectLookupMissingCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "missing" "object-lookup-missing-rule"

private def objectLookupHitContinuationCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "hit-continuation"
    "object-lookup-hit-continuation-rule"

private def objectLookupMissingContinuationCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "missing-continuation"
    "object-lookup-missing-continuation-rule"

private def objectLookupAdvanceContinuationCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "advance-continuation"
    "object-lookup-advance-continuation-rule"

private def objectLookupAdvanceCaptureTemplate : Atom :=
  objectLookupScanRuleTemplate "advance" "object-lookup-advance-rule"

def objectLookupScanCaptureRows : List Atom :=
  [.expression
      [.symbol "mm-internal-source-object-lookup-scan-rule",
        .symbol "hit-continuation", lookupHitContinuationRule],
   .expression
      [.symbol "mm-internal-source-object-lookup-scan-rule",
        .symbol "missing-continuation", lookupMissingContinuationRule],
   .expression
      [.symbol "mm-internal-source-object-lookup-scan-rule",
        .symbol "advance-continuation", lookupAdvanceContinuationRule],
   .expression
      [.symbol "mm-internal-source-object-lookup-scan-rule", .symbol "hit",
        lookupHitRule],
   .expression
      [.symbol "mm-internal-source-object-lookup-scan-rule",
        .symbol "missing", lookupMissingRule],
   .expression
      [.symbol "mm-internal-source-object-lookup-scan-rule",
        .symbol "advance", lookupAdvanceRule]]

private def objectLookupReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", objectLookupReloadLocation,
      .var "object-lookup-reload-input",
      .var "object-lookup-reload-output"]

private def objectLookupRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-object-lookup-rule",
      .var "object-lookup-rule"]

private def objectLookupReloadPatternAtoms : List Atom :=
  [objectLookupReloadSelfTemplate, objectLookupReloadTriggerTemplate,
   objectLookupHitContinuationCaptureTemplate,
   objectLookupMissingContinuationCaptureTemplate,
   objectLookupAdvanceContinuationCaptureTemplate,
   objectLookupHitCaptureTemplate, objectLookupMissingCaptureTemplate,
   objectLookupAdvanceCaptureTemplate, objectLookupRuleTemplate]

private def objectLookupReloadSinks : List Sink :=
  [.add objectLookupReloadSelfTemplate,
   .remove objectLookupReloadTriggerTemplate,
   .add (.var "object-lookup-hit-continuation-rule"),
   .add (.var "object-lookup-missing-continuation-rule"),
   .add (.var "object-lookup-advance-continuation-rule"),
   .add (.var "object-lookup-hit-rule"),
   .add (.var "object-lookup-missing-rule"),
   .add (.var "object-lookup-advance-rule"),
   .add (.var "object-lookup-rule")]

/-- Reinstall every registered scan or consumer-continuation rule by opaque
capture from verifier-owned rows.  No nested rule variable is visible to the
declaration that requested the reload. -/
def objectLookupReloadRule : Atom :=
  .expression
    [.symbol "exec", objectLookupReloadLocation,
      .expression (.symbol "," :: objectLookupReloadPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "+", objectLookupReloadSelfTemplate],
          .expression [.symbol "-", objectLookupReloadTriggerTemplate],
          .expression
            [.symbol "+", .var "object-lookup-hit-continuation-rule"],
          .expression
            [.symbol "+", .var "object-lookup-missing-continuation-rule"],
          .expression
            [.symbol "+", .var "object-lookup-advance-continuation-rule"],
          .expression [.symbol "+", .var "object-lookup-hit-rule"],
          .expression [.symbol "+", .var "object-lookup-missing-rule"],
          .expression [.symbol "+", .var "object-lookup-advance-rule"],
          .expression [.symbol "+", .var "object-lookup-rule"]]]

def objectLookupReloadDirective : SourceExecFact where
  atom := objectLookupReloadRule
  loc := objectLookupReloadLocation
  rule :=
    { priority := 35
      name := "mm-source-object-lookup-reload"
      input := .compat (mkPattern objectLookupReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate objectLookupReloadSinks }

theorem extract_objectLookupReloadRule_exact :
    extractSupportedSourceExecFact objectLookupReloadRule =
      some objectLookupReloadDirective := by
  rfl

def objectLookupStaticRows : List Atom :=
  objectLookupScanCaptureRows ++ lookupScanRules.map objectLookupRuleRow

@[simp] theorem objectLookupRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (objectLookupRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-object-lookup-rule" [rule] (by decide)

def lookupRules : List Atom :=
  lookupScanRules ++ [objectLookupReloadRule]

def lookupDirectives : List SourceExecFact :=
  lookupScanDirectives ++ [objectLookupReloadDirective]

theorem lookupRules_extract_exact :
    lookupRules.filterMap extractSupportedSourceExecFact = lookupDirectives := by
  rfl

/-! ## Source-bound executable controls -/

def lookupAtom (owner request : Atom) (candidate : LocatedName)
    (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", owner, request,
      locatedNameAtom candidate, cursor, frontier]

def keyedLookupAtom (owner key request : Atom) (candidate : LocatedName)
    (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-keyed-object-lookup", owner, key, request,
      locatedNameAtom candidate, cursor, frontier]

def lookupFoundAtom (owner request : Atom) (candidate : LocatedName)
    (occupied : ObjectOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-object-found", owner, request,
      locatedNameAtom candidate, objectOccurrenceAtom occupied]

def lookupMissingAtom (owner request : Atom) (candidate : LocatedName) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", owner, request,
      locatedNameAtom candidate]

private def canarySpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "lookup.mm", start, stop }

private def existingOccurrence : ObjectOccurrence :=
  { kind := .constant
    occurrence := { span := canarySpan 0 3, name := "wff" } }

private def sameNameCandidate : LocatedName :=
  { span := canarySpan 10 13, name := "wff" }

private def absentCandidate : LocatedName :=
  { span := canarySpan 20 21, name := "x" }

private def canaryOwner : Atom := .symbol "source-owner"
private def canaryRequest : Atom := .symbol "declaration-request"
private def canaryNext : Atom := locatedNameAtom existingOccurrence.occurrence

private def hitCanaryAtoms : List Atom :=
  [lookupHitRule,
   lookupAtom canaryOwner canaryRequest sameNameCandidate objectRootKey
     canaryNext,
   objectLinkAtom canaryOwner objectRootKey canaryNext existingOccurrence]

private def hitCanarySpace : Space := hitCanaryAtoms.toFinset

private theorem hitCanaryAtoms_nodup : hitCanaryAtoms.Nodup := by
  decide +kernel

private theorem hitCanaryAtoms_supported :
    cSupportedSourceExecFacts hitCanaryAtoms = [lookupHitDirective] := by
  rfl

theorem hitCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace hitCanarySpace) =
      some lookupHitDirective := by
  exact reflective_selects_of_computable_supported_singleton
    hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup
    hitCanaryAtoms_supported

theorem hitCanary_fires_source_occurrence :
    lookupFoundAtom canaryOwner canaryRequest sameNameCandidate
        existingOccurrence ∈
      fireReflectiveSourceExecFact hitCanarySpace lookupHitDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        lookupHitDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup)
  have computableMember :
      lookupFoundAtom canaryOwner canaryRequest sameNameCandidate
          existingOccurrence ∈
        (cFireReflectiveSourceExecFact hitCanaryAtoms
          lookupHitDirective).toFinset :=
    List.mem_toFinset.mpr (by decide +kernel)
  rw [agreement] at computableMember
  simpa [hitCanarySpace] using computableMember

theorem hitCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies hitCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact hitCanarySpace
          lookupHitDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected hitCanary_selects_directive)

private def missingCanaryAtoms : List Atom :=
  [lookupMissingRule,
   lookupAtom canaryOwner canaryRequest absentCandidate canaryNext canaryNext,
   objectFrontierAtom canaryOwner canaryNext]

private def missingCanarySpace : Space := missingCanaryAtoms.toFinset

private theorem missingCanaryAtoms_nodup : missingCanaryAtoms.Nodup := by
  decide +kernel

private theorem missingCanaryAtoms_supported :
    cSupportedSourceExecFacts missingCanaryAtoms =
      [lookupMissingDirective] := by
  rfl

theorem missingCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace missingCanarySpace) =
      some lookupMissingDirective := by
  exact reflective_selects_of_computable_supported_singleton
    missingCanaryAtoms lookupMissingDirective missingCanaryAtoms_nodup
    missingCanaryAtoms_supported

theorem missingCanary_fires_explicit_frontier :
    lookupMissingAtom canaryOwner canaryRequest absentCandidate ∈
      fireReflectiveSourceExecFact missingCanarySpace
        lookupMissingDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      missingCanaryAtoms lookupMissingDirective missingCanaryAtoms_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        lookupMissingDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        missingCanaryAtoms lookupMissingDirective missingCanaryAtoms_nodup)
  have computableMember :
      lookupMissingAtom canaryOwner canaryRequest absentCandidate ∈
        (cFireReflectiveSourceExecFact missingCanaryAtoms
          lookupMissingDirective).toFinset :=
    List.mem_toFinset.mpr (by decide +kernel)
  rw [agreement] at computableMember
  simpa [missingCanarySpace] using computableMember

theorem missingCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies missingCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact missingCanarySpace
          lookupMissingDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected missingCanary_selects_directive)

/-- A same-name occurrence of a different kind still wins the exact-hit rule;
the declaration policy, rather than the lookup mechanism, rejects it. -/
theorem hitRule_matches_name_across_occurrence_spans :
    (cmatchInputSpec [] hitCanaryAtoms lookupHitDirective.rule.input).isEmpty =
      false := by
  decide +kernel

/-- A frontier observation cannot be fabricated away from the exact frontier
row carried by the source-owned inventory. -/
theorem missingRule_rejects_wrong_frontier :
    (cmatchInputSpec []
      [lookupMissingRule,
       lookupAtom canaryOwner canaryRequest absentCandidate objectRootKey
         canaryNext,
       objectFrontierAtom canaryOwner canaryNext]
      lookupMissingDirective.rule.input).isEmpty = true := by
  decide +kernel

/-! ## Ground-keyed continuation controls -/

private def canaryLookupKey : Atom := .symbol "lookup-canary-key"
private def wrongCanaryLookupKey : Atom := .symbol "wrong-lookup-canary-key"
private def canaryContinuation : Atom := .symbol "lookup-canary-continuation"

private def keyedHitCanaryAtoms : List Atom :=
  [lookupHitContinuationRule,
   keyedLookupAtom canaryOwner canaryLookupKey canaryRequest
     sameNameCandidate objectRootKey canaryNext,
   objectLinkAtom canaryOwner objectRootKey canaryNext existingOccurrence,
   objectLookupFoundContinuationRow canaryLookupKey .constant
     canaryContinuation]

private def keyedHitCanarySpace : Space := keyedHitCanaryAtoms.toFinset

private theorem keyedHitCanaryAtoms_nodup :
    keyedHitCanaryAtoms.Nodup := by decide +kernel

private theorem keyedHitCanaryAtoms_supported :
    cSupportedSourceExecFacts keyedHitCanaryAtoms =
      [lookupHitContinuationDirective] := by
  rfl

theorem keyedHitCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace keyedHitCanarySpace) =
      some lookupHitContinuationDirective := by
  exact reflective_selects_of_computable_supported_singleton
    keyedHitCanaryAtoms lookupHitContinuationDirective
    keyedHitCanaryAtoms_nodup keyedHitCanaryAtoms_supported

private theorem keyedHitCanary_fire_agreement :
    (cFireReflectiveSourceExecFact keyedHitCanaryAtoms
        lookupHitContinuationDirective).toFinset =
      fireReflectiveSourceExecFact keyedHitCanarySpace
        lookupHitContinuationDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    keyedHitCanaryAtoms lookupHitContinuationDirective
    keyedHitCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      lookupHitContinuationDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      keyedHitCanaryAtoms lookupHitContinuationDirective
      keyedHitCanaryAtoms_nodup)

theorem keyedHitCanary_emits_observation_and_exact_consumer :
    lookupFoundAtom canaryOwner canaryRequest sameNameCandidate
        existingOccurrence ∈
      fireReflectiveSourceExecFact keyedHitCanarySpace
        lookupHitContinuationDirective /\
    canaryContinuation ∈
      fireReflectiveSourceExecFact keyedHitCanarySpace
        lookupHitContinuationDirective := by
  rw [← keyedHitCanary_fire_agreement]
  decide +kernel

theorem keyedHitRule_rejects_wrong_continuation_key :
    (cmatchInputSpec []
      [lookupHitContinuationRule,
       keyedLookupAtom canaryOwner canaryLookupKey canaryRequest
         sameNameCandidate objectRootKey canaryNext,
       objectLinkAtom canaryOwner objectRootKey canaryNext existingOccurrence,
       objectLookupFoundContinuationRow wrongCanaryLookupKey .constant
         canaryContinuation]
      lookupHitContinuationDirective.rule.input).isEmpty = true := by
  decide +kernel

/-! ## Opaque reinstallation controls -/

private def reloadCanaryAtoms : List Atom :=
  [objectLookupReloadRule, objectLookupReloadTriggerAtom canaryOwner] ++
    objectLookupStaticRows

private def reloadCanarySpace : Space := reloadCanaryAtoms.toFinset

private theorem reloadCanaryAtoms_nodup : reloadCanaryAtoms.Nodup := by
  decide +kernel

private theorem reloadCanaryAtoms_supported :
    cSupportedSourceExecFacts reloadCanaryAtoms =
      [objectLookupReloadDirective] := by
  rfl

theorem reloadCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace reloadCanarySpace) =
      some objectLookupReloadDirective := by
  exact reflective_selects_of_computable_supported_singleton
    reloadCanaryAtoms objectLookupReloadDirective reloadCanaryAtoms_nodup
    reloadCanaryAtoms_supported

private theorem reloadCanary_fire_agreement :
    (cFireReflectiveSourceExecFact reloadCanaryAtoms
        objectLookupReloadDirective).toFinset =
      fireReflectiveSourceExecFact reloadCanarySpace
        objectLookupReloadDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    reloadCanaryAtoms objectLookupReloadDirective reloadCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      objectLookupReloadDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      reloadCanaryAtoms objectLookupReloadDirective reloadCanaryAtoms_nodup)

theorem reloadCanary_reinstalls_hit :
    lookupHitRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        objectLookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_reinstalls_missing :
    lookupMissingRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        objectLookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_reinstalls_advance :
    lookupAdvanceRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        objectLookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies reloadCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact reloadCanarySpace
          objectLookupReloadDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected reloadCanary_selects_directive)

#print axioms constant_occupied_rejects
#print axioms variable_historical_variable_reactivates
#print axioms decodeObjectInventoryRows_objectInventoryRows
#print axioms objectInventoryRows_injective
#print axioms objectInventoryRows_getLast?
#print axioms objectLink_mem_objectInventoryRows_has_entry
#print axioms lookupRules_extract_exact
#print axioms objectLookupRuleRow_not_proofNeutral
#print axioms hitCanary_fires_source_occurrence
#print axioms hitCanary_inhabits_target_native_type
#print axioms missingCanary_fires_explicit_frontier
#print axioms missingCanary_inhabits_target_native_type
#print axioms missingRule_rejects_wrong_frontier
#print axioms keyedHitCanary_emits_observation_and_exact_consumer
#print axioms keyedHitRule_rejects_wrong_continuation_key
#print axioms reloadCanary_reinstalls_hit
#print axioms reloadCanary_reinstalls_missing
#print axioms reloadCanary_reinstalls_advance
#print axioms reloadCanary_inhabits_target_native_type

end Mettapedia.Languages.Metamath.MM2SourceObjectLookup
