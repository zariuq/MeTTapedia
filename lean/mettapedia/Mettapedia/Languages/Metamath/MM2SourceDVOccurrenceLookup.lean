import Mettapedia.GSLT.Core.FiniteOccurrenceLookup
import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection

/-!
# Source-derived DV-occurrence lookup in ordinary MM2

Repeated Metamath `$d` declarations have two different identities.  Pair
equality determines the shared proof capability, while occurrence position
determines which declaration a scope exit removes.  This module retains both:
the semantic lookup is keyed by a string pair, and the concrete linked ledger
uses exact natural-number occurrence cursors.

The linked rows are a representation and execution carrier, not an admission
boundary.  Their canonical decoder and source-provenance theorems establish
which rows are emitted from a `DVLicenseProjection`; later declaration rules
must consume only that source-owned carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Semantic finite lookup -/

abbrev DVPair := String × String

def semanticEntry (occurrence : MarkedDVOccurrence) :
    Entry DVPair MarkedDVOccurrence :=
  { key := occurrence.pair, value := occurrence }

def semanticInventory (projection : DVLicenseProjection) :
    List (Entry DVPair MarkedDVOccurrence) :=
  (markOccurrences projection.distinctOccurrences).map semanticEntry

abbrev SemanticState :=
  FiniteOccurrenceLookup.State DVPair MarkedDVOccurrence

def semanticGSLT : GSLT :=
  FiniteOccurrenceLookup.gslt DVPair MarkedDVOccurrence

/-- The occurrence lookup passes through OSLF before native-type use. -/
def semanticLookupNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  FiniteOccurrenceLookup.lookupNTT DVPair MarkedDVOccurrence

def semanticLookup (pair : DVPair) (projection : DVLicenseProjection) :
    Observation MarkedDVOccurrence :=
  FiniteOccurrenceLookup.lookup pair (semanticInventory projection)

/-- Every semantic lookup has a finite proof-relevant path to its exact
first-match or missing observation. -/
def semanticComplete (pair : DVPair) (projection : DVLicenseProjection) :
    semanticGSLT.RewritePath
      (FiniteOccurrenceLookup.initial pair (semanticInventory projection))
      (.finished pair (semanticInventory projection)
        (semanticLookup pair projection)) := by
  exact FiniteOccurrenceLookup.complete pair (semanticInventory projection)

/-- A successful semantic observation reconstructs an exact marked source
occurrence; it cannot manufacture a pair or marker. -/
theorem semanticLookup_found_has_source_occurrence
    (pair : DVPair) (projection : DVLicenseProjection)
    (position : Nat) (marked : MarkedDVOccurrence)
    (found : semanticLookup pair projection =
      .found position marked) :
    ∃ occurrence ∈ markOccurrences projection.distinctOccurrences,
      occurrence.pair = pair ∧ occurrence = marked := by
  have source :=
    FiniteOccurrenceLookup.lookupFrom_found_has_source_occurrence
      0 pair (semanticInventory projection) position marked (by
        simpa [semanticLookup, FiniteOccurrenceLookup.lookup] using found)
  simpa [semanticInventory, semanticEntry] using source

/-! ## Canonical occurrence-indexed representation -/

def dvOccurrenceKindAtom : DVOccurrenceKind → Atom
  | .first => .symbol "mm-source-dv-occurrence-first"
  | .duplicate => .symbol "mm-source-dv-occurrence-duplicate"

def decodeDVOccurrenceKindAtom : Atom → Option DVOccurrenceKind
  | .symbol "mm-source-dv-occurrence-first" => some .first
  | .symbol "mm-source-dv-occurrence-duplicate" => some .duplicate
  | _ => none

@[simp] theorem decodeDVOccurrenceKindAtom_dvOccurrenceKindAtom
    (kind : DVOccurrenceKind) :
    decodeDVOccurrenceKindAtom (dvOccurrenceKindAtom kind) = some kind := by
  cases kind <;> rfl

theorem dvOccurrenceKindAtom_injective :
    Function.Injective dvOccurrenceKindAtom := by
  intro left right equal
  have decoded := congrArg decodeDVOccurrenceKindAtom equal
  simpa using decoded

def markedDVOccurrenceAtom (occurrence : MarkedDVOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-entry",
      stringPairAtom occurrence.pair,
      dvOccurrenceKindAtom occurrence.kind]

def decodeMarkedDVOccurrenceAtom : Atom → Option MarkedDVOccurrence
  | .expression
      [.symbol "mm-source-dv-occurrence-entry", encodedPair, encodedKind] => do
      let pair <- decodeStringPairAtom encodedPair
      let kind <- decodeDVOccurrenceKindAtom encodedKind
      pure { pair, kind }
  | _ => none

@[simp] theorem decodeMarkedDVOccurrenceAtom_markedDVOccurrenceAtom
    (occurrence : MarkedDVOccurrence) :
    decodeMarkedDVOccurrenceAtom (markedDVOccurrenceAtom occurrence) =
      some occurrence := by
  cases occurrence
  simp [decodeMarkedDVOccurrenceAtom, markedDVOccurrenceAtom]

theorem markedDVOccurrenceAtom_injective :
    Function.Injective markedDVOccurrenceAtom := by
  intro left right equal
  have decoded := congrArg decodeMarkedDVOccurrenceAtom equal
  simpa using decoded

def dvOccurrenceLinkAtAtom (owner cursor next : Atom)
    (occurrence : MarkedDVOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-link", owner, cursor, next,
      markedDVOccurrenceAtom occurrence]

/-- Canonical snapshot link.  Runtime append protocols may instead use
source-derived opaque cursors through `dvOccurrenceLinkAtAtom`. -/
def dvOccurrenceLinkAtom (owner : Atom) (position : Nat)
    (occurrence : MarkedDVOccurrence) : Atom :=
  dvOccurrenceLinkAtAtom owner (natAtom position) (natAtom (position + 1))
    occurrence

def dvOccurrenceFrontierAtAtom (owner cursor : Atom) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-frontier", owner, cursor]

/-- Canonical numeric snapshot frontier. -/
def dvOccurrenceFrontierAtom (owner : Atom) (position : Nat) : Atom :=
  dvOccurrenceFrontierAtAtom owner (natAtom position)

@[simp] theorem dvOccurrenceLinkAtom_eq_at (owner : Atom) (position : Nat)
    (occurrence : MarkedDVOccurrence) :
    dvOccurrenceLinkAtom owner position occurrence =
      dvOccurrenceLinkAtAtom owner (natAtom position) (natAtom (position + 1))
        occurrence := rfl

@[simp] theorem dvOccurrenceFrontierAtom_eq_at (owner : Atom)
    (position : Nat) :
    dvOccurrenceFrontierAtom owner position =
      dvOccurrenceFrontierAtAtom owner (natAtom position) := rfl

def dvOccurrenceRowsFrom (owner : Atom) (position : Nat) :
    List MarkedDVOccurrence → List Atom
  | [] => [dvOccurrenceFrontierAtom owner position]
  | occurrence :: rest =>
      dvOccurrenceLinkAtom owner position occurrence ::
        dvOccurrenceRowsFrom owner (position + 1) rest

def dvOccurrenceRows (owner : Atom)
    (occurrences : List MarkedDVOccurrence) : List Atom :=
  dvOccurrenceRowsFrom owner 0 occurrences

def projectionRows (owner : Atom) (projection : DVLicenseProjection) :
    List Atom :=
  dvOccurrenceRows owner (markOccurrences projection.distinctOccurrences)

def decodeDVOccurrenceLinkAtom (owner : Atom) (expectedPosition : Nat) :
    Atom → Option MarkedDVOccurrence
  | .expression
      [.symbol "mm-source-dv-occurrence-link", actualOwner,
        encodedPosition, encodedNext, encodedOccurrence] => do
      guard (actualOwner == owner)
      guard (encodedPosition == natAtom expectedPosition)
      guard (encodedNext == natAtom (expectedPosition + 1))
      decodeMarkedDVOccurrenceAtom encodedOccurrence
  | _ => none

def decodeDVOccurrenceRowsFrom (owner : Atom) (position : Nat) :
    List Atom → Option (List MarkedDVOccurrence)
  | [frontier] =>
      if frontier == dvOccurrenceFrontierAtom owner position then
        some []
      else
        none
  | row :: rest => do
      let occurrence <- decodeDVOccurrenceLinkAtom owner position row
      let occurrences <- decodeDVOccurrenceRowsFrom owner (position + 1) rest
      pure (occurrence :: occurrences)
  | _ => none
termination_by rows => rows.length

def decodeDVOccurrenceRows (owner : Atom) (rows : List Atom) :
    Option (List MarkedDVOccurrence) :=
  decodeDVOccurrenceRowsFrom owner 0 rows

@[simp] theorem decodeDVOccurrenceRowsFrom_dvOccurrenceRowsFrom
    (owner : Atom) (position : Nat)
    (occurrences : List MarkedDVOccurrence) :
    decodeDVOccurrenceRowsFrom owner position
      (dvOccurrenceRowsFrom owner position occurrences) = some occurrences := by
  induction occurrences generalizing position with
  | nil =>
      simp [decodeDVOccurrenceRowsFrom, dvOccurrenceRowsFrom,
        dvOccurrenceFrontierAtom, dvOccurrenceFrontierAtAtom]
  | cons occurrence rest induction =>
      cases rest with
      | nil =>
          simp [decodeDVOccurrenceRowsFrom, dvOccurrenceRowsFrom,
            decodeDVOccurrenceLinkAtom, dvOccurrenceLinkAtom,
            dvOccurrenceLinkAtAtom, dvOccurrenceFrontierAtom,
            dvOccurrenceFrontierAtAtom]
      | cons next tail =>
          simp [decodeDVOccurrenceRowsFrom, dvOccurrenceRowsFrom,
            decodeDVOccurrenceLinkAtom, dvOccurrenceLinkAtom,
            dvOccurrenceLinkAtAtom]
          exact induction (position + 1)

@[simp] theorem decodeDVOccurrenceRows_dvOccurrenceRows
    (owner : Atom) (occurrences : List MarkedDVOccurrence) :
    decodeDVOccurrenceRows owner (dvOccurrenceRows owner occurrences) =
      some occurrences := by
  exact decodeDVOccurrenceRowsFrom_dvOccurrenceRowsFrom owner 0 occurrences

@[simp] theorem decodeDVOccurrenceRows_projectionRows
    (owner : Atom) (projection : DVLicenseProjection) :
    decodeDVOccurrenceRows owner (projectionRows owner projection) =
      some (markOccurrences projection.distinctOccurrences) := by
  exact decodeDVOccurrenceRows_dvOccurrenceRows owner _

theorem dvOccurrenceRows_injective (owner : Atom) :
    Function.Injective (dvOccurrenceRows owner) := by
  intro left right equal
  have decoded := congrArg (decodeDVOccurrenceRows owner) equal
  simpa using decoded

@[simp] theorem dvOccurrenceRowsFrom_length (owner : Atom) (position : Nat)
    (occurrences : List MarkedDVOccurrence) :
    (dvOccurrenceRowsFrom owner position occurrences).length =
      occurrences.length + 1 := by
  induction occurrences generalizing position with
  | nil => rfl
  | cons occurrence rest induction =>
      simp [dvOccurrenceRowsFrom, induction]

@[simp] theorem dvOccurrenceRows_length (owner : Atom)
    (occurrences : List MarkedDVOccurrence) :
    (dvOccurrenceRows owner occurrences).length = occurrences.length + 1 := by
  exact dvOccurrenceRowsFrom_length owner 0 occurrences

@[simp] theorem dvOccurrenceRowsFrom_getLast?
    (owner : Atom) (position : Nat)
    (occurrences : List MarkedDVOccurrence) :
    (dvOccurrenceRowsFrom owner position occurrences).getLast? =
      some (dvOccurrenceFrontierAtom owner (position + occurrences.length)) := by
  induction occurrences generalizing position with
  | nil => rfl
  | cons occurrence rest induction =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          change
            (dvOccurrenceLinkAtom owner position occurrence ::
              dvOccurrenceRowsFrom owner (position + 1)
                (next :: tail)).getLast? =
              some (dvOccurrenceFrontierAtom owner
                (position + (occurrence :: next :: tail).length))
          rw [List.getLast?_cons_of_ne_nil]
          · rw [induction (position + 1)]
            apply congrArg some
            apply congrArg (dvOccurrenceFrontierAtom owner)
            simp only [List.length_cons]
            omega
          · simp [dvOccurrenceRowsFrom]

@[simp] theorem dvOccurrenceRows_getLast? (owner : Atom)
    (occurrences : List MarkedDVOccurrence) :
    (dvOccurrenceRows owner occurrences).getLast? =
      some (dvOccurrenceFrontierAtom owner occurrences.length) := by
  unfold dvOccurrenceRows
  rw [dvOccurrenceRowsFrom_getLast?]
  simp

/-- A canonical link row carries an exact occurrence of the represented
ordered ledger. -/
theorem dvOccurrenceLink_mem_rowsFrom_has_occurrence
    (owner : Atom) (start position : Nat)
    (occurrence : MarkedDVOccurrence)
    (occurrences : List MarkedDVOccurrence)
    (member : dvOccurrenceLinkAtom owner position occurrence ∈
      dvOccurrenceRowsFrom owner start occurrences) :
    occurrence ∈ occurrences := by
  induction occurrences generalizing start with
  | nil =>
      simp [dvOccurrenceRowsFrom, dvOccurrenceLinkAtom,
        dvOccurrenceLinkAtAtom, dvOccurrenceFrontierAtom,
        dvOccurrenceFrontierAtAtom] at member
  | cons head tail induction =>
      simp only [dvOccurrenceRowsFrom, List.mem_cons] at member
      rcases member with equal | member
      · have argumentsEqual :
            [.symbol "mm-source-dv-occurrence-link", owner, natAtom position,
              natAtom (position + 1), markedDVOccurrenceAtom occurrence] =
            [.symbol "mm-source-dv-occurrence-link", owner, natAtom start,
              natAtom (start + 1), markedDVOccurrenceAtom head] :=
          Atom.expression.inj equal
        have encodedEqual : markedDVOccurrenceAtom occurrence =
            markedDVOccurrenceAtom head := by
          simpa using congrArg List.getLast? argumentsEqual
        have occurrenceEqual :=
          markedDVOccurrenceAtom_injective encodedEqual
        subst occurrence
        simp
      · exact List.mem_cons_of_mem head (induction (start + 1) member)

theorem dvOccurrenceLink_mem_rows_has_occurrence
    (owner : Atom) (position : Nat)
    (occurrence : MarkedDVOccurrence)
    (occurrences : List MarkedDVOccurrence)
    (member : dvOccurrenceLinkAtom owner position occurrence ∈
      dvOccurrenceRows owner occurrences) :
    occurrence ∈ occurrences := by
  exact dvOccurrenceLink_mem_rowsFrom_has_occurrence
    owner 0 position occurrence occurrences member

/-- The concrete projection cannot invent a pair absent from the authored
source occurrence ledger. -/
theorem dvOccurrenceLink_mem_projectionRows_has_source_pair
    (owner : Atom) (position : Nat)
    (occurrence : MarkedDVOccurrence)
    (projection : DVLicenseProjection)
    (member : dvOccurrenceLinkAtom owner position occurrence ∈
      projectionRows owner projection) :
    occurrence.pair ∈ projection.distinctOccurrences := by
  exact marked_mem_markOccurrences_has_source_pair
    projection.distinctOccurrences occurrence
    (dvOccurrenceLink_mem_rows_has_occurrence owner position occurrence
      (markOccurrences projection.distinctOccurrences) member)

/-! ## Ordinary MM2 finite scan -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def lookupHitLocation : Atom :=
  location "00" "mm-source-dv-occurrence-lookup-hit"

private def lookupMissingLocation : Atom :=
  location "01" "mm-source-dv-occurrence-lookup-missing"

private def lookupAdvanceLocation : Atom :=
  location "02" "mm-source-dv-occurrence-lookup-advance"

private def lookupReloadLocation : Atom :=
  location "36" "mm-source-dv-occurrence-lookup-reload"

private def lookupTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-lookup", .var "source",
      .var "request", .var "candidate-pair", .var "cursor",
      .var "frontier"]

private def lookupAtFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-lookup", .var "source",
      .var "request", .var "candidate-pair", .var "frontier",
      .var "frontier"]

private def matchingLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-link", .var "source",
      .var "cursor", .var "next-cursor",
      .expression
        [.symbol "mm-source-dv-occurrence-entry", .var "candidate-pair",
          .var "occurrence-kind"]]

private def anyLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-link", .var "source",
      .var "cursor", .var "next-cursor",
      .expression
        [.symbol "mm-source-dv-occurrence-entry", .var "occupied-pair",
          .var "occurrence-kind"]]

private def frontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-frontier", .var "source",
      .var "frontier"]

private def lookupFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-found", .var "source",
      .var "request", .var "candidate-pair", .var "cursor",
      .expression
        [.symbol "mm-source-dv-occurrence-entry", .var "candidate-pair",
          .var "occurrence-kind"]]

private def lookupMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-missing", .var "source",
      .var "request", .var "candidate-pair"]

private def lookupNextTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-lookup", .var "source",
      .var "request", .var "candidate-pair", .var "next-cursor",
      .var "frontier"]

def lookupReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-source-dv-occurrence-lookup", .var "source"]

def lookupReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-occurrence-lookup", owner]

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

private def hitSelf : Atom :=
  selfTemplate lookupHitLocation "dv-occurrence-hit"

private def hitPatterns : List Atom :=
  [hitSelf, lookupTemplate, matchingLinkTemplate]

private def hitSinks : List Sink :=
  [.add hitSelf, .remove lookupTemplate, .add lookupFoundTemplate]

def lookupHitRule : Atom :=
  mkRule lookupHitLocation hitPatterns hitSinks

def lookupHitDirective : SourceExecFact where
  atom := lookupHitRule
  loc := lookupHitLocation
  rule :=
    { priority := 0
      name := "mm-source-dv-occurrence-lookup-hit"
      input := .compat (mkPattern hitPatterns)
      guards := []
      tmpl := mkTemplate hitSinks }

theorem extract_lookupHitRule_exact :
    extractSupportedSourceExecFact lookupHitRule = some lookupHitDirective := by
  rfl

private def missingSelf : Atom :=
  selfTemplate lookupMissingLocation "dv-occurrence-missing"

private def missingPatterns : List Atom :=
  [missingSelf, lookupAtFrontierTemplate, frontierTemplate]

private def missingSinks : List Sink :=
  [.add missingSelf, .remove lookupAtFrontierTemplate,
    .add lookupMissingTemplate]

def lookupMissingRule : Atom :=
  mkRule lookupMissingLocation missingPatterns missingSinks

def lookupMissingDirective : SourceExecFact where
  atom := lookupMissingRule
  loc := lookupMissingLocation
  rule :=
    { priority := 1
      name := "mm-source-dv-occurrence-lookup-missing"
      input := .compat (mkPattern missingPatterns)
      guards := []
      tmpl := mkTemplate missingSinks }

theorem extract_lookupMissingRule_exact :
    extractSupportedSourceExecFact lookupMissingRule =
      some lookupMissingDirective := by
  rfl

private def advanceSelf : Atom :=
  selfTemplate lookupAdvanceLocation "dv-occurrence-advance"

private def advancePatterns : List Atom :=
  [advanceSelf, lookupTemplate, anyLinkTemplate]

private def advanceSinks : List Sink :=
  [.remove lookupTemplate, .add lookupNextTemplate,
    .add lookupReloadTriggerTemplate]

def lookupAdvanceRule : Atom :=
  mkRule lookupAdvanceLocation advancePatterns advanceSinks

def lookupAdvanceDirective : SourceExecFact where
  atom := lookupAdvanceRule
  loc := lookupAdvanceLocation
  rule :=
    { priority := 2
      name := "mm-source-dv-occurrence-lookup-advance"
      input := .compat (mkPattern advancePatterns)
      guards := []
      tmpl := mkTemplate advanceSinks }

theorem extract_lookupAdvanceRule_exact :
    extractSupportedSourceExecFact lookupAdvanceRule =
      some lookupAdvanceDirective := by
  rfl

def lookupScanRules : List Atom :=
  [lookupHitRule, lookupMissingRule, lookupAdvanceRule]

def lookupScanDirectives : List SourceExecFact :=
  [lookupHitDirective, lookupMissingDirective, lookupAdvanceDirective]

/-! ## Verifier-owned rule reinstallation -/

def lookupRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-occurrence-lookup-rule", rule]

private def reloadSelf : Atom :=
  selfTemplate lookupReloadLocation "dv-occurrence-reload"

private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-occurrence-lookup-rule",
      .var "dv-occurrence-lookup-rule"]

private def reloadPatterns : List Atom :=
  [reloadSelf, lookupReloadTriggerTemplate, reloadRuleTemplate]

private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove lookupReloadTriggerTemplate,
    .add (.var "dv-occurrence-lookup-rule")]

def lookupReloadRule : Atom :=
  mkRule lookupReloadLocation reloadPatterns reloadSinks

def lookupReloadDirective : SourceExecFact where
  atom := lookupReloadRule
  loc := lookupReloadLocation
  rule :=
    { priority := 36
      name := "mm-source-dv-occurrence-lookup-reload"
      input := .compat (mkPattern reloadPatterns)
      guards := []
      tmpl := mkTemplate reloadSinks }

theorem extract_lookupReloadRule_exact :
    extractSupportedSourceExecFact lookupReloadRule =
      some lookupReloadDirective := by
  rfl

def lookupStaticRows : List Atom :=
  lookupScanRules.map lookupRuleRow

@[simp] theorem lookupRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (lookupRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-occurrence-lookup-rule" [rule] (by decide)

def lookupRules : List Atom :=
  lookupScanRules ++ [lookupReloadRule]

def lookupDirectives : List SourceExecFact :=
  lookupScanDirectives ++ [lookupReloadDirective]

theorem lookupRules_extract_exact :
    lookupRules.filterMap extractSupportedSourceExecFact = lookupDirectives := by
  rfl

/-! ## Source-bound constructors and controls -/

def lookupAtAtom (owner request : Atom) (pair : DVPair)
    (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-lookup", owner, request,
      stringPairAtom pair, cursor, frontier]

def lookupAtom (owner request : Atom) (pair : DVPair)
    (cursor frontier : Nat) : Atom :=
  lookupAtAtom owner request pair (natAtom cursor) (natAtom frontier)

def lookupFoundAtAtom (owner request : Atom) (pair : DVPair)
    (cursor : Atom) (occurrence : MarkedDVOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-found", owner, request,
      stringPairAtom pair, cursor,
      markedDVOccurrenceAtom occurrence]

def lookupFoundAtom (owner request : Atom) (pair : DVPair)
    (position : Nat) (occurrence : MarkedDVOccurrence) : Atom :=
  lookupFoundAtAtom owner request pair (natAtom position) occurrence

def lookupMissingAtom (owner request : Atom) (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-missing", owner, request,
      stringPairAtom pair]

private def canaryOwner : Atom := .symbol "dv-occurrence-source"
private def canaryRequest : Atom := .symbol "dv-declaration-request"

private def firstXY : MarkedDVOccurrence :=
  { pair := ("x", "y"), kind := .first }

private def duplicateXY : MarkedDVOccurrence :=
  { pair := ("x", "y"), kind := .duplicate }

private def firstUV : MarkedDVOccurrence :=
  { pair := ("u", "v"), kind := .first }

private def canaryOccurrences : List MarkedDVOccurrence :=
  [firstXY, duplicateXY, firstUV]

private def canaryProjection : DVLicenseProjection :=
  { activeFloatingVariables := ["x", "y", "u", "v"]
    distinctOccurrences := [("x", "y"), ("x", "y"), ("u", "v")] }

theorem canaryProjection_marks_occurrences_exactly :
    markOccurrences canaryProjection.distinctOccurrences =
      canaryOccurrences := by
  decide +kernel

theorem canaryProjection_rows_decode_exactly :
    decodeDVOccurrenceRows canaryOwner
        (projectionRows canaryOwner canaryProjection) =
      some canaryOccurrences := by
  rw [decodeDVOccurrenceRows_projectionRows,
    canaryProjection_marks_occurrences_exactly]

theorem semanticCanary_finds_first_equal_pair :
    semanticLookup ("x", "y") canaryProjection =
      .found 0 firstXY := by
  decide +kernel

theorem semanticCanary_misses_at_exact_frontier :
    semanticLookup ("q", "r") canaryProjection = .missing 3 := by
  decide +kernel

def semanticCanary_complete_path :
    semanticGSLT.RewritePath
      (FiniteOccurrenceLookup.initial ("x", "y")
        (semanticInventory canaryProjection))
      (.finished ("x", "y") (semanticInventory canaryProjection)
        (.found 0 firstXY)) := by
  simpa [semanticCanary_finds_first_equal_pair] using
    semanticComplete ("x", "y") canaryProjection

private def hitCanaryAtoms : List Atom :=
  [lookupHitRule,
    lookupAtom canaryOwner canaryRequest ("x", "y") 0 3,
    dvOccurrenceLinkAtom canaryOwner 0 firstXY]

private def hitCanarySpace : Space := hitCanaryAtoms.toFinset

private theorem hitCanaryAtoms_nodup : hitCanaryAtoms.Nodup := by
  decide +kernel

private theorem hitCanaryAtoms_supported :
    cSupportedSourceExecFacts hitCanaryAtoms = [lookupHitDirective] := by
  rfl

theorem hitCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace hitCanarySpace) =
      some lookupHitDirective := by
  exact reflective_selects_of_computable_supported_singleton
    hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup
    hitCanaryAtoms_supported

private theorem hitCanary_fire_agreement :
    (cFireReflectiveSourceExecFact hitCanaryAtoms
        lookupHitDirective).toFinset =
      fireReflectiveSourceExecFact hitCanarySpace lookupHitDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      lookupHitDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      hitCanaryAtoms lookupHitDirective hitCanaryAtoms_nodup)

theorem hitCanary_fires_exact_first_occurrence :
    lookupFoundAtom canaryOwner canaryRequest ("x", "y") 0 firstXY ∈
      fireReflectiveSourceExecFact hitCanarySpace lookupHitDirective := by
  rw [← hitCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem hitCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies hitCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact hitCanarySpace
          lookupHitDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected hitCanary_selects_directive)

private def advanceCanaryAtoms : List Atom :=
  [lookupAdvanceRule,
    lookupAtom canaryOwner canaryRequest ("u", "v") 0 3,
    dvOccurrenceLinkAtom canaryOwner 0 firstXY]

private def advanceCanarySpace : Space := advanceCanaryAtoms.toFinset

private theorem advanceCanaryAtoms_nodup : advanceCanaryAtoms.Nodup := by
  decide +kernel

private theorem advanceCanaryAtoms_supported :
    cSupportedSourceExecFacts advanceCanaryAtoms =
      [lookupAdvanceDirective] := by
  rfl

theorem advanceCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace advanceCanarySpace) =
      some lookupAdvanceDirective := by
  exact reflective_selects_of_computable_supported_singleton
    advanceCanaryAtoms lookupAdvanceDirective advanceCanaryAtoms_nodup
    advanceCanaryAtoms_supported

private theorem advanceCanary_fire_agreement :
    (cFireReflectiveSourceExecFact advanceCanaryAtoms
        lookupAdvanceDirective).toFinset =
      fireReflectiveSourceExecFact advanceCanarySpace
        lookupAdvanceDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    advanceCanaryAtoms lookupAdvanceDirective advanceCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      lookupAdvanceDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      advanceCanaryAtoms lookupAdvanceDirective advanceCanaryAtoms_nodup)

theorem advanceCanary_moves_to_exact_successor :
    lookupAtom canaryOwner canaryRequest ("u", "v") 1 3 ∈
      fireReflectiveSourceExecFact advanceCanarySpace
        lookupAdvanceDirective := by
  rw [← advanceCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem advanceCanary_requests_rule_reload :
    lookupReloadTriggerAtom canaryOwner ∈
      fireReflectiveSourceExecFact advanceCanarySpace
        lookupAdvanceDirective := by
  rw [← advanceCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def missingCanaryAtoms : List Atom :=
  [lookupMissingRule,
    lookupAtom canaryOwner canaryRequest ("q", "r") 3 3,
    dvOccurrenceFrontierAtom canaryOwner 3]

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

private theorem missingCanary_fire_agreement :
    (cFireReflectiveSourceExecFact missingCanaryAtoms
        lookupMissingDirective).toFinset =
      fireReflectiveSourceExecFact missingCanarySpace
        lookupMissingDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    missingCanaryAtoms lookupMissingDirective missingCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      lookupMissingDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      missingCanaryAtoms lookupMissingDirective missingCanaryAtoms_nodup)

theorem missingCanary_fires_only_at_exact_frontier :
    lookupMissingAtom canaryOwner canaryRequest ("q", "r") ∈
      fireReflectiveSourceExecFact missingCanarySpace
        lookupMissingDirective := by
  rw [← missingCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem missingCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies missingCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact missingCanarySpace
          lookupMissingDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected missingCanary_selects_directive)

/-- A missing observation cannot fire at a cursor other than the exact
source-owned frontier. -/
theorem missingRule_rejects_wrong_frontier :
    (cmatchInputSpec []
      [lookupMissingRule,
        lookupAtom canaryOwner canaryRequest ("q", "r") 2 3,
        dvOccurrenceFrontierAtom canaryOwner 3]
      lookupMissingDirective.rule.input).isEmpty = true := by
  decide +kernel

/-- A row owned by another source cannot answer this source's lookup. -/
theorem hitRule_rejects_wrong_owner :
    (cmatchInputSpec []
      [lookupHitRule,
        lookupAtom canaryOwner canaryRequest ("x", "y") 0 3,
        dvOccurrenceLinkAtom (.symbol "other-source") 0 firstXY]
      lookupHitDirective.rule.input).isEmpty = true := by
  decide +kernel

private def reloadCanaryAtoms : List Atom :=
  [lookupReloadRule, lookupReloadTriggerAtom canaryOwner] ++ lookupStaticRows

private def reloadCanarySpace : Space := reloadCanaryAtoms.toFinset

private theorem reloadCanaryAtoms_nodup : reloadCanaryAtoms.Nodup := by
  decide +kernel

private theorem reloadCanaryAtoms_supported :
    cSupportedSourceExecFacts reloadCanaryAtoms = [lookupReloadDirective] := by
  rfl

theorem reloadCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace reloadCanarySpace) =
      some lookupReloadDirective := by
  exact reflective_selects_of_computable_supported_singleton
    reloadCanaryAtoms lookupReloadDirective reloadCanaryAtoms_nodup
    reloadCanaryAtoms_supported

private theorem reloadCanary_fire_agreement :
    (cFireReflectiveSourceExecFact reloadCanaryAtoms
        lookupReloadDirective).toFinset =
      fireReflectiveSourceExecFact reloadCanarySpace
        lookupReloadDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    reloadCanaryAtoms lookupReloadDirective reloadCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      lookupReloadDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      reloadCanaryAtoms lookupReloadDirective reloadCanaryAtoms_nodup)

theorem reloadCanary_reinstalls_hit :
    lookupHitRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        lookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_reinstalls_missing :
    lookupMissingRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        lookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_reinstalls_advance :
    lookupAdvanceRule ∈
      fireReflectiveSourceExecFact reloadCanarySpace
        lookupReloadDirective := by
  rw [← reloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem reloadCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies reloadCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact reloadCanarySpace
          lookupReloadDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected reloadCanary_selects_directive)

/-! ## Continuous source-derived scans -/

private def continuousHitProgram : List Atom :=
  lookupRules ++ lookupStaticRows ++
    [lookupAtom canaryOwner canaryRequest ("u", "v") 0 3] ++
      projectionRows canaryOwner canaryProjection

/-- The executable work queue skips two unequal occurrences, reloads its
finite rule inventory as required, and returns the exact third occurrence.
The original request is consumed rather than left as residue. -/
theorem continuousHitProgram_finds_exact_third_occurrence :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 9
        continuousHitProgram).1
    lookupFoundAtom canaryOwner canaryRequest ("u", "v") 2 firstUV ∈
        final ∧
      lookupAtom canaryOwner canaryRequest ("u", "v") 0 3 ∉ final ∧
      lookupFoundAtom canaryOwner canaryRequest ("u", "v") 1 firstUV ∉
        final := by
  decide +kernel

def continuousHitProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 9 continuousHitProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 9
        continuousHitProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 9
    continuousHitProgram

private def continuousMissingProgram : List Atom :=
  lookupRules ++ lookupStaticRows ++
    [lookupAtom canaryOwner canaryRequest ("q", "r") 0 3] ++
      projectionRows canaryOwner canaryProjection

/-- Missing is emitted only after all three source occurrences have been
crossed and the exact explicit frontier has been reached. -/
theorem continuousMissingProgram_reaches_exact_frontier :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 14
        continuousMissingProgram).1
    lookupMissingAtom canaryOwner canaryRequest ("q", "r") ∈ final ∧
      lookupAtom canaryOwner canaryRequest ("q", "r") 0 3 ∉ final := by
  decide +kernel

def continuousMissingProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 14 continuousMissingProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 14
        continuousMissingProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 14
    continuousMissingProgram

section AxiomAudit

#print axioms semanticComplete
#print axioms semanticLookup_found_has_source_occurrence
#print axioms markedDVOccurrenceAtom_injective
#print axioms decodeDVOccurrenceRows_projectionRows
#print axioms dvOccurrenceRows_injective
#print axioms dvOccurrenceRows_getLast?
#print axioms dvOccurrenceLink_mem_projectionRows_has_source_pair
#print axioms lookupRules_extract_exact
#print axioms lookupRuleRow_not_proofNeutral
#print axioms semanticCanary_complete_path
#print axioms hitCanary_fires_exact_first_occurrence
#print axioms hitCanary_inhabits_target_native_type
#print axioms advanceCanary_moves_to_exact_successor
#print axioms advanceCanary_requests_rule_reload
#print axioms missingCanary_fires_only_at_exact_frontier
#print axioms missingCanary_inhabits_target_native_type
#print axioms missingRule_rejects_wrong_frontier
#print axioms hitRule_rejects_wrong_owner
#print axioms reloadCanary_reinstalls_hit
#print axioms reloadCanary_reinstalls_missing
#print axioms reloadCanary_reinstalls_advance
#print axioms reloadCanary_inhabits_target_native_type
#print axioms continuousHitProgram_finds_exact_third_occurrence
#print axioms continuousHitProgram_has_oslf_native_trace
#print axioms continuousMissingProgram_reaches_exact_frontier
#print axioms continuousMissingProgram_has_oslf_native_trace

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
