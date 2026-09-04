import Mettapedia.Languages.Metamath.MM2SourceObjectLookup
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSourceExecAdd

/-!
# Historical variable-typecode lookup in ordinary MM2

Metamath assigns each variable one historical typecode at its first `$f`
declaration.  A later `$f` may reuse that assignment, but it may not change
it.  This module represents the history as one occurrence-preserving object
ledger plus one source-bound binding record per ledger occurrence.

The existing finite object lookup supplies cursor discipline and an explicit
missing observation.  The adapter below accepts a hit only when the exact
linked occurrence has its matching binding record.  It therefore reuses the
generic walker without turning a variable name into authority for an
unrelated typecode.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Source occurrence and semantic lookup -/

/-- One accepted `$f` occurrence carrying all three source names needed to
audit the historical assignment. -/
structure VariableTypecodeOccurrence where
  statementPosition : Nat
  label : LocatedName
  typecode : LocatedName
  variableName : LocatedName
deriving DecidableEq, Repr

def VariableTypecodeOccurrence.key
    (occurrence : VariableTypecodeOccurrence) : String :=
  occurrence.variableName.name

def semanticEntry (occurrence : VariableTypecodeOccurrence) :
    Entry String VariableTypecodeOccurrence :=
  { key := occurrence.key, value := occurrence }

abbrev SemanticState :=
  FiniteOccurrenceLookup.State String VariableTypecodeOccurrence

def semanticGSLT : GSLT :=
  FiniteOccurrenceLookup.gslt String VariableTypecodeOccurrence

/-- The historical lookup GSLT is interpreted through OSLF before its exact
target native type is used. -/
def semanticOSLF :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF semanticGSLT

def semanticNTT (target : SemanticState) :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
    semanticGSLT target

theorem semanticStep_inhabits_target_native_type
    {before after : SemanticState}
    (step : FiniteOccurrenceLookup.Step before after) :
    semanticOSLF.satisfies before (semanticNTT after).pred := by
  change
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      semanticGSLT).satisfies before
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          semanticGSLT after).pred
  rw [Mettapedia.OSLF.Framework.GSLTTypeSynthesis.satisfies_exactTargetNativeType_iff_step]
  exact step

/-! ## Exact MM2 representation -/

def variableTypecodeOccurrenceAtom
    (occurrence : VariableTypecodeOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-variable-typecode-occurrence",
      natAtom occurrence.statementPosition,
      locatedNameAtom occurrence.label,
      locatedNameAtom occurrence.typecode,
      locatedNameAtom occurrence.variableName]

def decodeVariableTypecodeOccurrenceAtom :
    Atom → Option VariableTypecodeOccurrence
  | .expression
      [.symbol "mm-source-variable-typecode-occurrence",
        encodedPosition, encodedLabel, encodedTypecode, encodedVariable] => do
      let statementPosition <- decodeNatAtom encodedPosition
      let label <- decodeLocatedNameAtom encodedLabel
      let typecode <- decodeLocatedNameAtom encodedTypecode
      let variableName <- decodeLocatedNameAtom encodedVariable
      pure { statementPosition, label, typecode, variableName }
  | _ => none

@[simp] theorem decodeVariableTypecodeOccurrenceAtom_encoded
    (occurrence : VariableTypecodeOccurrence) :
    decodeVariableTypecodeOccurrenceAtom
        (variableTypecodeOccurrenceAtom occurrence) = some occurrence := by
  cases occurrence
  simp [decodeVariableTypecodeOccurrenceAtom,
    variableTypecodeOccurrenceAtom]

theorem variableTypecodeOccurrenceAtom_injective :
    Function.Injective variableTypecodeOccurrenceAtom := by
  intro left right equal
  have decoded := congrArg decodeVariableTypecodeOccurrenceAtom equal
  simpa using decoded

def variableTypecodeLedgerOwner (owner : Atom) : Atom :=
  .expression [.symbol "mm-source-variable-typecode-ledger", owner]

theorem variableTypecodeLedgerOwner_injective :
    Function.Injective variableTypecodeLedgerOwner := by
  intro left right equal
  simpa [variableTypecodeLedgerOwner] using equal

def variableTypecodeObjectOccurrence
    (occurrence : VariableTypecodeOccurrence) : ObjectOccurrence :=
  { kind := .variable, occurrence := occurrence.variableName }

def variableTypecodeBindingAtom (owner : Atom)
    (occurrence : VariableTypecodeOccurrence) : Atom :=
  .expression
    [.symbol "mm-source-variable-typecode-binding", owner,
      objectOccurrenceAtom (variableTypecodeObjectOccurrence occurrence),
      .expression
        [.symbol "mm-source-variable-typecode-payload",
          natAtom occurrence.statementPosition,
          locatedNameAtom occurrence.label,
          locatedNameAtom occurrence.typecode]]

def decodeVariableTypecodeBindingAtom (owner : Atom) :
    Atom → Option VariableTypecodeOccurrence
  | .expression
      [.symbol "mm-source-variable-typecode-binding", actualOwner,
        encodedObject,
        .expression
          [.symbol "mm-source-variable-typecode-payload", encodedPosition,
            encodedLabel, encodedTypecode]] => do
      guard (actualOwner == owner)
      let object <- decodeObjectOccurrenceAtom encodedObject
      guard (object.kind == .variable)
      let statementPosition <- decodeNatAtom encodedPosition
      let label <- decodeLocatedNameAtom encodedLabel
      let typecode <- decodeLocatedNameAtom encodedTypecode
      let variableName := object.occurrence
      pure { statementPosition, label, typecode, variableName }
  | _ => none

@[simp] theorem decodeVariableTypecodeBindingAtom_encoded
    (owner : Atom) (occurrence : VariableTypecodeOccurrence) :
    decodeVariableTypecodeBindingAtom owner
        (variableTypecodeBindingAtom owner occurrence) = some occurrence := by
  simp [decodeVariableTypecodeBindingAtom, variableTypecodeBindingAtom]
  simp [variableTypecodeObjectOccurrence]

theorem variableTypecodeBindingAtom_injective (owner : Atom) :
    Function.Injective (variableTypecodeBindingAtom owner) := by
  intro left right equal
  have decoded := congrArg (decodeVariableTypecodeBindingAtom owner) equal
  simpa using decoded

def variableTypecodeInventoryRows (owner : Atom)
    (occurrences : List VariableTypecodeOccurrence) : List Atom :=
  objectInventoryRows (variableTypecodeLedgerOwner owner)
    (occurrences.map variableTypecodeObjectOccurrence)

def variableTypecodeBindingRows (owner : Atom)
    (occurrences : List VariableTypecodeOccurrence) : List Atom :=
  occurrences.map (variableTypecodeBindingAtom owner)

def variableTypecodeLedgerRows (owner : Atom)
    (occurrences : List VariableTypecodeOccurrence) : List Atom :=
  variableTypecodeInventoryRows owner occurrences ++
    variableTypecodeBindingRows owner occurrences

/-- Decode the linked key inventory and binding records independently, then
require exact occurrence-for-occurrence agreement. -/
def decodeVariableTypecodeLedgerRows (owner : Atom)
    (inventoryRows bindingRows : List Atom) :
    Option (List VariableTypecodeOccurrence) := do
  let objects <- decodeObjectInventoryRows (variableTypecodeLedgerOwner owner)
    inventoryRows
  let occurrences <- bindingRows.mapM (decodeVariableTypecodeBindingAtom owner)
  guard (objects == occurrences.map variableTypecodeObjectOccurrence)
  pure occurrences

@[simp] theorem decodeVariableTypecodeBindingRows_encoded
    (owner : Atom) (occurrences : List VariableTypecodeOccurrence) :
    (variableTypecodeBindingRows owner occurrences).mapM
        (decodeVariableTypecodeBindingAtom owner) = some occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences induction =>
      simp_all [variableTypecodeBindingRows]

@[simp] theorem decodeVariableTypecodeLedgerRows_encoded
    (owner : Atom) (occurrences : List VariableTypecodeOccurrence) :
    decodeVariableTypecodeLedgerRows owner
        (variableTypecodeInventoryRows owner occurrences)
        (variableTypecodeBindingRows owner occurrences) = some occurrences := by
  simp [decodeVariableTypecodeLedgerRows, variableTypecodeInventoryRows,
    decodeVariableTypecodeBindingRows_encoded]

private theorem variableTypecodeBindingAtom_not_mem_inventoryRowsFrom
    (owner ledgerOwner start : Atom)
    (occurrence : VariableTypecodeOccurrence)
    (objects : List ObjectOccurrence) :
    variableTypecodeBindingAtom owner occurrence ∉
      objectInventoryRowsFrom ledgerOwner start objects := by
  induction objects generalizing start with
  | nil =>
      simp [objectInventoryRowsFrom, objectFrontierAtom,
        variableTypecodeBindingAtom]
  | cons object objects induction =>
      simp only [objectInventoryRowsFrom, List.mem_cons, not_or]
      constructor
      · simp [objectLinkAtom, variableTypecodeBindingAtom]
      · exact induction (locatedNameAtom object.occurrence)

theorem variableTypecodeBinding_mem_ledgerRows_has_occurrence
    (owner : Atom) (occurrence : VariableTypecodeOccurrence)
    (occurrences : List VariableTypecodeOccurrence)
    (member : variableTypecodeBindingAtom owner occurrence ∈
      variableTypecodeLedgerRows owner occurrences) :
    occurrence ∈ occurrences := by
  rw [variableTypecodeLedgerRows, List.mem_append] at member
  rcases member with inventoryMember | bindingMember
  · exact False.elim
      (variableTypecodeBindingAtom_not_mem_inventoryRowsFrom owner
        (variableTypecodeLedgerOwner owner) objectRootKey occurrence
        (occurrences.map variableTypecodeObjectOccurrence) inventoryMember)
  · rw [variableTypecodeBindingRows, List.mem_map] at bindingMember
    obtain ⟨sourceOccurrence, sourceMember, equal⟩ := bindingMember
    have occurrenceEqual : sourceOccurrence = occurrence := by
      have decoded :=
        congrArg (decodeVariableTypecodeBindingAtom owner) equal
      simpa using decoded
    simpa [occurrenceEqual] using sourceMember

/-! ## Adapter from generic object-lookup observations -/

def variableTypecodeFoundAtom (owner request : Atom)
    (candidate : LocatedName) (occurrence : VariableTypecodeOccurrence) : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-found", owner, request,
      locatedNameAtom candidate,
      objectOccurrenceAtom (variableTypecodeObjectOccurrence occurrence),
      .expression
        [.symbol "mm-source-variable-typecode-payload",
          natAtom occurrence.statementPosition,
          locatedNameAtom occurrence.label,
          locatedNameAtom occurrence.typecode]]

def variableTypecodeMissingAtom (owner request : Atom)
    (candidate : LocatedName) : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-missing", owner, request,
      locatedNameAtom candidate]

@[simp] theorem variableTypecodeFoundAtom_not_proofNeutral
    (owner request : Atom) (candidate : LocatedName)
    (occurrence : VariableTypecodeOccurrence) :
    isProofNeutralInitialAtom
      (variableTypecodeFoundAtom owner request candidate occurrence) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-variable-typecode-found"
    [owner, request, locatedNameAtom candidate,
      objectOccurrenceAtom (variableTypecodeObjectOccurrence occurrence),
      .expression
        [.symbol "mm-source-variable-typecode-payload",
          natAtom occurrence.statementPosition,
          locatedNameAtom occurrence.label,
          locatedNameAtom occurrence.typecode]] (by decide)

private def foundLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-source-variable-typecode-found"]
private def missingLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-source-variable-typecode-missing"]

private def selfTemplate (location : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", location, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def candidateTemplate : Atom := .var "candidate"

private def historicalObjectTemplate : Atom := .var "historical-object"

private def payloadTemplate : Atom := .var "historical-payload"

private def ledgerOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-variable-typecode-ledger", .var "source"]

private def genericFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-found", ledgerOwnerTemplate, .var "request",
      candidateTemplate,
      historicalObjectTemplate]

private def bindingTemplate : Atom :=
  .expression
    [.symbol "mm-source-variable-typecode-binding", .var "source",
      historicalObjectTemplate, payloadTemplate]

private def foundTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-found", .var "source",
      .var "request", candidateTemplate, historicalObjectTemplate,
      payloadTemplate]

private def genericMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-missing", ledgerOwnerTemplate, .var "request",
      candidateTemplate]

private def missingTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-typecode-missing", .var "source",
      .var "request", candidateTemplate]

private def sinkAtom : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom => .expression [.symbol "head", natAtom count, atom]
  | .tail count atom => .expression [.symbol "tail", natAtom count, atom]

private def mkRule (location : Atom) (patterns : List Atom)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", location, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkAtom)]

private def mkDirective (atom location : Atom) (priority : Nat)
    (name : String) (patterns : List Atom) (sinks : List Sink) :
    SourceExecFact :=
  { atom
    loc := location
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def foundSelf : Atom :=
  selfTemplate foundLocation "variable-typecode-found"
private def foundPatterns : List Atom :=
  [foundSelf, genericFoundTemplate, bindingTemplate]
private def foundSinks : List Sink :=
  [.add foundSelf, .remove genericFoundTemplate, .add foundTemplate]

def variableTypecodeFoundRule : Atom :=
  mkRule foundLocation foundPatterns foundSinks
def variableTypecodeFoundDirective : SourceExecFact :=
  mkDirective variableTypecodeFoundRule foundLocation 0
    "mm-source-variable-typecode-found" foundPatterns foundSinks

private def missingSelf : Atom :=
  selfTemplate missingLocation "variable-typecode-missing"
private def missingPatterns : List Atom :=
  [missingSelf, genericMissingTemplate]
private def missingSinks : List Sink :=
  [.add missingSelf, .remove genericMissingTemplate, .add missingTemplate]

def variableTypecodeMissingRule : Atom :=
  mkRule missingLocation missingPatterns missingSinks
def variableTypecodeMissingDirective : SourceExecFact :=
  mkDirective variableTypecodeMissingRule missingLocation 1
    "mm-source-variable-typecode-missing" missingPatterns missingSinks

theorem extract_variableTypecodeFoundRule_exact :
    extractSupportedSourceExecFact variableTypecodeFoundRule =
      some variableTypecodeFoundDirective := by rfl

theorem extract_variableTypecodeMissingRule_exact :
    extractSupportedSourceExecFact variableTypecodeMissingRule =
      some variableTypecodeMissingDirective := by rfl

def variableTypecodeLookupRules : List Atom :=
  [variableTypecodeFoundRule, variableTypecodeMissingRule]

def variableTypecodeLookupDirectives : List SourceExecFact :=
  [variableTypecodeFoundDirective, variableTypecodeMissingDirective]

theorem variableTypecodeLookupRules_extract_exact :
    variableTypecodeLookupRules.filterMap extractSupportedSourceExecFact =
      variableTypecodeLookupDirectives := by rfl

/-! ## Symbolic firing and OSLF/NTT controls -/

private def fixtureOwner : Atom := .symbol "variable-typecode-source"
private def fixtureRequest : Atom := .symbol "floating-request"
private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "typecode.mm", start, stop }
private def fixtureLabel : LocatedName :=
  { span := fixtureSpan 10 12, name := "wx" }
private def fixtureTypecode : LocatedName :=
  { span := fixtureSpan 13 16, name := "wff" }
private def fixtureVariable : LocatedName :=
  { span := fixtureSpan 17 18, name := "x" }
private def fixtureCandidate : LocatedName :=
  { span := fixtureSpan 30 31, name := "x" }
private def fixtureOccurrence : VariableTypecodeOccurrence :=
  { statementPosition := 2
    label := fixtureLabel
    typecode := fixtureTypecode
    variableName := fixtureVariable }

private def fixtureGenericFound : Atom :=
  lookupFoundAtom (variableTypecodeLedgerOwner fixtureOwner) fixtureRequest
    fixtureCandidate (variableTypecodeObjectOccurrence fixtureOccurrence)
private def fixtureBinding : Atom :=
  variableTypecodeBindingAtom fixtureOwner fixtureOccurrence
private def foundRead : List Atom :=
  [variableTypecodeFoundRule, fixtureGenericFound, fixtureBinding]

private theorem foundRule_ne_genericFound :
    variableTypecodeFoundRule ≠ fixtureGenericFound := by
  simp [variableTypecodeFoundRule, mkRule, fixtureGenericFound,
    lookupFoundAtom]

private theorem foundRule_ne_binding :
    variableTypecodeFoundRule ≠ fixtureBinding := by
  simp [variableTypecodeFoundRule, mkRule, fixtureBinding,
    variableTypecodeBindingAtom]

private theorem genericFound_ne_binding :
    fixtureGenericFound ≠ fixtureBinding := by
  simp [fixtureGenericFound, lookupFoundAtom, fixtureBinding,
    variableTypecodeBindingAtom]

theorem foundAdapter_emits_instantiated
    {data : List Atom} {final : Subst} {result : Atom}
    (matched : final ∈
      (cmatchInputSpec []
        (variableTypecodeFoundDirective.atom ::
          data.erase variableTypecodeFoundDirective.atom)
        variableTypecodeFoundDirective.rule.input).map Prod.fst)
    (instantiated :
      instantiateTemplateAtom? final foundTemplate = some result) :
    result ∈ cFireReflectiveSourceExecFact data
      variableTypecodeFoundDirective := by
  apply mem_cFireReflectiveSourceExecFact_of_last_add data
    variableTypecodeFoundDirective
    [.add foundSelf, .remove genericFoundTemplate] foundTemplate
    result (by rfl) final matched instantiated

theorem canonicalBinding_matches_adapter_binding :
    (cmatchAtom [] bindingTemplate fixtureBinding).isSome = true := by
  rfl

private def foundOSLFAtoms : List Atom := foundRead
private def foundOSLFSource : Space := foundOSLFAtoms.toFinset
private theorem foundOSLFAtoms_nodup : foundOSLFAtoms.Nodup := by
  simp [foundOSLFAtoms, foundRead, foundRule_ne_genericFound,
    foundRule_ne_binding, genericFound_ne_binding]
private theorem foundOSLFAtoms_supported :
    cSupportedSourceExecFacts foundOSLFAtoms =
      [variableTypecodeFoundDirective] := by rfl
private theorem foundOSLF_selects :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace foundOSLFSource) =
      some variableTypecodeFoundDirective := by
  exact reflective_selects_of_computable_supported_singleton
    foundOSLFAtoms variableTypecodeFoundDirective foundOSLFAtoms_nodup
    foundOSLFAtoms_supported

theorem foundCanary_inhabits_target_native_type :
    let target := fireReflectiveSourceExecFact foundOSLFSource
      variableTypecodeFoundDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies foundOSLFSource
      (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected foundOSLF_selects)

private def fixtureGenericMissing : Atom :=
  lookupMissingAtom (variableTypecodeLedgerOwner fixtureOwner) fixtureRequest
    fixtureCandidate
theorem missingAdapter_emits_instantiated
    {data : List Atom} {final : Subst} {result : Atom}
    (matched : final ∈
      (cmatchInputSpec []
        (variableTypecodeMissingDirective.atom ::
          data.erase variableTypecodeMissingDirective.atom)
        variableTypecodeMissingDirective.rule.input).map Prod.fst)
    (instantiated :
      instantiateTemplateAtom? final missingTemplate = some result) :
    result ∈ cFireReflectiveSourceExecFact data
      variableTypecodeMissingDirective := by
  apply mem_cFireReflectiveSourceExecFact_of_last_add data
    variableTypecodeMissingDirective
    [.add missingSelf, .remove genericMissingTemplate] missingTemplate
    result (by rfl) final matched instantiated

theorem canonicalGenericMissing_matches_adapter_observation :
    (cmatchAtom [] genericMissingTemplate fixtureGenericMissing).isSome =
      true := by
  rfl

/-- A binding record for another variable cannot justify the generic hit for
the candidate, even when the assigned typecode is the same. -/
theorem different_historical_variable_has_distinct_binding_row :
    let other : VariableTypecodeOccurrence :=
      { fixtureOccurrence with
        variableName := { span := fixtureSpan 40 41, name := "y" } }
    fixtureBinding ≠ variableTypecodeBindingAtom fixtureOwner other := by
  dsimp only
  intro equal
  have occurrenceEqual :=
    variableTypecodeBindingAtom_injective fixtureOwner equal
  simp [fixtureOccurrence, fixtureVariable, fixtureSpan] at occurrenceEqual

section AxiomAudit

#print axioms semanticStep_inhabits_target_native_type
#print axioms decodeVariableTypecodeOccurrenceAtom_encoded
#print axioms variableTypecodeOccurrenceAtom_injective
#print axioms decodeVariableTypecodeBindingAtom_encoded
#print axioms variableTypecodeBindingAtom_injective
#print axioms decodeVariableTypecodeLedgerRows_encoded
#print axioms variableTypecodeBinding_mem_ledgerRows_has_occurrence
#print axioms variableTypecodeLookupRules_extract_exact
#print axioms foundAdapter_emits_instantiated
#print axioms canonicalBinding_matches_adapter_binding
#print axioms foundCanary_inhabits_target_native_type
#print axioms missingAdapter_emits_instantiated
#print axioms canonicalGenericMissing_matches_adapter_observation
#print axioms different_historical_variable_has_distinct_binding_row

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
