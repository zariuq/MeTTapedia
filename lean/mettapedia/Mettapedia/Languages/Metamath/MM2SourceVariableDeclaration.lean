import Mettapedia.Languages.Metamath.MM2SourceObjectLookup
import Mettapedia.Languages.Metamath.MM2SourceActionExecution

/-!
# Source-derived variable declaration in ordinary MM2

Variable declarations have two independent effects.  A first declaration
adds a permanent variable identity to the global object history, while every
accepted declaration adds a scope-local activation.  An inactive historical
variable may therefore be activated again without duplicating its permanent
identity.

The executable protocol validates the complete declaration before changing
either durable ledger.  Candidates are first recorded in a transaction-local
linked ledger.  Only after all global-namespace, active-variable, and
within-statement checks succeed does a commit cursor append the permanent and
active rows.  A rejected declaration cannot leave a partially applied source
state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Source-level transactional semantics -/

inductive VariableStageKind where
  | fresh
  | reactivate
deriving DecidableEq, Repr

structure VariableStageEntry where
  kind : VariableStageKind
  occurrence : LocatedName
deriving DecidableEq, Repr

def activeOccurrenceEntry (occurrence : LocatedName) : ObjectOccurrence :=
  { kind := .variable, occurrence }

def stageNames (staged : List VariableStageEntry) : List String :=
  staged.map (fun entry => entry.occurrence.name)

def commitInventory (inventory : List ObjectOccurrence)
    (staged : List VariableStageEntry) : List ObjectOccurrence :=
  staged.foldl (fun current entry =>
    match entry.kind with
    | .fresh => current ++ [activeOccurrenceEntry entry.occurrence]
    | .reactivate => current) inventory

def commitActive (active : List LocatedName)
    (staged : List VariableStageEntry) : List LocatedName :=
  active ++ staged.map VariableStageEntry.occurrence

inductive VariableControl where
  | checkingGlobal (candidate : LocatedName) (remaining : List LocatedName)
      (staged : List VariableStageEntry) (lookup : SemanticState)
  | checkingActive (candidate : LocatedName) (remaining : List LocatedName)
      (staged : List VariableStageEntry) (historical : ObjectOccurrence)
      (lookup : SemanticState)
  | finished
  | rejectedOccupied (candidate : LocatedName) (occupied : ObjectOccurrence)
  | rejectedActive (candidate : LocatedName) (active : ObjectOccurrence)
  | rejectedDuplicate (candidate : LocatedName)
deriving DecidableEq

structure VariableState where
  inventory : List ObjectOccurrence
  active : List LocatedName
  control : VariableControl
deriving DecidableEq

def activeSemanticEntries (active : List LocatedName) :
    List (Entry String ObjectOccurrence) :=
  active.map (semanticEntry <| activeOccurrenceEntry ·)

def initialVariableState (inventory : List ObjectOccurrence)
    (active : List LocatedName) (candidate : LocatedName)
    (remaining : List LocatedName) : VariableState :=
  { inventory
    active
    control := .checkingGlobal candidate remaining []
      (FiniteOccurrenceLookup.initial candidate.name
        (inventory.map semanticEntry)) }

inductive VariableStep : VariableState -> VariableState -> Prop where
  | scanGlobal {inventory : List ObjectOccurrence} {active : List LocatedName}
      {candidate : LocatedName} {remaining : List LocatedName}
      {staged : List VariableStageEntry} {before after : SemanticState}
      (step : FiniteOccurrenceLookup.Step before after)
      (scanning : exists cursor, after = .scanning cursor) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate remaining staged before }
        { inventory, active,
          control := .checkingGlobal candidate remaining staged after }
  | rejectOccupied {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {before : SemanticState} {position : Nat} {occupied : ObjectOccurrence}
      (found : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.found position occupied)))
      (differentKind : occupied.kind != .variable) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate remaining staged before }
        { inventory, active,
          control := .rejectedOccupied candidate occupied }
  | beginActiveLookup {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {before : SemanticState} {position : Nat} {historical : ObjectOccurrence}
      (found : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.found position historical)))
      (sameKind : historical.kind = .variable) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate remaining staged before }
        { inventory, active,
          control := .checkingActive candidate remaining staged historical
            (FiniteOccurrenceLookup.initial candidate.name
              (activeSemanticEntries active)) }
  | stageFreshMore {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate next : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {before : SemanticState} {endPosition : Nat}
      (missing : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.missing endPosition)))
      (freshInStatement : candidate.name ∉ stageNames staged) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate (next :: remaining) staged before }
        { inventory, active,
          control := .checkingGlobal next remaining
            (staged ++ [{ kind := .fresh, occurrence := candidate }])
            (FiniteOccurrenceLookup.initial next.name
              (inventory.map semanticEntry)) }
  | stageFreshLast {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {staged : List VariableStageEntry} {before : SemanticState}
      {endPosition : Nat}
      (missing : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.missing endPosition)))
      (freshInStatement : candidate.name ∉ stageNames staged) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate [] staged before }
        { inventory := commitInventory inventory
            (staged ++ [{ kind := .fresh, occurrence := candidate }])
          active := commitActive active
            (staged ++ [{ kind := .fresh, occurrence := candidate }])
          control := .finished }
  | rejectDuplicate {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {before : SemanticState} {endPosition : Nat}
      (missing : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.missing endPosition)))
      (duplicate : candidate.name ∈ stageNames staged) :
      VariableStep
        { inventory, active,
          control := .checkingGlobal candidate remaining staged before }
        { inventory, active, control := .rejectedDuplicate candidate }
  | scanActive {inventory : List ObjectOccurrence} {active : List LocatedName}
      {candidate : LocatedName} {remaining : List LocatedName}
      {staged : List VariableStageEntry} {historical : ObjectOccurrence}
      {before after : SemanticState}
      (step : FiniteOccurrenceLookup.Step before after)
      (scanning : exists cursor, after = .scanning cursor) :
      VariableStep
        { inventory, active,
          control := .checkingActive candidate remaining staged historical before }
        { inventory, active,
          control := .checkingActive candidate remaining staged historical after }
  | rejectActive {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {historical : ObjectOccurrence} {before : SemanticState}
      {position : Nat} {occupied : ObjectOccurrence}
      (found : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (activeSemanticEntries active)
          (.found position occupied))) :
      VariableStep
        { inventory, active,
          control := .checkingActive candidate remaining staged historical before }
        { inventory, active, control := .rejectedActive candidate occupied }
  | stageReactivationMore {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate next : LocatedName}
      {remaining : List LocatedName} {staged : List VariableStageEntry}
      {historical : ObjectOccurrence} {before : SemanticState}
      {endPosition : Nat}
      (missing : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (activeSemanticEntries active)
          (.missing endPosition))) :
      VariableStep
        { inventory, active,
          control := .checkingActive candidate (next :: remaining) staged
            historical before }
        { inventory, active,
          control := .checkingGlobal next remaining
            (staged ++ [{ kind := .reactivate, occurrence := candidate }])
            (FiniteOccurrenceLookup.initial next.name
              (inventory.map semanticEntry)) }
  | stageReactivationLast {inventory : List ObjectOccurrence}
      {active : List LocatedName} {candidate : LocatedName}
      {staged : List VariableStageEntry} {historical : ObjectOccurrence}
      {before : SemanticState} {endPosition : Nat}
      (missing : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (activeSemanticEntries active)
          (.missing endPosition))) :
      VariableStep
        { inventory, active,
          control := .checkingActive candidate [] staged historical before }
        { inventory := commitInventory inventory
            (staged ++ [{ kind := .reactivate, occurrence := candidate }])
          active := commitActive active
            (staged ++ [{ kind := .reactivate, occurrence := candidate }])
          control := .finished }

def variableGSLT : GSLT where
  Term := VariableState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := VariableStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def variableNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    variableGSLT

theorem variableStep_durable_state_is_atomic
    {before after : VariableState} (step : VariableStep before after) :
    (after.inventory = before.inventory ∧ after.active = before.active) ∨
      after.control = .finished := by
  cases step <;> simp [commitInventory, commitActive]

theorem variableStep_finished_activates_staged_order
    {before after : VariableState} (step : VariableStep before after)
    (finished : after.control = .finished) :
    ∃ staged : List VariableStageEntry,
      after.active = before.active ++ staged.map VariableStageEntry.occurrence := by
  cases step <;> simp_all [commitActive]
  · rename_i inventory active candidate staged before endPosition missing fresh
    exact ⟨staged ++ [{ kind := .fresh, occurrence := candidate }], by simp⟩
  · rename_i inventory active candidate staged historical before endPosition missing
    exact ⟨staged ++ [{ kind := .reactivate, occurrence := candidate }], by simp⟩

@[simp] theorem commitActive_names (active : List LocatedName)
    (staged : List VariableStageEntry) :
    (commitActive active staged).map LocatedName.name =
      active.map LocatedName.name ++ stageNames staged := by
  simp [commitActive, stageNames, List.map_append]

/-! ## Active and transaction ledger identities -/

def activeVariableLedgerOwner (owner : Atom) : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", owner]

def variableTransactionOwner (owner position : Atom) : Atom :=
  .expression [.symbol "mm-source-variable-transaction", owner, position]

def activeVariableRows (owner : Atom) (active : List LocatedName) : List Atom :=
  objectInventoryRows (activeVariableLedgerOwner owner)
    (active.map activeOccurrenceEntry)

@[simp] theorem activeVariableRows_decode (owner : Atom)
    (active : List LocatedName) :
    decodeObjectInventoryRows (activeVariableLedgerOwner owner)
        (activeVariableRows owner active) =
      some (active.map activeOccurrenceEntry) := by
  simp [activeVariableRows]

theorem activeVariableLedgerOwner_injective :
    Function.Injective activeVariableLedgerOwner := by
  intro left right equal
  simpa [activeVariableLedgerOwner] using equal

def variableStageMarkerAtom (owner position : Atom)
    (entry : VariableStageEntry) : Atom :=
  .expression
    [.symbol "mm-source-variable-stage-kind",
      variableTransactionOwner owner position,
      (match entry.kind with
       | .fresh => .symbol "mm-source-variable-stage-fresh"
       | .reactivate => .symbol "mm-source-variable-stage-reactivate"),
      locatedNameAtom entry.occurrence]

/-! ## Ordinary MM2 validation and commit protocol -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def variableStartLocation := location "02" "mm-source-variable-start"
private def variableEmptyLocation := location "02" "mm-source-variable-empty"
private def variableConstantOccupiedLocation :=
  location "03" "mm-source-variable-constant-occupied"
private def variableLabelOccupiedLocation :=
  location "03" "mm-source-variable-label-occupied"
private def variableHistoricalLocation := location "03" "mm-source-variable-historical"
private def variableGlobalMissingLocation := location "03" "mm-source-variable-global-missing"
private def variableActiveFoundLocation := location "04" "mm-source-variable-active-found"
private def variableActiveMissingMoreLocation :=
  location "04" "mm-source-variable-reactivate-more"
private def variableActiveMissingLastLocation :=
  location "04" "mm-source-variable-reactivate-last"
private def variableStageFoundLocation := location "05" "mm-source-variable-stage-found"
private def variableStageMissingMoreLocation :=
  location "05" "mm-source-variable-fresh-more"
private def variableStageMissingLastLocation :=
  location "05" "mm-source-variable-fresh-last"
private def variableCommitFreshLocation := location "06" "mm-source-variable-commit-fresh"
private def variableCommitReactivationLocation :=
  location "06" "mm-source-variable-commit-reactivation"
private def variableCommitFinishLocation := location "07" "mm-source-variable-commit-finish"
private def variableAbortLocation := location "06" "mm-source-variable-abort"
private def variableAbortFinishLocation :=
  location "07" "mm-source-variable-abort-finish"

private def candidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "candidate-span", .var "candidate-name"]

private def nonemptyNamesTemplate : Atom :=
  .expression [.symbol "mm-cons", candidateTemplate, .var "remaining-names"]

private def variableStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-var", .var "declaration-site", nonemptyNamesTemplate,
      .var "declaration-terminator"]

private def emptyVariableStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-var", .var "declaration-site",
      .expression [.symbol "mm-nil"], .var "declaration-terminator"]

private def variableCurrentTemplate (statement : Atom) : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", statement, .var "dispatch-input",
      .var "dispatch-output"]

private def sourceObjectFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source",
      .var "object-frontier"]

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-variable-ledger", .var "source"]

private def activeFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", activeOwnerTemplate,
      .var "active-frontier"]

private def transactionOwnerTemplate : Atom :=
  .expression
    [.symbol "mm-source-variable-transaction", .var "source", .var "position"]

private def transactionFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", transactionOwnerTemplate,
      .var "transaction-frontier"]

private def transactionRootFrontierTemplate : Atom :=
  objectFrontierAtom transactionOwnerTemplate objectRootKey

private def variableAbortControlTemplate (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-variable-abort", .var "source", .var "position",
      cursor, frontier]

private def variableRequestTemplate (statement pendingNames : Atom) : Atom :=
  .expression
    [.symbol "mm-source-variable-request", .var "source", .var "position",
      .var "next-position", statement, .var "dispatch-input",
      .var "dispatch-output", pendingNames]

private def carriedStatementTemplate : Atom := .var "variable-statement"

private def initialRequestTemplate : Atom :=
  variableRequestTemplate variableStatementTemplate (.var "remaining-names")

private def continuingRequestTemplate (pending : Atom) : Atom :=
  variableRequestTemplate carriedStatementTemplate pending

private def lookupTemplate (lookupOwner request candidate cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", lookupOwner, request, candidate,
      cursor, frontier]

private def initialGlobalLookupTemplate : Atom :=
  lookupTemplate (.var "source") initialRequestTemplate candidateTemplate
    objectRootKey (.var "object-frontier")

private def reloadTriggerTemplate (lookupOwner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", lookupOwner]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"), .var (stem ++ "-output")]

private def sinkSyntaxAtom : Sink -> Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

private def mkRule (loc : Atom) (patterns : List Atom) (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkSyntaxAtom)]

private def rejectedTemplate (statement reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source", .var "position",
      statement, reason, evidence]

private def variableStartSelf := selfTemplate variableStartLocation "variable-start"
private def variableStartPatterns : List Atom :=
  [variableStartSelf, variableCurrentTemplate variableStatementTemplate,
   sourceObjectFrontierTemplate, activeFrontierTemplate]
private def variableStartSinks : List Sink :=
  [.add variableStartSelf,
   .remove (variableCurrentTemplate variableStatementTemplate),
   .add transactionRootFrontierTemplate, .add initialGlobalLookupTemplate,
   .add (reloadTriggerTemplate (.var "source"))]

def variableStartRule : Atom :=
  mkRule variableStartLocation variableStartPatterns variableStartSinks

def variableStartDirective : SourceExecFact where
  atom := variableStartRule
  loc := variableStartLocation
  rule :=
    { priority := 2
      name := "mm-source-variable-start"
      input := .compat (mkPattern variableStartPatterns)
      guards := []
      tmpl := mkTemplate variableStartSinks }

theorem extract_variableStartRule_exact :
    extractSupportedSourceExecFact variableStartRule =
      some variableStartDirective := by
  rfl

private def variableEmptySelf := selfTemplate variableEmptyLocation "variable-empty"
private def variableEmptyPatterns : List Atom :=
  [variableEmptySelf, variableCurrentTemplate emptyVariableStatementTemplate]
private def variableEmptyRejected : Atom :=
  rejectedTemplate emptyVariableStatementTemplate
    (.symbol "empty-variable-declaration") (.var "declaration-site")
private def variableEmptySinks : List Sink :=
  [.add variableEmptySelf,
   .remove (variableCurrentTemplate emptyVariableStatementTemplate),
   .add variableEmptyRejected]

def variableEmptyRule : Atom :=
  mkRule variableEmptyLocation variableEmptyPatterns variableEmptySinks

def variableEmptyDirective : SourceExecFact where
  atom := variableEmptyRule
  loc := variableEmptyLocation
  rule :=
    { priority := 2
      name := "mm-source-variable-empty"
      input := .compat (mkPattern variableEmptyPatterns)
      guards := []
      tmpl := mkTemplate variableEmptySinks }

theorem extract_variableEmptyRule_exact :
    extractSupportedSourceExecFact variableEmptyRule =
      some variableEmptyDirective := by
  rfl

private def foundTemplate (lookupOwner request kind : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-found", lookupOwner, request, candidateTemplate,
      .expression
        [.symbol "mm-source-object-entry", kind,
          .expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "candidate-name"]]]

private def globalFoundTemplate (kind : Atom) : Atom :=
  foundTemplate (.var "source")
    (continuingRequestTemplate (.var "pending-names")) kind

private def occupiedEntryTemplate (kind : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-entry", kind,
      .expression
        [.symbol "mm-source-name", .var "occupied-span",
          .var "candidate-name"]]

private def occupiedRuleFor (loc : Atom) (stem kind reason : String) :
    Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let found := globalFoundTemplate (.symbol kind)
  let rejected := rejectedTemplate carriedStatementTemplate (.symbol reason)
    (occupiedEntryTemplate (.symbol kind))
  let patterns := [self, found, transactionFrontierTemplate]
  let sinks : List Sink := [.add self, .remove found, .add rejected,
    .add (variableAbortControlTemplate objectRootKey
      (.var "transaction-frontier"))]
  let atom := mkRule loc patterns sinks
  (atom,
    { atom
      loc
      rule :=
        { priority := 3
          name := stem
          input := .compat (mkPattern patterns)
          guards := []
          tmpl := mkTemplate sinks } })

def variableConstantOccupiedRule : Atom :=
  (occupiedRuleFor variableConstantOccupiedLocation
    "mm-source-variable-constant-occupied" "mm-source-object-constant"
      "occupied-object-name").1

def variableConstantOccupiedDirective : SourceExecFact :=
  (occupiedRuleFor variableConstantOccupiedLocation
    "mm-source-variable-constant-occupied" "mm-source-object-constant"
      "occupied-object-name").2

def variableLabelOccupiedRule : Atom :=
  (occupiedRuleFor variableLabelOccupiedLocation
    "mm-source-variable-label-occupied" "mm-source-object-label"
      "occupied-object-name").1

def variableLabelOccupiedDirective : SourceExecFact :=
  (occupiedRuleFor variableLabelOccupiedLocation
    "mm-source-variable-label-occupied" "mm-source-object-label"
      "occupied-object-name").2

theorem extract_variableConstantOccupiedRule_exact :
    extractSupportedSourceExecFact variableConstantOccupiedRule =
      some variableConstantOccupiedDirective := by rfl

theorem extract_variableLabelOccupiedRule_exact :
    extractSupportedSourceExecFact variableLabelOccupiedRule =
      some variableLabelOccupiedDirective := by rfl

private def historicalFoundTemplate : Atom :=
  globalFoundTemplate (.symbol "mm-source-object-variable")

private def activeLookupTemplate : Atom :=
  lookupTemplate activeOwnerTemplate
    (continuingRequestTemplate (.var "pending-names")) candidateTemplate
    objectRootKey (.var "active-frontier")

private def variableHistoricalSelf :=
  selfTemplate variableHistoricalLocation "variable-historical"
private def variableHistoricalPatterns : List Atom :=
  [variableHistoricalSelf, historicalFoundTemplate, activeFrontierTemplate]
private def variableHistoricalSinks : List Sink :=
  [.add variableHistoricalSelf, .remove historicalFoundTemplate,
   .add activeLookupTemplate, .add (reloadTriggerTemplate activeOwnerTemplate)]

def variableHistoricalRule : Atom :=
  mkRule variableHistoricalLocation variableHistoricalPatterns
    variableHistoricalSinks

def variableHistoricalDirective : SourceExecFact where
  atom := variableHistoricalRule
  loc := variableHistoricalLocation
  rule :=
    { priority := 3
      name := "mm-source-variable-historical"
      input := .compat (mkPattern variableHistoricalPatterns)
      guards := []
      tmpl := mkTemplate variableHistoricalSinks }

theorem extract_variableHistoricalRule_exact :
    extractSupportedSourceExecFact variableHistoricalRule =
      some variableHistoricalDirective := by rfl

private def globalMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-missing", .var "source",
      continuingRequestTemplate (.var "pending-names"), candidateTemplate]

private def transactionLookupTemplate : Atom :=
  lookupTemplate transactionOwnerTemplate
    (continuingRequestTemplate (.var "pending-names")) candidateTemplate
    objectRootKey (.var "transaction-frontier")

private def variableGlobalMissingSelf :=
  selfTemplate variableGlobalMissingLocation "variable-global-missing"
private def variableGlobalMissingPatterns : List Atom :=
  [variableGlobalMissingSelf, globalMissingTemplate,
   transactionFrontierTemplate]
private def variableGlobalMissingSinks : List Sink :=
  [.add variableGlobalMissingSelf, .remove globalMissingTemplate,
   .add transactionLookupTemplate,
   .add (reloadTriggerTemplate transactionOwnerTemplate)]

def variableGlobalMissingRule : Atom :=
  mkRule variableGlobalMissingLocation variableGlobalMissingPatterns
    variableGlobalMissingSinks

def variableGlobalMissingDirective : SourceExecFact where
  atom := variableGlobalMissingRule
  loc := variableGlobalMissingLocation
  rule :=
    { priority := 3
      name := "mm-source-variable-global-missing"
      input := .compat (mkPattern variableGlobalMissingPatterns)
      guards := []
      tmpl := mkTemplate variableGlobalMissingSinks }

theorem extract_variableGlobalMissingRule_exact :
    extractSupportedSourceExecFact variableGlobalMissingRule =
      some variableGlobalMissingDirective := by rfl

private def activeFoundTemplate : Atom :=
  foundTemplate activeOwnerTemplate
    (continuingRequestTemplate (.var "pending-names"))
    (.symbol "mm-source-object-variable")

private def variableActiveFoundSelf :=
  selfTemplate variableActiveFoundLocation "variable-active-found"
private def variableActiveFoundRejected :=
  rejectedTemplate carriedStatementTemplate (.symbol "active-variable-name")
    (occupiedEntryTemplate (.symbol "mm-source-object-variable"))
private def variableActiveFoundPatterns : List Atom :=
  [variableActiveFoundSelf, activeFoundTemplate, transactionFrontierTemplate]
private def variableActiveFoundSinks : List Sink :=
  [.add variableActiveFoundSelf, .remove activeFoundTemplate,
   .add variableActiveFoundRejected,
   .add (variableAbortControlTemplate objectRootKey
     (.var "transaction-frontier"))]

def variableActiveFoundRule : Atom :=
  mkRule variableActiveFoundLocation variableActiveFoundPatterns
    variableActiveFoundSinks

def variableActiveFoundDirective : SourceExecFact where
  atom := variableActiveFoundRule
  loc := variableActiveFoundLocation
  rule :=
    { priority := 4
      name := "mm-source-variable-active-found"
      input := .compat (mkPattern variableActiveFoundPatterns)
      guards := []
      tmpl := mkTemplate variableActiveFoundSinks }

theorem extract_variableActiveFoundRule_exact :
    extractSupportedSourceExecFact variableActiveFoundRule =
      some variableActiveFoundDirective := by rfl

private def activeMissingTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-missing", activeOwnerTemplate,
      continuingRequestTemplate (.var "pending-names"), candidateTemplate]

private def stageFoundTemplate : Atom :=
  foundTemplate transactionOwnerTemplate
    (continuingRequestTemplate (.var "pending-names"))
    (.symbol "mm-source-object-variable")

private def variableStageFoundSelf :=
  selfTemplate variableStageFoundLocation "variable-stage-found"
private def variableStageFoundRejected :=
  rejectedTemplate carriedStatementTemplate
    (.symbol "duplicate-variable-name") candidateTemplate
private def variableStageFoundPatterns : List Atom :=
  [variableStageFoundSelf, stageFoundTemplate, transactionFrontierTemplate]
private def variableStageFoundSinks : List Sink :=
  [.add variableStageFoundSelf, .remove stageFoundTemplate,
   .add variableStageFoundRejected,
   .add (variableAbortControlTemplate objectRootKey
     (.var "transaction-frontier"))]

def variableStageFoundRule : Atom :=
  mkRule variableStageFoundLocation variableStageFoundPatterns
    variableStageFoundSinks

def variableStageFoundDirective : SourceExecFact where
  atom := variableStageFoundRule
  loc := variableStageFoundLocation
  rule :=
    { priority := 5
      name := "mm-source-variable-stage-found"
      input := .compat (mkPattern variableStageFoundPatterns)
      guards := []
      tmpl := mkTemplate variableStageFoundSinks }

theorem extract_variableStageFoundRule_exact :
    extractSupportedSourceExecFact variableStageFoundRule =
      some variableStageFoundDirective := by rfl

private def moreNamesTemplate : Atom :=
  .expression
    [.symbol "mm-cons",
      .expression
        [.symbol "mm-source-name", .var "next-candidate-span",
          .var "next-candidate-name"],
      .var "after-next-names"]

private def noNamesTemplate : Atom := .expression [.symbol "mm-nil"]

private def nextCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "next-candidate-span",
      .var "next-candidate-name"]

private def nextRequestTemplate : Atom :=
  continuingRequestTemplate (.var "after-next-names")

private def nextGlobalLookupTemplate : Atom :=
  lookupTemplate (.var "source") nextRequestTemplate nextCandidateTemplate
    objectRootKey (.var "object-frontier")

private def stagedEntryTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-entry", .symbol "mm-source-object-variable",
      candidateTemplate]

private def stagedLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", transactionOwnerTemplate,
      .var "transaction-frontier", candidateTemplate, stagedEntryTemplate]

private def stagedFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", transactionOwnerTemplate,
      candidateTemplate]

private def stageMarkerTemplate (kind : String) : Atom :=
  .expression
    [.symbol "mm-source-variable-stage-kind", transactionOwnerTemplate,
      .symbol kind, candidateTemplate]

private def stageAndContinueSinks (missing : Atom) (kind : String) : List Sink :=
  [.remove missing, .remove transactionFrontierTemplate,
   .add stagedLinkTemplate, .add stagedFrontierTemplate,
   .add (stageMarkerTemplate kind), .add nextGlobalLookupTemplate,
   .add (reloadTriggerTemplate (.var "source"))]

private def commitControlTemplate (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-variable-commit", .var "source", .var "position",
      .var "next-position", carriedStatementTemplate,
      .var "dispatch-input", .var "dispatch-output", cursor, frontier]

private def stageAndCommitSinks (missing : Atom) (kind : String) : List Sink :=
  [.remove missing, .remove transactionFrontierTemplate,
   .add stagedLinkTemplate, .add stagedFrontierTemplate,
   .add (stageMarkerTemplate kind),
   .add (commitControlTemplate objectRootKey candidateTemplate),
   .add (reloadTriggerTemplate (.var "source"))]

/-! The remaining rules split on the pending-name list in the request.  The
fully explicit definitions keep the executable patterns auditable. -/

private def requestWithPending (pending : Atom) : Atom :=
  continuingRequestTemplate pending

private def missingWithPending (lookupOwner pending : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", lookupOwner,
      requestWithPending pending, candidateTemplate]

private def activeMissingMore : Atom :=
  missingWithPending activeOwnerTemplate moreNamesTemplate
private def activeMissingLast : Atom :=
  missingWithPending activeOwnerTemplate noNamesTemplate
private def stageMissingMore : Atom :=
  missingWithPending transactionOwnerTemplate moreNamesTemplate
private def stageMissingLast : Atom :=
  missingWithPending transactionOwnerTemplate noNamesTemplate

private def explicitStageRule (priority : Nat) (loc : Atom)
    (stem kind : String) (missing : Atom) (last : Bool) :
    Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let patterns := [self, missing, transactionFrontierTemplate,
    sourceObjectFrontierTemplate]
  let staged := if last then stageAndCommitSinks missing kind
    else stageAndContinueSinks missing kind
  let sinks := [.add self] ++ staged
  let atom := mkRule loc patterns sinks
  (atom,
    { atom
      loc
      rule :=
        { priority
          name := stem
          input := .compat (mkPattern patterns)
          guards := []
          tmpl := mkTemplate sinks } })

def variableActiveMissingMoreRule : Atom :=
  (explicitStageRule 4 variableActiveMissingMoreLocation
    "mm-source-variable-reactivate-more" "mm-source-variable-stage-reactivate"
    activeMissingMore false).1
def variableActiveMissingMoreDirective : SourceExecFact :=
  (explicitStageRule 4 variableActiveMissingMoreLocation
    "mm-source-variable-reactivate-more" "mm-source-variable-stage-reactivate"
    activeMissingMore false).2
def variableActiveMissingLastRule : Atom :=
  (explicitStageRule 4 variableActiveMissingLastLocation
    "mm-source-variable-reactivate-last" "mm-source-variable-stage-reactivate"
    activeMissingLast true).1
def variableActiveMissingLastDirective : SourceExecFact :=
  (explicitStageRule 4 variableActiveMissingLastLocation
    "mm-source-variable-reactivate-last" "mm-source-variable-stage-reactivate"
    activeMissingLast true).2
def variableStageMissingMoreRule : Atom :=
  (explicitStageRule 5 variableStageMissingMoreLocation
    "mm-source-variable-fresh-more" "mm-source-variable-stage-fresh"
    stageMissingMore false).1
def variableStageMissingMoreDirective : SourceExecFact :=
  (explicitStageRule 5 variableStageMissingMoreLocation
    "mm-source-variable-fresh-more" "mm-source-variable-stage-fresh"
    stageMissingMore false).2
def variableStageMissingLastRule : Atom :=
  (explicitStageRule 5 variableStageMissingLastLocation
    "mm-source-variable-fresh-last" "mm-source-variable-stage-fresh"
    stageMissingLast true).1
def variableStageMissingLastDirective : SourceExecFact :=
  (explicitStageRule 5 variableStageMissingLastLocation
    "mm-source-variable-fresh-last" "mm-source-variable-stage-fresh"
    stageMissingLast true).2

theorem extract_variableActiveMissingMoreRule_exact :
    extractSupportedSourceExecFact variableActiveMissingMoreRule =
      some variableActiveMissingMoreDirective := by rfl
theorem extract_variableActiveMissingLastRule_exact :
    extractSupportedSourceExecFact variableActiveMissingLastRule =
      some variableActiveMissingLastDirective := by rfl
theorem extract_variableStageMissingMoreRule_exact :
    extractSupportedSourceExecFact variableStageMissingMoreRule =
      some variableStageMissingMoreDirective := by rfl
theorem extract_variableStageMissingLastRule_exact :
    extractSupportedSourceExecFact variableStageMissingLastRule =
      some variableStageMissingLastDirective := by rfl

private def stageLinkAtCursorTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", transactionOwnerTemplate,
      .var "transaction-cursor", .var "transaction-next", stagedEntryTemplate]

private def currentCommitTemplate : Atom :=
  commitControlTemplate (.var "transaction-cursor")
    (.var "transaction-frontier")

private def nextCommitTemplate : Atom :=
  commitControlTemplate (.var "transaction-next")
    (.var "transaction-frontier")

private def globalAppendedLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "object-frontier",
      candidateTemplate, stagedEntryTemplate]

private def globalAppendedFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source", candidateTemplate]

private def activeAppendedLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", activeOwnerTemplate,
      .var "active-frontier", candidateTemplate, stagedEntryTemplate]

private def activeAppendedFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", activeOwnerTemplate,
      candidateTemplate]

private def commitRuleFor (loc : Atom) (stem stageKind : String)
    (fresh : Bool) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let marker := stageMarkerTemplate stageKind
  let patterns := [self, currentCommitTemplate, stageLinkAtCursorTemplate,
    marker, activeFrontierTemplate] ++
      (if fresh then [sourceObjectFrontierTemplate] else [])
  let durableSinks : List Sink :=
    [.remove activeFrontierTemplate, .add activeAppendedLinkTemplate,
     .add activeAppendedFrontierTemplate] ++
      (if fresh then
        [.remove sourceObjectFrontierTemplate, .add globalAppendedLinkTemplate,
         .add globalAppendedFrontierTemplate]
       else [])
  let sinks : List Sink :=
    [.add self, .remove currentCommitTemplate,
     .remove stageLinkAtCursorTemplate, .remove marker] ++ durableSinks ++
      [.add nextCommitTemplate]
  let atom := mkRule loc patterns sinks
  (atom,
    { atom
      loc
      rule :=
        { priority := 6
          name := stem
          input := .compat (mkPattern patterns)
          guards := []
          tmpl := mkTemplate sinks } })

def variableCommitFreshRule : Atom :=
  (commitRuleFor variableCommitFreshLocation "mm-source-variable-commit-fresh"
    "mm-source-variable-stage-fresh" true).1
def variableCommitFreshDirective : SourceExecFact :=
  (commitRuleFor variableCommitFreshLocation "mm-source-variable-commit-fresh"
    "mm-source-variable-stage-fresh" true).2
def variableCommitReactivationRule : Atom :=
  (commitRuleFor variableCommitReactivationLocation
    "mm-source-variable-commit-reactivation"
    "mm-source-variable-stage-reactivate" false).1
def variableCommitReactivationDirective : SourceExecFact :=
  (commitRuleFor variableCommitReactivationLocation
    "mm-source-variable-commit-reactivation"
    "mm-source-variable-stage-reactivate" false).2

theorem extract_variableCommitFreshRule_exact :
    extractSupportedSourceExecFact variableCommitFreshRule =
      some variableCommitFreshDirective := by rfl
theorem extract_variableCommitReactivationRule_exact :
    extractSupportedSourceExecFact variableCommitReactivationRule =
      some variableCommitReactivationDirective := by rfl

private def sourceReloadCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-reload",
      .var "source-verifier-reload-rule"]

def variableSourceReloadCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-variable-reload", sourceVerifierReloadRule]

private def commitFinishedTemplate : Atom :=
  commitControlTemplate (.var "transaction-frontier")
    (.var "transaction-frontier")

private def sourceNextControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def statementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source", .var "position",
      carriedStatementTemplate]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def variableCommitFinishSelf :=
  selfTemplate variableCommitFinishLocation "variable-commit-finish"
private def variableCommitFinishPatterns : List Atom :=
  [variableCommitFinishSelf, commitFinishedTemplate,
   transactionFrontierTemplate, sourceReloadCaptureTemplate]
private def variableCommitFinishSinks : List Sink :=
  [.add variableCommitFinishSelf, .remove commitFinishedTemplate,
   .remove transactionFrontierTemplate, .add sourceNextControlTemplate,
   .add statementAppliedTemplate, .add sourceReloadTemplate,
   .add (.var "source-verifier-reload-rule")]

def variableCommitFinishRule : Atom :=
  mkRule variableCommitFinishLocation variableCommitFinishPatterns
    variableCommitFinishSinks

def variableCommitFinishDirective : SourceExecFact where
  atom := variableCommitFinishRule
  loc := variableCommitFinishLocation
  rule :=
    { priority := 7
      name := "mm-source-variable-commit-finish"
      input := .compat (mkPattern variableCommitFinishPatterns)
      guards := []
      tmpl := mkTemplate variableCommitFinishSinks }

theorem extract_variableCommitFinishRule_exact :
    extractSupportedSourceExecFact variableCommitFinishRule =
      some variableCommitFinishDirective := by rfl

private def currentAbortTemplate : Atom :=
  variableAbortControlTemplate (.var "transaction-cursor")
    (.var "transaction-frontier")

private def nextAbortTemplate : Atom :=
  variableAbortControlTemplate (.var "transaction-next")
    (.var "transaction-frontier")

private def abortStageMarkerTemplate : Atom :=
  .expression
    [.symbol "mm-source-variable-stage-kind", transactionOwnerTemplate,
      .var "stage-kind", candidateTemplate]

private def variableAbortSelf :=
  selfTemplate variableAbortLocation "variable-abort"

private def variableAbortPatterns : List Atom :=
  [variableAbortSelf, currentAbortTemplate, stageLinkAtCursorTemplate,
   abortStageMarkerTemplate]

private def variableAbortSinks : List Sink :=
  [.add variableAbortSelf, .remove currentAbortTemplate,
   .remove stageLinkAtCursorTemplate, .remove abortStageMarkerTemplate,
   .add nextAbortTemplate]

def variableAbortRule : Atom :=
  mkRule variableAbortLocation variableAbortPatterns variableAbortSinks

def variableAbortDirective : SourceExecFact where
  atom := variableAbortRule
  loc := variableAbortLocation
  rule :=
    { priority := 6
      name := "mm-source-variable-abort"
      input := .compat (mkPattern variableAbortPatterns)
      guards := []
      tmpl := mkTemplate variableAbortSinks }

theorem extract_variableAbortRule_exact :
    extractSupportedSourceExecFact variableAbortRule =
      some variableAbortDirective := by rfl

private def abortFinishedTemplate : Atom :=
  variableAbortControlTemplate (.var "transaction-frontier")
    (.var "transaction-frontier")

private def variableAbortFinishSelf :=
  selfTemplate variableAbortFinishLocation "variable-abort-finish"

private def variableAbortFinishPatterns : List Atom :=
  [variableAbortFinishSelf, abortFinishedTemplate,
   transactionFrontierTemplate]

private def variableAbortFinishSinks : List Sink :=
  [.add variableAbortFinishSelf, .remove abortFinishedTemplate,
   .remove transactionFrontierTemplate]

def variableAbortFinishRule : Atom :=
  mkRule variableAbortFinishLocation variableAbortFinishPatterns
    variableAbortFinishSinks

def variableAbortFinishDirective : SourceExecFact where
  atom := variableAbortFinishRule
  loc := variableAbortFinishLocation
  rule :=
    { priority := 7
      name := "mm-source-variable-abort-finish"
      input := .compat (mkPattern variableAbortFinishPatterns)
      guards := []
      tmpl := mkTemplate variableAbortFinishSinks }

theorem extract_variableAbortFinishRule_exact :
    extractSupportedSourceExecFact variableAbortFinishRule =
      some variableAbortFinishDirective := by rfl

def variableDeclarationOwnRules : List Atom :=
  [variableStartRule, variableEmptyRule, variableConstantOccupiedRule,
   variableLabelOccupiedRule, variableHistoricalRule,
   variableGlobalMissingRule, variableActiveFoundRule,
   variableActiveMissingMoreRule, variableActiveMissingLastRule,
   variableStageFoundRule, variableStageMissingMoreRule,
   variableStageMissingLastRule, variableCommitFreshRule,
   variableCommitReactivationRule, variableCommitFinishRule,
   variableAbortRule, variableAbortFinishRule]

def variableDeclarationOwnDirectives : List SourceExecFact :=
  [variableStartDirective, variableEmptyDirective,
   variableConstantOccupiedDirective, variableLabelOccupiedDirective,
   variableHistoricalDirective, variableGlobalMissingDirective,
   variableActiveFoundDirective, variableActiveMissingMoreDirective,
   variableActiveMissingLastDirective, variableStageFoundDirective,
   variableStageMissingMoreDirective, variableStageMissingLastDirective,
   variableCommitFreshDirective, variableCommitReactivationDirective,
   variableCommitFinishDirective, variableAbortDirective,
   variableAbortFinishDirective]

def variableDeclarationRules : List Atom :=
  variableDeclarationOwnRules ++ lookupRules

def variableDeclarationDirectives : List SourceExecFact :=
  variableDeclarationOwnDirectives ++ lookupDirectives

def variableLookupContinuationRules : List Atom :=
  [variableConstantOccupiedRule, variableLabelOccupiedRule,
   variableHistoricalRule, variableGlobalMissingRule,
   variableActiveFoundRule, variableActiveMissingMoreRule,
   variableActiveMissingLastRule, variableStageFoundRule,
   variableStageMissingMoreRule, variableStageMissingLastRule]
    ++ [variableCommitFreshRule, variableCommitReactivationRule,
      variableCommitFinishRule, variableAbortRule, variableAbortFinishRule]

def variableLookupStaticRows : List Atom :=
  variableLookupContinuationRules.map objectLookupRuleRow

def variableDeclarationStaticRows : List Atom :=
  variableLookupStaticRows ++ [variableSourceReloadCaptureRow]

theorem variableDeclarationRules_extract_exact :
    variableDeclarationRules.filterMap extractSupportedSourceExecFact =
      variableDeclarationDirectives := by rfl

theorem variableLookupStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ variableLookupStaticRows) :
    isProofNeutralInitialAtom row = false := by
  rw [variableLookupStaticRows, List.mem_map] at member
  obtain ⟨rule, _, rfl⟩ := member
  exact objectLookupRuleRow_not_proofNeutral rule

@[simp] theorem variableSourceReloadCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom variableSourceReloadCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-variable-reload" [sourceVerifierReloadRule]
      (by decide)

/-! ## Bounded positive and negative controls -/

private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "variable.mm", start, stop }

private def fixtureName : LocatedName :=
  { span := fixtureSpan 3 4, name := "x" }

private def fixtureStatement : RawStatement :=
  .varDecl (fixtureSpan 0 2) [fixtureName] (fixtureSpan 5 7)

private def fixtureOwner : Atom := .symbol "variable-source"

private def startCanaryAtoms : List Atom :=
  [variableStartRule, sourceCurrentAtom fixtureOwner 0 1 fixtureStatement,
   objectFrontierAtom fixtureOwner objectRootKey,
   objectFrontierAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey]

private def startCanarySpace : Space := startCanaryAtoms.toFinset

private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel

private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms = [variableStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace startCanarySpace) =
      some variableStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms variableStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          variableStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

private def activePrior : ObjectOccurrence :=
  { kind := .variable,
    occurrence := { span := fixtureSpan 10 11, name := "x" } }

private def activeFoundRequest : Atom :=
  .expression
    [.symbol "mm-source-variable-request", fixtureOwner, natAtom 0, natAtom 1,
      rawStatementAtom fixtureStatement, .symbol "dispatch-input",
      .symbol "dispatch-output", listAtom locatedNameAtom []]

private def activeFoundCanaryAtoms : List Atom :=
  [variableActiveFoundRule,
   lookupFoundAtom (activeVariableLedgerOwner fixtureOwner) activeFoundRequest
     fixtureName activePrior,
   objectFrontierAtom (variableTransactionOwner fixtureOwner (natAtom 0))
     objectRootKey]

private def activeFoundCanarySpace : Space := activeFoundCanaryAtoms.toFinset

private theorem activeFoundCanaryAtoms_nodup :
    activeFoundCanaryAtoms.Nodup := by decide +kernel

private theorem activeFoundCanaryAtoms_supported :
    cSupportedSourceExecFacts activeFoundCanaryAtoms =
      [variableActiveFoundDirective] := by rfl

theorem activeFoundCanary_selects_rejection :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace activeFoundCanarySpace) =
      some variableActiveFoundDirective := by
  exact reflective_selects_of_computable_supported_singleton
    activeFoundCanaryAtoms variableActiveFoundDirective
    activeFoundCanaryAtoms_nodup activeFoundCanaryAtoms_supported

private theorem activeFoundCanary_fire_agreement :
    (cFireReflectiveSourceExecFact activeFoundCanaryAtoms
        variableActiveFoundDirective).toFinset =
      fireReflectiveSourceExecFact activeFoundCanarySpace
        variableActiveFoundDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    activeFoundCanaryAtoms variableActiveFoundDirective
    activeFoundCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      variableActiveFoundDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      activeFoundCanaryAtoms variableActiveFoundDirective
      activeFoundCanaryAtoms_nodup)

def activeRedeclarationRejectedAtom : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 0,
      rawStatementAtom fixtureStatement, .symbol "active-variable-name",
      objectOccurrenceAtom activePrior]

theorem activeFoundCanary_emits_exact_rejection :
    activeRedeclarationRejectedAtom ∈
      fireReflectiveSourceExecFact activeFoundCanarySpace
        variableActiveFoundDirective := by
  rw [← activeFoundCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def commitCanaryControl : Atom :=
  .expression
    [.symbol "mm-source-variable-commit", fixtureOwner, natAtom 0, natAtom 1,
      rawStatementAtom fixtureStatement, .symbol "dispatch-input",
      .symbol "dispatch-output", objectRootKey, locatedNameAtom fixtureName]

private def commitCanaryEntry : ObjectOccurrence :=
  activeOccurrenceEntry fixtureName

private def commitCanaryTransactionLink : Atom :=
  objectLinkAtom (variableTransactionOwner fixtureOwner (natAtom 0))
    objectRootKey (locatedNameAtom fixtureName) commitCanaryEntry

private def commitCanaryMarker (kind : VariableStageKind) : Atom :=
  variableStageMarkerAtom fixtureOwner (natAtom 0) { kind, occurrence := fixtureName }

private def commitFreshCanaryAtoms : List Atom :=
  [variableCommitFreshRule, commitCanaryControl, commitCanaryTransactionLink,
   commitCanaryMarker .fresh,
   objectFrontierAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey,
   objectFrontierAtom fixtureOwner objectRootKey]

private def commitFreshCanarySpace : Space := commitFreshCanaryAtoms.toFinset

private theorem commitFreshCanaryAtoms_nodup :
    commitFreshCanaryAtoms.Nodup := by decide +kernel

private theorem commitFreshCanaryAtoms_supported :
    cSupportedSourceExecFacts commitFreshCanaryAtoms =
      [variableCommitFreshDirective] := by rfl

theorem commitFreshCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace commitFreshCanarySpace) =
      some variableCommitFreshDirective := by
  exact reflective_selects_of_computable_supported_singleton
    commitFreshCanaryAtoms variableCommitFreshDirective
    commitFreshCanaryAtoms_nodup commitFreshCanaryAtoms_supported

private theorem commitFreshCanary_fire_agreement :
    (cFireReflectiveSourceExecFact commitFreshCanaryAtoms
        variableCommitFreshDirective).toFinset =
      fireReflectiveSourceExecFact commitFreshCanarySpace
        variableCommitFreshDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    commitFreshCanaryAtoms variableCommitFreshDirective
    commitFreshCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      variableCommitFreshDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      commitFreshCanaryAtoms variableCommitFreshDirective
      commitFreshCanaryAtoms_nodup)

theorem commitFreshCanary_appends_permanent_occurrence :
    objectLinkAtom fixtureOwner objectRootKey (locatedNameAtom fixtureName)
        commitCanaryEntry ∈
      fireReflectiveSourceExecFact commitFreshCanarySpace
        variableCommitFreshDirective := by
  rw [← commitFreshCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem commitFreshCanary_appends_active_occurrence :
    objectLinkAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey
        (locatedNameAtom fixtureName) commitCanaryEntry ∈
      fireReflectiveSourceExecFact commitFreshCanarySpace
        variableCommitFreshDirective := by
  rw [← commitFreshCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def commitReactivationCanaryAtoms : List Atom :=
  [variableCommitReactivationRule, commitCanaryControl,
   commitCanaryTransactionLink, commitCanaryMarker .reactivate,
   objectFrontierAtom (activeVariableLedgerOwner fixtureOwner) objectRootKey]

private def commitReactivationCanarySpace : Space :=
  commitReactivationCanaryAtoms.toFinset

private theorem commitReactivationCanaryAtoms_nodup :
    commitReactivationCanaryAtoms.Nodup := by decide +kernel

private theorem commitReactivationCanaryAtoms_supported :
    cSupportedSourceExecFacts commitReactivationCanaryAtoms =
      [variableCommitReactivationDirective] := by rfl

private theorem commitReactivationCanary_fire_agreement :
    (cFireReflectiveSourceExecFact commitReactivationCanaryAtoms
        variableCommitReactivationDirective).toFinset =
      fireReflectiveSourceExecFact commitReactivationCanarySpace
        variableCommitReactivationDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    commitReactivationCanaryAtoms variableCommitReactivationDirective
    commitReactivationCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      variableCommitReactivationDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      commitReactivationCanaryAtoms variableCommitReactivationDirective
      commitReactivationCanaryAtoms_nodup)

theorem commitReactivationCanary_does_not_mint_permanent_occurrence :
    objectLinkAtom fixtureOwner objectRootKey (locatedNameAtom fixtureName)
        commitCanaryEntry ∉
      fireReflectiveSourceExecFact commitReactivationCanarySpace
        variableCommitReactivationDirective := by
  rw [← commitReactivationCanary_fire_agreement]
  simpa using (show objectLinkAtom fixtureOwner objectRootKey
    (locatedNameAtom fixtureName) commitCanaryEntry ∉
      (cFireReflectiveSourceExecFact commitReactivationCanaryAtoms
        variableCommitReactivationDirective).toFinset by decide +kernel)

#print axioms variableStep_durable_state_is_atomic
#print axioms variableStep_finished_activates_staged_order
#print axioms commitActive_names
#print axioms activeVariableRows_decode
#print axioms variableDeclarationRules_extract_exact
#print axioms startCanary_inhabits_target_native_type
#print axioms activeFoundCanary_selects_rejection
#print axioms activeFoundCanary_emits_exact_rejection
#print axioms commitFreshCanary_appends_permanent_occurrence
#print axioms commitFreshCanary_appends_active_occurrence
#print axioms commitReactivationCanary_does_not_mint_permanent_occurrence

end Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
