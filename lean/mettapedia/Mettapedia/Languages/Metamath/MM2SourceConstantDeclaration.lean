import Mettapedia.Languages.Metamath.MM2SourceObjectLookup

/-!
# Source-derived constant declaration in ordinary MM2

This module realizes the first complete non-proof Metamath source operation
inside the target verifier.  A `$c` event is admitted only at top level and
only when its nonempty occurrence list is fresh in the global object ledger.
The complete occurrence list is validated into a transaction-local ledger
before any permanent object row changes.  A separate commit cursor then
appends each source occurrence in order.  No precomputed source-state delta is
consumed, and rejection cannot leave a partially applied declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration

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

/-! ## Proof-relevant semantic machine -/

def constantStageEntries (staged : List LocatedName) :
    List (Entry String ObjectOccurrence) :=
  staged.map (semanticEntry <| { kind := .constant, occurrence := · })

def commitConstants (inventory : List ObjectOccurrence)
    (staged : List LocatedName) : List ObjectOccurrence :=
  inventory ++ staged.map (fun occurrence =>
    { kind := .constant, occurrence := occurrence })

inductive ConstantControl where
  | checkingGlobal (candidate : LocatedName) (remaining : List LocatedName)
      (staged : List LocatedName) (lookup : SemanticState)
  | checkingStage (candidate : LocatedName) (remaining : List LocatedName)
      (staged : List LocatedName) (lookup : SemanticState)
  | finished
  | rejected (candidate : LocatedName) (occupied : ObjectOccurrence)
  | rejectedDuplicate (candidate : LocatedName)
deriving DecidableEq

structure ConstantState where
  inventory : List ObjectOccurrence
  control : ConstantControl
deriving DecidableEq

def initialConstantState (inventory : List ObjectOccurrence)
    (candidate : LocatedName) (remaining : List LocatedName) : ConstantState :=
  { inventory
    control := .checkingGlobal candidate remaining []
      (FiniteOccurrenceLookup.initial candidate.name
        (inventory.map semanticEntry)) }

inductive ConstantStep : ConstantState -> ConstantState -> Prop where
  | scanGlobal {inventory : List ObjectOccurrence} {candidate : LocatedName}
      {remaining staged : List LocatedName} {before after : SemanticState}
      (step : FiniteOccurrenceLookup.Step before after)
      (stillScanning : exists scan, after = .scanning scan) :
      ConstantStep
        { inventory,
          control := .checkingGlobal candidate remaining staged before }
        { inventory,
          control := .checkingGlobal candidate remaining staged after }
  | occupied {inventory : List ObjectOccurrence} {candidate : LocatedName}
      {remaining staged : List LocatedName} {before : SemanticState}
      {position : Nat} {entry : ObjectOccurrence}
      (step : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.found position entry))) :
      ConstantStep
        { inventory,
          control := .checkingGlobal candidate remaining staged before }
        { inventory, control := .rejected candidate entry }
  | beginStageLookup {inventory : List ObjectOccurrence}
      {candidate : LocatedName} {remaining staged : List LocatedName}
      {before : SemanticState} {endPosition : Nat}
      (step : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (inventory.map semanticEntry)
          (.missing endPosition))) :
      ConstantStep
        { inventory,
          control := .checkingGlobal candidate remaining staged before }
        { inventory,
          control := .checkingStage candidate remaining staged
            (FiniteOccurrenceLookup.initial candidate.name
              (constantStageEntries staged)) }
  | scanStage {inventory : List ObjectOccurrence} {candidate : LocatedName}
      {remaining staged : List LocatedName} {before after : SemanticState}
      (step : FiniteOccurrenceLookup.Step before after)
      (stillScanning : exists scan, after = .scanning scan) :
      ConstantStep
        { inventory,
          control := .checkingStage candidate remaining staged before }
        { inventory,
          control := .checkingStage candidate remaining staged after }
  | duplicate {inventory : List ObjectOccurrence}
      {candidate : LocatedName} {remaining staged : List LocatedName}
      {before : SemanticState} {position : Nat} {entry : ObjectOccurrence}
      (step : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (constantStageEntries staged)
          (.found position entry))) :
      ConstantStep
        { inventory,
          control := .checkingStage candidate remaining staged before }
        { inventory, control := .rejectedDuplicate candidate }
  | stageMore {inventory : List ObjectOccurrence}
      {candidate next : LocatedName} {remaining : List LocatedName}
      {staged : List LocatedName} {before : SemanticState} {endPosition : Nat}
      (step : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (constantStageEntries staged)
          (.missing endPosition))) :
      ConstantStep
        { inventory,
          control := .checkingStage candidate (next :: remaining) staged before }
        { inventory,
          control := .checkingGlobal next remaining (staged ++ [candidate])
            (FiniteOccurrenceLookup.initial next.name
              (inventory.map semanticEntry)) }
  | stageLast {inventory : List ObjectOccurrence}
      {candidate : LocatedName} {staged : List LocatedName}
      {before : SemanticState} {endPosition : Nat}
      (step : FiniteOccurrenceLookup.Step before
        (.finished candidate.name (constantStageEntries staged)
          (.missing endPosition))) :
      ConstantStep
        { inventory,
          control := .checkingStage candidate [] staged before }
        { inventory := commitConstants inventory (staged ++ [candidate])
          control := .finished }

def constantGSLT : GSLT where
  Term := ConstantState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ConstantStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The declaration machine receives its native modal theory only through
OSLF, independently of the MM2 encoding below. -/
def constantNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    constantGSLT

theorem constantStep_durable_state_is_atomic
    {before after : ConstantState} (step : ConstantStep before after) :
    after.inventory = before.inventory ∨ after.control = .finished := by
  cases step <;> simp [commitConstants]

theorem constantStep_never_appends_nonconstant
    {before after : ConstantState} (step : ConstantStep before after)
    (entry : ObjectOccurrence)
    (newEntry : entry ∈ after.inventory ∧ entry ∉ before.inventory) :
    entry.kind = .constant := by
  cases step <;> simp_all [commitConstants]
  rename_i inventory candidate staged before endPosition missing
  rcases newEntry.1 with old | added
  · exact False.elim (newEntry.2 old)
  · rcases added with stagedEntry | lastEntry
    · obtain ⟨occurrence, _, rfl⟩ := stagedEntry
      rfl
    · rw [lastEntry]

theorem constantStep_finished_commits_staged_order
    {before after : ConstantState} (step : ConstantStep before after)
    (finished : after.control = .finished) :
    ∃ staged : List LocatedName,
      after.inventory = commitConstants before.inventory staged := by
  cases step <;> simp_all [commitConstants]
  rename_i inventory candidate staged before endPosition missing
  exact ⟨staged ++ [candidate], by simp⟩

/-! ## Target representation -/

private def constantStartLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-constant-start"]

private def constantNestedLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-source-constant-not-top-level"]

private def constantEmptyLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-constant-empty"]

private def constantOccupiedLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-constant-occupied"]

private def constantGlobalMissingLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-constant-global-missing"]

private def constantStageFoundLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-constant-stage-found"]

private def constantStageMissingMoreLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-constant-stage-more"]

private def constantStageMissingLastLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-constant-stage-last"]

private def constantCommitLocation : Atom :=
  .expression [.symbol "05", .symbol "mm-source-constant-commit"]

private def constantCommitFinishLocation : Atom :=
  .expression [.symbol "06", .symbol "mm-source-constant-commit-finish"]

private def constantAbortLocation : Atom :=
  .expression [.symbol "05", .symbol "mm-source-constant-abort"]

private def constantAbortFinishLocation : Atom :=
  .expression [.symbol "06", .symbol "mm-source-constant-abort-finish"]

private def candidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "candidate-span",
      .var "candidate-name"]

private def nextCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "next-candidate-span",
      .var "next-candidate-name"]

private def nonemptyNamesTemplate : Atom :=
  .expression [.symbol "mm-cons", candidateTemplate, .var "remaining-names"]

private def constantStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-const", .var "declaration-site",
      nonemptyNamesTemplate, .var "declaration-terminator"]

private def emptyConstantStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-const", .var "declaration-site",
      .expression [.symbol "mm-nil"], .var "declaration-terminator"]

private def constantCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", constantStatementTemplate,
      .var "dispatch-input", .var "dispatch-output"]

private def emptyConstantCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", emptyConstantStatementTemplate,
      .var "dispatch-input", .var "dispatch-output"]

private def topLevelEnvironmentTemplate : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "source",
      .expression [.symbol "mm-nil"], .var "next-hypothesis",
      .var "next-assertion"]

private def constantRequestTemplate (statement pendingNames : Atom) : Atom :=
  .expression
    [.symbol "mm-source-constant-request", .var "source", .var "position",
      .var "next-position", statement,
      .var "dispatch-input", .var "dispatch-output", pendingNames]

private def initialConstantRequestTemplate : Atom :=
  constantRequestTemplate constantStatementTemplate (.var "remaining-names")

private def carriedConstantStatementTemplate : Atom :=
  .var "constant-statement"

private def continuingConstantRequestTemplate (pendingNames : Atom) : Atom :=
  constantRequestTemplate carriedConstantStatementTemplate pendingNames

def constantTransactionOwner (owner position : Atom) : Atom :=
  .expression [.symbol "mm-source-constant-transaction", owner, position]

private def transactionOwnerTemplate : Atom :=
  constantTransactionOwner (.var "source") (.var "position")

private def lookupTemplate (owner request candidate cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-lookup", owner, request, candidate, cursor,
      frontier]

private def lookupInitialTemplate (request candidate frontier : Atom) : Atom :=
  lookupTemplate (.var "source") request candidate objectRootKey frontier

private def constantLookupInitialTemplate : Atom :=
  lookupInitialTemplate initialConstantRequestTemplate candidateTemplate
    (.var "object-frontier")

private def sourceObjectFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source",
      .var "object-frontier"]

private def transactionFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", transactionOwnerTemplate,
      .var "transaction-frontier"]

private def transactionRootFrontierTemplate : Atom :=
  objectFrontierAtom transactionOwnerTemplate objectRootKey

private def reloadTriggerTemplate (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-object-lookup", owner]

private def constantAbortControlTemplate (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-constant-abort", .var "source", .var "position",
      cursor, frontier]

private def constantStartSelfTemplate : Atom :=
  .expression
    [.symbol "exec", constantStartLocation,
      .var "constant-start-input", .var "constant-start-output"]

private def constantStartPatternAtoms : List Atom :=
  [constantStartSelfTemplate, constantCurrentTemplate,
   topLevelEnvironmentTemplate, sourceObjectFrontierTemplate]

private def constantStartSinks : List Sink :=
  [.add constantStartSelfTemplate, .remove constantCurrentTemplate,
   .add transactionRootFrontierTemplate, .add constantLookupInitialTemplate,
   .add (reloadTriggerTemplate (.var "source"))]

def constantStartRule : Atom :=
  .expression
    [.symbol "exec", constantStartLocation,
      .expression (.symbol "," :: constantStartPatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "+", constantStartSelfTemplate],
          .expression [.symbol "-", constantCurrentTemplate],
          .expression [.symbol "+", transactionRootFrontierTemplate],
          .expression [.symbol "+", constantLookupInitialTemplate],
          .expression [.symbol "+", reloadTriggerTemplate (.var "source")]]]

def constantStartDirective : SourceExecFact where
  atom := constantStartRule
  loc := constantStartLocation
  rule :=
    { priority := 2
      name := "mm-source-constant-start"
      input := .compat (mkPattern constantStartPatternAtoms)
      guards := []
      tmpl := mkTemplate constantStartSinks }

theorem extract_constantStartRule_exact :
    extractSupportedSourceExecFact constantStartRule =
      some constantStartDirective := by
  rfl

private def rejectedTemplate (statement reason evidence : Atom) : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", .var "source",
      .var "position", statement, reason, evidence]

private def nestedConstantStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-const", .var "declaration-site",
      .var "declared-names", .var "declaration-terminator"]

private def nestedConstantCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-source-current", .var "source", .var "position",
      .var "next-position", nestedConstantStatementTemplate,
      .var "dispatch-input", .var "dispatch-output"]

private def nonemptyEnvironmentTemplate : Atom :=
  .expression
    [.symbol "mm-source-environment", .var "source",
      .expression
        [.symbol "mm-cons", .var "scope-checkpoint", .var "scope-rest"],
      .var "next-hypothesis", .var "next-assertion"]

private def constantNestedSelfTemplate : Atom :=
  .expression
    [.symbol "exec", constantNestedLocation,
      .var "constant-nested-input", .var "constant-nested-output"]

private def constantNestedRejectedTemplate : Atom :=
  rejectedTemplate nestedConstantStatementTemplate
    (.symbol "constant-not-top-level") (.var "declaration-site")

private def constantNestedPatternAtoms : List Atom :=
  [constantNestedSelfTemplate, nestedConstantCurrentTemplate,
   nonemptyEnvironmentTemplate]

private def constantNestedSinks : List Sink :=
  [.add constantNestedSelfTemplate, .remove nestedConstantCurrentTemplate,
   .add constantNestedRejectedTemplate]

def constantNestedRule : Atom :=
  .expression
    [.symbol "exec", constantNestedLocation,
      .expression (.symbol "," :: constantNestedPatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "+", constantNestedSelfTemplate],
          .expression [.symbol "-", nestedConstantCurrentTemplate],
          .expression [.symbol "+", constantNestedRejectedTemplate]]]

def constantNestedDirective : SourceExecFact where
  atom := constantNestedRule
  loc := constantNestedLocation
  rule :=
    { priority := 1
      name := "mm-source-constant-not-top-level"
      input := .compat (mkPattern constantNestedPatternAtoms)
      guards := []
      tmpl := mkTemplate constantNestedSinks }

theorem extract_constantNestedRule_exact :
    extractSupportedSourceExecFact constantNestedRule =
      some constantNestedDirective := by
  rfl

private def constantEmptySelfTemplate : Atom :=
  .expression
    [.symbol "exec", constantEmptyLocation,
      .var "constant-empty-input", .var "constant-empty-output"]

private def constantEmptyRejectedTemplate : Atom :=
  rejectedTemplate emptyConstantStatementTemplate
    (.symbol "empty-constant-declaration") (.var "declaration-site")

private def constantEmptyPatternAtoms : List Atom :=
  [constantEmptySelfTemplate, emptyConstantCurrentTemplate,
   topLevelEnvironmentTemplate]

private def constantEmptySinks : List Sink :=
  [.add constantEmptySelfTemplate, .remove emptyConstantCurrentTemplate,
   .add constantEmptyRejectedTemplate]

def constantEmptyRule : Atom :=
  .expression
    [.symbol "exec", constantEmptyLocation,
      .expression (.symbol "," :: constantEmptyPatternAtoms),
      .expression
        [.symbol "O", .expression [.symbol "+", constantEmptySelfTemplate],
          .expression [.symbol "-", emptyConstantCurrentTemplate],
          .expression [.symbol "+", constantEmptyRejectedTemplate]]]

def constantEmptyDirective : SourceExecFact where
  atom := constantEmptyRule
  loc := constantEmptyLocation
  rule :=
    { priority := 2
      name := "mm-source-constant-empty"
      input := .compat (mkPattern constantEmptyPatternAtoms)
      guards := []
      tmpl := mkTemplate constantEmptySinks }

theorem extract_constantEmptyRule_exact :
    extractSupportedSourceExecFact constantEmptyRule =
      some constantEmptyDirective := by
  rfl

private def occupiedEntryTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-entry", .var "occupied-kind",
      .expression
        [.symbol "mm-source-name", .var "occupied-span",
          .var "candidate-name"]]

private def constantFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-found", .var "source",
      continuingConstantRequestTemplate (.var "pending-names"),
      candidateTemplate,
      occupiedEntryTemplate]

private def constantOccupiedSelfTemplate : Atom :=
  .expression
    [.symbol "exec", constantOccupiedLocation,
      .var "constant-occupied-input", .var "constant-occupied-output"]

private def constantOccupiedRejectedTemplate : Atom :=
  rejectedTemplate carriedConstantStatementTemplate
    (.symbol "occupied-object-name") occupiedEntryTemplate

private def constantOccupiedPatternAtoms : List Atom :=
  [constantOccupiedSelfTemplate, constantFoundTemplate,
   transactionFrontierTemplate]

private def constantOccupiedSinks : List Sink :=
  [.add constantOccupiedSelfTemplate, .remove constantFoundTemplate,
   .add constantOccupiedRejectedTemplate,
   .add (constantAbortControlTemplate objectRootKey
     (.var "transaction-frontier"))]

def constantOccupiedRule : Atom :=
  .expression
    [.symbol "exec", constantOccupiedLocation,
      .expression (.symbol "," :: constantOccupiedPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "+", constantOccupiedSelfTemplate],
          .expression [.symbol "-", constantFoundTemplate],
          .expression [.symbol "+", constantOccupiedRejectedTemplate],
          .expression
            [.symbol "+", constantAbortControlTemplate objectRootKey
              (.var "transaction-frontier")]]]

def constantOccupiedDirective : SourceExecFact where
  atom := constantOccupiedRule
  loc := constantOccupiedLocation
  rule :=
    { priority := 3
      name := "mm-source-constant-occupied"
      input := .compat (mkPattern constantOccupiedPatternAtoms)
      guards := []
      tmpl := mkTemplate constantOccupiedSinks }

theorem extract_constantOccupiedRule_exact :
    extractSupportedSourceExecFact constantOccupiedRule =
      some constantOccupiedDirective := by
  rfl

private def constantMissingTemplate (pendingNames : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", .var "source",
      continuingConstantRequestTemplate pendingNames, candidateTemplate]

private def sinkSyntaxAtom : Sink -> Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom => .expression [.symbol "head", natAtom count, atom]
  | .tail count atom => .expression [.symbol "tail", natAtom count, atom]

private def mkRule (loc : Atom) (patterns : List Atom)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkSyntaxAtom)]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def stagedEntryTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-entry",
      .symbol "mm-source-object-constant", candidateTemplate]

private def transactionLookupTemplate : Atom :=
  lookupTemplate transactionOwnerTemplate
    (continuingConstantRequestTemplate (.var "pending-names"))
    candidateTemplate objectRootKey (.var "transaction-frontier")

private def constantGlobalMissingSelfTemplate : Atom :=
  selfTemplate constantGlobalMissingLocation "constant-global-missing"

private def constantGlobalMissingPatternAtoms : List Atom :=
  [constantGlobalMissingSelfTemplate,
   constantMissingTemplate (.var "pending-names"),
   transactionFrontierTemplate]

private def constantGlobalMissingSinks : List Sink :=
  [.add constantGlobalMissingSelfTemplate,
   .remove (constantMissingTemplate (.var "pending-names")),
   .add transactionLookupTemplate,
   .add (reloadTriggerTemplate transactionOwnerTemplate)]

def constantGlobalMissingRule : Atom :=
  mkRule constantGlobalMissingLocation constantGlobalMissingPatternAtoms
    constantGlobalMissingSinks

def constantGlobalMissingDirective : SourceExecFact where
  atom := constantGlobalMissingRule
  loc := constantGlobalMissingLocation
  rule :=
    { priority := 3
      name := "mm-source-constant-global-missing"
      input := .compat (mkPattern constantGlobalMissingPatternAtoms)
      guards := []
      tmpl := mkTemplate constantGlobalMissingSinks }

theorem extract_constantGlobalMissingRule_exact :
    extractSupportedSourceExecFact constantGlobalMissingRule =
      some constantGlobalMissingDirective := by rfl

private def transactionFoundTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-found", transactionOwnerTemplate,
      continuingConstantRequestTemplate (.var "pending-names"),
      candidateTemplate,
      .expression
        [.symbol "mm-source-object-entry",
          .symbol "mm-source-object-constant",
          .expression
            [.symbol "mm-source-name", .var "occupied-span",
              .var "candidate-name"]]]

private def constantStageFoundSelfTemplate : Atom :=
  selfTemplate constantStageFoundLocation "constant-stage-found"

private def constantStageFoundRejectedTemplate : Atom :=
  rejectedTemplate carriedConstantStatementTemplate
    (.symbol "duplicate-constant-name") candidateTemplate

private def constantStageFoundPatternAtoms : List Atom :=
  [constantStageFoundSelfTemplate, transactionFoundTemplate,
   transactionFrontierTemplate]

private def constantStageFoundSinks : List Sink :=
  [.add constantStageFoundSelfTemplate, .remove transactionFoundTemplate,
   .add constantStageFoundRejectedTemplate,
   .add (constantAbortControlTemplate objectRootKey
     (.var "transaction-frontier"))]

def constantStageFoundRule : Atom :=
  mkRule constantStageFoundLocation constantStageFoundPatternAtoms
    constantStageFoundSinks

def constantStageFoundDirective : SourceExecFact where
  atom := constantStageFoundRule
  loc := constantStageFoundLocation
  rule :=
    { priority := 4
      name := "mm-source-constant-stage-found"
      input := .compat (mkPattern constantStageFoundPatternAtoms)
      guards := []
      tmpl := mkTemplate constantStageFoundSinks }

theorem extract_constantStageFoundRule_exact :
    extractSupportedSourceExecFact constantStageFoundRule =
      some constantStageFoundDirective := by rfl

private def transactionMissingTemplate (pendingNames : Atom) : Atom :=
  .expression
    [.symbol "mm-source-object-missing", transactionOwnerTemplate,
      continuingConstantRequestTemplate pendingNames, candidateTemplate]

private def stagedLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", transactionOwnerTemplate,
      .var "transaction-frontier", candidateTemplate, stagedEntryTemplate]

private def stagedFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", transactionOwnerTemplate,
      candidateTemplate]

private def moreNamesTemplate : Atom :=
  .expression
    [.symbol "mm-cons", nextCandidateTemplate,
      .var "after-next-names"]

private def noNamesTemplate : Atom := .expression [.symbol "mm-nil"]

private def nextRequestTemplate : Atom :=
  continuingConstantRequestTemplate (.var "after-next-names")

private def nextLookupTemplate : Atom :=
  lookupInitialTemplate nextRequestTemplate nextCandidateTemplate
    (.var "object-frontier")

private def constantCommitControlTemplate (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-constant-commit", .var "source", .var "position",
      .var "next-position", carriedConstantStatementTemplate,
      .var "dispatch-input", .var "dispatch-output", cursor, frontier]

private def stageSinks (missing : Atom) (last : Bool) : List Sink :=
  [.remove missing, .remove transactionFrontierTemplate,
   .add stagedLinkTemplate, .add stagedFrontierTemplate] ++
    (if last then
      [.add (constantCommitControlTemplate objectRootKey candidateTemplate),
       .add (reloadTriggerTemplate (.var "source"))]
     else
      [.add nextLookupTemplate,
       .add (reloadTriggerTemplate (.var "source"))])

private def stageRule (loc : Atom) (stem : String) (pending : Atom)
    (last : Bool) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let missing := transactionMissingTemplate pending
  let patterns := [self, missing, transactionFrontierTemplate,
    sourceObjectFrontierTemplate]
  let sinks := [.add self] ++ stageSinks missing last
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

def constantStageMissingMoreRule : Atom :=
  (stageRule constantStageMissingMoreLocation "mm-source-constant-stage-more"
    moreNamesTemplate false).1

def constantStageMissingMoreDirective : SourceExecFact :=
  (stageRule constantStageMissingMoreLocation "mm-source-constant-stage-more"
    moreNamesTemplate false).2

def constantStageMissingLastRule : Atom :=
  (stageRule constantStageMissingLastLocation "mm-source-constant-stage-last"
    noNamesTemplate true).1

def constantStageMissingLastDirective : SourceExecFact :=
  (stageRule constantStageMissingLastLocation "mm-source-constant-stage-last"
    noNamesTemplate true).2

theorem extract_constantStageMissingMoreRule_exact :
    extractSupportedSourceExecFact constantStageMissingMoreRule =
      some constantStageMissingMoreDirective := by rfl

theorem extract_constantStageMissingLastRule_exact :
    extractSupportedSourceExecFact constantStageMissingLastRule =
      some constantStageMissingLastDirective := by rfl

private def transactionLinkAtCursorTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", transactionOwnerTemplate,
      .var "transaction-cursor", .var "transaction-next",
      stagedEntryTemplate]

private def currentCommitTemplate : Atom :=
  constantCommitControlTemplate (.var "transaction-cursor")
    (.var "transaction-frontier")

private def nextCommitTemplate : Atom :=
  constantCommitControlTemplate (.var "transaction-next")
    (.var "transaction-frontier")

private def committedLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-link", .var "source", .var "object-frontier",
      candidateTemplate, stagedEntryTemplate]

private def committedFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-object-frontier", .var "source", candidateTemplate]

private def constantCommitSelfTemplate : Atom :=
  selfTemplate constantCommitLocation "constant-commit"

private def constantCommitPatternAtoms : List Atom :=
  [constantCommitSelfTemplate, currentCommitTemplate,
   transactionLinkAtCursorTemplate, sourceObjectFrontierTemplate]

private def constantCommitSinks : List Sink :=
  [.add constantCommitSelfTemplate, .remove currentCommitTemplate,
   .remove transactionLinkAtCursorTemplate,
   .remove sourceObjectFrontierTemplate, .add committedLinkTemplate,
   .add committedFrontierTemplate, .add nextCommitTemplate]

def constantCommitRule : Atom :=
  mkRule constantCommitLocation constantCommitPatternAtoms constantCommitSinks

def constantCommitDirective : SourceExecFact where
  atom := constantCommitRule
  loc := constantCommitLocation
  rule :=
    { priority := 5
      name := "mm-source-constant-commit"
      input := .compat (mkPattern constantCommitPatternAtoms)
      guards := []
      tmpl := mkTemplate constantCommitSinks }

theorem extract_constantCommitRule_exact :
    extractSupportedSourceExecFact constantCommitRule =
      some constantCommitDirective := by rfl

private def nextSourceControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-control", .var "source", .var "next-position"]

private def sourceStatementAppliedTemplate : Atom :=
  .expression
    [.symbol "mm-source-statement-applied", .var "source",
      .var "position", carriedConstantStatementTemplate]

private def sourceReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-verifier", .var "source"]

private def sourceReloadRuleCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-constant-reload",
      .var "source-verifier-reload-rule"]

def sourceReloadRuleCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-source-constant-reload",
      sourceVerifierReloadRule]

private def commitFinishedTemplate : Atom :=
  constantCommitControlTemplate (.var "transaction-frontier")
    (.var "transaction-frontier")

private def constantCommitFinishSelfTemplate : Atom :=
  selfTemplate constantCommitFinishLocation "constant-commit-finish"

private def constantCommitFinishPatternAtoms : List Atom :=
  [constantCommitFinishSelfTemplate, commitFinishedTemplate,
   transactionFrontierTemplate, sourceReloadRuleCaptureTemplate]

private def constantCommitFinishSinks : List Sink :=
  [.add constantCommitFinishSelfTemplate, .remove commitFinishedTemplate,
   .remove transactionFrontierTemplate, .add nextSourceControlTemplate,
   .add sourceStatementAppliedTemplate, .add sourceReloadTemplate,
   .add (.var "source-verifier-reload-rule")]

def constantCommitFinishRule : Atom :=
  mkRule constantCommitFinishLocation constantCommitFinishPatternAtoms
    constantCommitFinishSinks

def constantCommitFinishDirective : SourceExecFact where
  atom := constantCommitFinishRule
  loc := constantCommitFinishLocation
  rule :=
    { priority := 6
      name := "mm-source-constant-commit-finish"
      input := .compat (mkPattern constantCommitFinishPatternAtoms)
      guards := []
      tmpl := mkTemplate constantCommitFinishSinks }

theorem extract_constantCommitFinishRule_exact :
    extractSupportedSourceExecFact constantCommitFinishRule =
      some constantCommitFinishDirective := by rfl

private def currentAbortTemplate : Atom :=
  constantAbortControlTemplate (.var "transaction-cursor")
    (.var "transaction-frontier")

private def nextAbortTemplate : Atom :=
  constantAbortControlTemplate (.var "transaction-next")
    (.var "transaction-frontier")

private def constantAbortSelfTemplate : Atom :=
  selfTemplate constantAbortLocation "constant-abort"

private def constantAbortPatternAtoms : List Atom :=
  [constantAbortSelfTemplate, currentAbortTemplate,
   transactionLinkAtCursorTemplate]

private def constantAbortSinks : List Sink :=
  [.add constantAbortSelfTemplate, .remove currentAbortTemplate,
   .remove transactionLinkAtCursorTemplate, .add nextAbortTemplate]

def constantAbortRule : Atom :=
  mkRule constantAbortLocation constantAbortPatternAtoms constantAbortSinks

def constantAbortDirective : SourceExecFact where
  atom := constantAbortRule
  loc := constantAbortLocation
  rule :=
    { priority := 5
      name := "mm-source-constant-abort"
      input := .compat (mkPattern constantAbortPatternAtoms)
      guards := []
      tmpl := mkTemplate constantAbortSinks }

theorem extract_constantAbortRule_exact :
    extractSupportedSourceExecFact constantAbortRule =
      some constantAbortDirective := by rfl

private def abortFinishedTemplate : Atom :=
  constantAbortControlTemplate (.var "transaction-frontier")
    (.var "transaction-frontier")

private def constantAbortFinishSelfTemplate : Atom :=
  selfTemplate constantAbortFinishLocation "constant-abort-finish"

private def constantAbortFinishPatternAtoms : List Atom :=
  [constantAbortFinishSelfTemplate, abortFinishedTemplate,
   transactionFrontierTemplate]

private def constantAbortFinishSinks : List Sink :=
  [.add constantAbortFinishSelfTemplate, .remove abortFinishedTemplate,
   .remove transactionFrontierTemplate]

def constantAbortFinishRule : Atom :=
  mkRule constantAbortFinishLocation constantAbortFinishPatternAtoms
    constantAbortFinishSinks

def constantAbortFinishDirective : SourceExecFact where
  atom := constantAbortFinishRule
  loc := constantAbortFinishLocation
  rule :=
    { priority := 6
      name := "mm-source-constant-abort-finish"
      input := .compat (mkPattern constantAbortFinishPatternAtoms)
      guards := []
      tmpl := mkTemplate constantAbortFinishSinks }

theorem extract_constantAbortFinishRule_exact :
    extractSupportedSourceExecFact constantAbortFinishRule =
      some constantAbortFinishDirective := by rfl

def constantDeclarationOwnRules : List Atom :=
  [constantNestedRule, constantStartRule, constantEmptyRule, constantOccupiedRule,
   constantGlobalMissingRule, constantStageFoundRule,
   constantStageMissingMoreRule, constantStageMissingLastRule,
   constantCommitRule, constantCommitFinishRule,
   constantAbortRule, constantAbortFinishRule]

def constantDeclarationOwnDirectives : List SourceExecFact :=
  [constantNestedDirective, constantStartDirective, constantEmptyDirective,
   constantOccupiedDirective, constantGlobalMissingDirective,
   constantStageFoundDirective, constantStageMissingMoreDirective,
   constantStageMissingLastDirective, constantCommitDirective,
   constantCommitFinishDirective, constantAbortDirective,
   constantAbortFinishDirective]

def constantDeclarationRules : List Atom :=
  constantDeclarationOwnRules ++ lookupRules

def constantDeclarationDirectives : List SourceExecFact :=
  constantDeclarationOwnDirectives ++ lookupDirectives

/-- Continuations registered with the generic object-lookup reloader.  A
lookup request and the code that consumes its observation are therefore
rearmed in the same verifier-owned transition. -/
def constantLookupContinuationRules : List Atom :=
  [constantOccupiedRule, constantGlobalMissingRule,
   constantStageFoundRule, constantStageMissingMoreRule,
   constantStageMissingLastRule, constantCommitRule,
   constantCommitFinishRule, constantAbortRule, constantAbortFinishRule]

def constantLookupStaticRows : List Atom :=
  constantLookupContinuationRules.map objectLookupRuleRow

def constantDeclarationStaticRows : List Atom :=
  constantLookupStaticRows ++ [sourceReloadRuleCaptureRow]

theorem constantLookupStaticRows_not_proofNeutral
    {row : Atom} (member : row ∈ constantLookupStaticRows) :
    isProofNeutralInitialAtom row = false := by
  rw [constantLookupStaticRows, List.mem_map] at member
  obtain ⟨rule, _, rfl⟩ := member
  exact objectLookupRuleRow_not_proofNeutral rule

@[simp] theorem sourceReloadRuleCaptureRow_not_proofNeutral :
    isProofNeutralInitialAtom sourceReloadRuleCaptureRow = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-constant-reload" [sourceVerifierReloadRule]
      (by decide)

theorem constantDeclarationRules_extract_exact :
    constantDeclarationRules.filterMap extractSupportedSourceExecFact =
      constantDeclarationDirectives := by
  rfl

/-! ## Bounded rule controls -/

private def fixtureSite : LocatedByteSpan :=
  { fileId := "constant.mm", start := 0, stop := 2 }

private def fixtureTerminator : LocatedByteSpan :=
  { fileId := "constant.mm", start := 8, stop := 10 }

private def fixtureName : LocatedName :=
  { span := { fileId := "constant.mm", start := 3, stop := 6 }
    name := "wff" }

private def fixtureStatement : RawStatement :=
  .constDecl fixtureSite [fixtureName] fixtureTerminator

private def fixtureOwner : Atom := .symbol "constant-source"

def fixtureEntry : ObjectOccurrence :=
  { kind := .constant, occurrence := fixtureName }

private def duplicatePrior : ObjectOccurrence :=
  { kind := .variable
    occurrence :=
      { span := { fileId := "earlier.mm", start := 1, stop := 4 }
        name := "wff" } }

def duplicateRejectedAtom : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 0,
      rawStatementAtom fixtureStatement, .symbol "occupied-object-name",
      objectOccurrenceAtom duplicatePrior]

private def nestedFixtureEnvironment : Atom :=
  sourceEnvironmentAtom fixtureOwner
    (listAtom id [.symbol "scope-checkpoint"]) 0 0

private def nestedFixtureRejectedAtom : Atom :=
  .expression
    [.symbol "mm-source-statement-rejected", fixtureOwner, natAtom 0,
      rawStatementAtom fixtureStatement, .symbol "constant-not-top-level",
      locatedByteSpanAtom fixtureSite]

private def nestedCanaryProgram : List Atom :=
  [constantNestedRule,
   sourceCurrentAtom fixtureOwner 0 1 fixtureStatement,
   nestedFixtureEnvironment]

theorem nestedCanary_rejects_without_advancing :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 nestedCanaryProgram).1
    nestedFixtureRejectedAtom ∈ final /\
      sourceControlAtom fixtureOwner 1 ∉ final := by
  decide +kernel

private def startCanaryAtoms : List Atom :=
  [constantStartRule,
   sourceCurrentAtom fixtureOwner 0 1 fixtureStatement,
   sourceInitialEnvironmentAtom fixtureOwner,
   objectFrontierAtom fixtureOwner objectRootKey]

private def startCanarySpace : Space := startCanaryAtoms.toFinset

private theorem startCanaryAtoms_nodup : startCanaryAtoms.Nodup := by
  decide +kernel

private theorem startCanaryAtoms_supported :
    cSupportedSourceExecFacts startCanaryAtoms = [constantStartDirective] := by
  rfl

theorem startCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace startCanarySpace) =
      some constantStartDirective := by
  exact reflective_selects_of_computable_supported_singleton
    startCanaryAtoms constantStartDirective startCanaryAtoms_nodup
    startCanaryAtoms_supported

theorem startCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies startCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact startCanarySpace
          constantStartDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected startCanary_selects_directive)

private def finishCanaryRequest : Atom :=
  .expression
    [.symbol "mm-source-constant-request", fixtureOwner, natAtom 0,
      natAtom 1, rawStatementAtom fixtureStatement,
      .symbol "dispatch-input", .symbol "dispatch-output",
      listAtom locatedNameAtom []]

private def fixtureTransactionOwner : Atom :=
  constantTransactionOwner fixtureOwner (natAtom 0)

private def fixtureCommitControl (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-source-constant-commit", fixtureOwner, natAtom 0,
      natAtom 1, rawStatementAtom fixtureStatement,
      .symbol "dispatch-input", .symbol "dispatch-output", cursor, frontier]

private def commitCanaryAtoms : List Atom :=
  [constantCommitRule,
   fixtureCommitControl objectRootKey (locatedNameAtom fixtureName),
   objectLinkAtom fixtureTransactionOwner objectRootKey
     (locatedNameAtom fixtureName) fixtureEntry,
   objectFrontierAtom fixtureOwner objectRootKey]

private def commitCanarySpace : Space := commitCanaryAtoms.toFinset

private theorem commitCanaryAtoms_nodup : commitCanaryAtoms.Nodup := by
  decide +kernel

private theorem commitCanaryAtoms_supported :
    cSupportedSourceExecFacts commitCanaryAtoms = [constantCommitDirective] := by
  rfl

theorem commitCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace commitCanarySpace) =
      some constantCommitDirective := by
  exact reflective_selects_of_computable_supported_singleton
    commitCanaryAtoms constantCommitDirective commitCanaryAtoms_nodup
    commitCanaryAtoms_supported

private theorem commitCanary_fire_agreement :
    (cFireReflectiveSourceExecFact commitCanaryAtoms
        constantCommitDirective).toFinset =
      fireReflectiveSourceExecFact commitCanarySpace
        constantCommitDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    commitCanaryAtoms constantCommitDirective commitCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      constantCommitDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      commitCanaryAtoms constantCommitDirective commitCanaryAtoms_nodup)

theorem commitCanary_appends_exact_occurrence :
    objectLinkAtom fixtureOwner objectRootKey (locatedNameAtom fixtureName)
        fixtureEntry ∈
      fireReflectiveSourceExecFact commitCanarySpace
        constantCommitDirective := by
  rw [← commitCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def finishCanaryAtoms : List Atom :=
  [constantCommitFinishRule,
   fixtureCommitControl (locatedNameAtom fixtureName)
     (locatedNameAtom fixtureName),
   objectFrontierAtom fixtureTransactionOwner
     (locatedNameAtom fixtureName),
   sourceReloadRuleCaptureRow]

private def finishCanarySpace : Space := finishCanaryAtoms.toFinset

private theorem finishCanaryAtoms_nodup : finishCanaryAtoms.Nodup := by
  decide +kernel

private theorem finishCanaryAtoms_supported :
    cSupportedSourceExecFacts finishCanaryAtoms =
      [constantCommitFinishDirective] := by
  rfl

theorem finishCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace finishCanarySpace) =
      some constantCommitFinishDirective := by
  exact reflective_selects_of_computable_supported_singleton
    finishCanaryAtoms constantCommitFinishDirective finishCanaryAtoms_nodup
    finishCanaryAtoms_supported

theorem finishCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies finishCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact finishCanarySpace
          constantCommitFinishDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected finishCanary_selects_directive)

private theorem finishCanary_fire_agreement :
    (cFireReflectiveSourceExecFact finishCanaryAtoms
        constantCommitFinishDirective).toFinset =
      fireReflectiveSourceExecFact finishCanarySpace
        constantCommitFinishDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    finishCanaryAtoms constantCommitFinishDirective finishCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      constantCommitFinishDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      finishCanaryAtoms constantCommitFinishDirective finishCanaryAtoms_nodup)

theorem finishCanary_advances_source :
    sourceControlAtom fixtureOwner 1 ∈
      fireReflectiveSourceExecFact finishCanarySpace
        constantCommitFinishDirective := by
  rw [← finishCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem finishCanary_marks_statement_applied :
    .expression
        [.symbol "mm-source-statement-applied", fixtureOwner, natAtom 0,
          rawStatementAtom fixtureStatement] ∈
      fireReflectiveSourceExecFact finishCanarySpace
        constantCommitFinishDirective := by
  rw [← finishCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem finishCanary_releases_source_reloader :
    sourceVerifierReloadRule ∈
      fireReflectiveSourceExecFact finishCanarySpace
        constantCommitFinishDirective := by
  rw [← finishCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def occupiedCanaryRequest : Atom :=
  .expression
    [.symbol "mm-source-constant-request", fixtureOwner, natAtom 0,
      natAtom 1, rawStatementAtom fixtureStatement,
      .symbol "dispatch-input", .symbol "dispatch-output",
      listAtom locatedNameAtom []]

private def stagedPriorName : LocatedName :=
  { span := { fileId := "constant.mm", start := 11, stop := 14 }
    name := "setvar" }

private def stagedPriorEntry : ObjectOccurrence :=
  { kind := .constant, occurrence := stagedPriorName }

private def occupiedCanaryAtoms : List Atom :=
  [constantOccupiedRule,
   lookupFoundAtom fixtureOwner occupiedCanaryRequest fixtureName
     duplicatePrior,
   objectLinkAtom fixtureTransactionOwner objectRootKey
     (locatedNameAtom stagedPriorName) stagedPriorEntry,
   objectFrontierAtom fixtureTransactionOwner
     (locatedNameAtom stagedPriorName)]

private def occupiedCanarySpace : Space := occupiedCanaryAtoms.toFinset

private theorem occupiedCanaryAtoms_nodup : occupiedCanaryAtoms.Nodup := by
  decide +kernel

private theorem occupiedCanaryAtoms_supported :
    cSupportedSourceExecFacts occupiedCanaryAtoms =
      [constantOccupiedDirective] := by
  rfl

theorem occupiedCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace occupiedCanarySpace) =
      some constantOccupiedDirective := by
  exact reflective_selects_of_computable_supported_singleton
    occupiedCanaryAtoms constantOccupiedDirective occupiedCanaryAtoms_nodup
    occupiedCanaryAtoms_supported

theorem occupiedCanary_rejects_cross_kind_collision :
    duplicateRejectedAtom ∈
      fireReflectiveSourceExecFact occupiedCanarySpace
        constantOccupiedDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      occupiedCanaryAtoms constantOccupiedDirective occupiedCanaryAtoms_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        constantOccupiedDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        occupiedCanaryAtoms constantOccupiedDirective
        occupiedCanaryAtoms_nodup)
  have computableMember : duplicateRejectedAtom ∈
      (cFireReflectiveSourceExecFact occupiedCanaryAtoms
        constantOccupiedDirective).toFinset :=
    List.mem_toFinset.mpr (by decide +kernel)
  rw [agreement] at computableMember
  simpa [occupiedCanarySpace] using computableMember

theorem occupiedCanary_does_not_commit_prior_stage :
    objectLinkAtom fixtureOwner objectRootKey
        (locatedNameAtom stagedPriorName) stagedPriorEntry ∉
      fireReflectiveSourceExecFact occupiedCanarySpace
        constantOccupiedDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      occupiedCanaryAtoms constantOccupiedDirective occupiedCanaryAtoms_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        constantOccupiedDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        occupiedCanaryAtoms constantOccupiedDirective
        occupiedCanaryAtoms_nodup)
  have computableNonmember : objectLinkAtom fixtureOwner objectRootKey
      (locatedNameAtom stagedPriorName) stagedPriorEntry ∉
        (cFireReflectiveSourceExecFact occupiedCanaryAtoms
          constantOccupiedDirective).toFinset := by decide +kernel
  rw [agreement] at computableNonmember
  simpa [occupiedCanarySpace] using computableNonmember

theorem occupiedCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies occupiedCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact occupiedCanarySpace
          constantOccupiedDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected occupiedCanary_selects_directive)

/-! ## Scanner/consumer reinstallation -/

private def continuationReloadCanaryAtoms : List Atom :=
  [objectLookupReloadRule,
   objectLookupReloadTriggerAtom fixtureOwner] ++
    objectLookupStaticRows ++ constantLookupStaticRows

private def continuationReloadCanarySpace : Space :=
  continuationReloadCanaryAtoms.toFinset

private theorem continuationReloadCanaryAtoms_nodup :
    continuationReloadCanaryAtoms.Nodup := by
  decide +kernel

private theorem continuationReloadCanaryAtoms_supported :
    cSupportedSourceExecFacts continuationReloadCanaryAtoms =
      [objectLookupReloadDirective] := by
  rfl

theorem continuationReloadCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace continuationReloadCanarySpace) =
      some objectLookupReloadDirective := by
  exact reflective_selects_of_computable_supported_singleton
    continuationReloadCanaryAtoms objectLookupReloadDirective
    continuationReloadCanaryAtoms_nodup
    continuationReloadCanaryAtoms_supported

private theorem continuationReloadCanary_fire_agreement :
    (cFireReflectiveSourceExecFact continuationReloadCanaryAtoms
        objectLookupReloadDirective).toFinset =
      fireReflectiveSourceExecFact continuationReloadCanarySpace
        objectLookupReloadDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    continuationReloadCanaryAtoms objectLookupReloadDirective
    continuationReloadCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      objectLookupReloadDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      continuationReloadCanaryAtoms objectLookupReloadDirective
      continuationReloadCanaryAtoms_nodup)

theorem continuationReloadCanary_reinstalls_occupied :
    constantOccupiedRule ∈
      fireReflectiveSourceExecFact continuationReloadCanarySpace
        objectLookupReloadDirective := by
  rw [← continuationReloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem continuationReloadCanary_reinstalls_global_missing :
    constantGlobalMissingRule ∈
      fireReflectiveSourceExecFact continuationReloadCanarySpace
        objectLookupReloadDirective := by
  rw [← continuationReloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem continuationReloadCanary_reinstalls_commit_finish :
    constantCommitFinishRule ∈
      fireReflectiveSourceExecFact continuationReloadCanarySpace
        objectLookupReloadDirective := by
  rw [← continuationReloadCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem continuationReloadCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies
      continuationReloadCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact continuationReloadCanarySpace
          objectLookupReloadDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected continuationReloadCanary_selects_directive)

#print axioms constantStep_durable_state_is_atomic
#print axioms constantStep_never_appends_nonconstant
#print axioms constantStep_finished_commits_staged_order
#print axioms constantDeclarationRules_extract_exact
#print axioms constantLookupStaticRows_not_proofNeutral
#print axioms sourceReloadRuleCaptureRow_not_proofNeutral
#print axioms nestedCanary_rejects_without_advancing
#print axioms startCanary_inhabits_target_native_type
#print axioms commitCanary_appends_exact_occurrence
#print axioms finishCanary_advances_source
#print axioms finishCanary_marks_statement_applied
#print axioms finishCanary_releases_source_reloader
#print axioms finishCanary_inhabits_target_native_type
#print axioms occupiedCanary_rejects_cross_kind_collision
#print axioms occupiedCanary_does_not_commit_prior_stage
#print axioms occupiedCanary_inhabits_target_native_type
#print axioms continuationReloadCanary_reinstalls_occupied
#print axioms continuationReloadCanary_reinstalls_global_missing
#print axioms continuationReloadCanary_reinstalls_commit_finish
#print axioms continuationReloadCanary_inhabits_target_native_type

end Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration
