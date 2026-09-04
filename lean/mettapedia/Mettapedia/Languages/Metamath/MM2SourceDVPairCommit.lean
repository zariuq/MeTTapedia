import Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution

/-!
# Transactional `$d` pair append in ordinary MM2

This module is the commit kernel between validated source-pair work and the
two runtime ledgers used by Metamath verification.  A verifier-owned
authorization names one exact `$d` statement occurrence and pair occurrence.
The ordinary MM2 rules consume the result of the finite occurrence lookup and
atomically extend:

* the scope-aligned source occurrence ledger, preserving
  first-versus-duplicate identity;
* the scope-local activity ledger, preserving live, inert, or shared ownership;
* the proof-facing symmetric DV rows, but only for a first live occurrence.

Scope exit restores both the source-occurrence and active-capability frontiers.
Thus `first` and `duplicate` are relative to the exact active source prefix,
not to declarations that have already left scope.

The authorization is deliberately in the reserved internal namespace.  This
kernel does not manufacture it from a pair-plan row: the upstream `$d`
validator must establish name membership, uniqueness, and exact pair-plan
derivation before emitting it.  Consequently these rules are reusable without
turning representation validation into source authorization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVPairCommit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

abbrev DVPair := String × String

/-! ## Verifier-owned authorization -/

inductive DVEndpointStatus where
  | live
  | inert
deriving DecidableEq, Repr

def dvEndpointStatusAtom : DVEndpointStatus → Atom
  | .live => .symbol "mm-source-dv-endpoints-live"
  | .inert => .symbol "mm-source-dv-endpoints-inert"

def decodeDVEndpointStatusAtom : Atom → Option DVEndpointStatus
  | .symbol "mm-source-dv-endpoints-live" => some .live
  | .symbol "mm-source-dv-endpoints-inert" => some .inert
  | _ => none

@[simp] theorem decodeDVEndpointStatusAtom_encoded
    (status : DVEndpointStatus) :
    decodeDVEndpointStatusAtom (dvEndpointStatusAtom status) = some status := by
  cases status <;> rfl

def dvPairAuthorizationAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (status : DVEndpointStatus) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-authorized", owner,
      natAtom statementPosition, natAtom pairPosition, stringPairAtom pair,
      dvEndpointStatusAtom status]

def decodeDVPairAuthorizationAtom (owner : Atom) :
    Atom → Option (Nat × Nat × DVPair × DVEndpointStatus)
  | .expression
      [.symbol "mm-internal-source-dv-pair-authorized", actualOwner,
        encodedStatementPosition, encodedPairPosition, encodedPair,
        encodedStatus] => do
      guard (actualOwner == owner)
      let statementPosition <- decodeNatAtom encodedStatementPosition
      let pairPosition <- decodeNatAtom encodedPairPosition
      let pair <- decodeStringPairAtom encodedPair
      let status <- decodeDVEndpointStatusAtom encodedStatus
      pure (statementPosition, pairPosition, pair, status)
  | _ => none

@[simp] theorem decodeDVPairAuthorizationAtom_encoded (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (status : DVEndpointStatus) :
    decodeDVPairAuthorizationAtom owner
      (dvPairAuthorizationAtom owner statementPosition pairPosition pair
        status) =
      some (statementPosition, pairPosition, pair, status) := by
  cases pair
  simp [decodeDVPairAuthorizationAtom, dvPairAuthorizationAtom]

@[simp] theorem dvPairAuthorizationAtom_not_proofNeutral (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (status : DVEndpointStatus) :
    isProofNeutralInitialAtom
      (dvPairAuthorizationAtom owner statementPosition pairPosition pair
        status) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-pair-authorized"
    [owner, natAtom statementPosition, natAtom pairPosition,
      stringPairAtom pair, dvEndpointStatusAtom status] (by decide)

def dvPairCommittedAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-committed", owner,
      natAtom statementPosition, natAtom pairPosition, stringPairAtom pair]

/-! ## Ordinary MM2 rule family -/

private def location (name : String) : Atom :=
  .expression [.symbol "03", .symbol name]

private def firstLiveLocation :=
  location "mm-source-dv-pair-commit-first-live"
private def firstInertLocation :=
  location "mm-source-dv-pair-commit-first-inert"
private def duplicateLiveLocation :=
  location "mm-source-dv-pair-commit-duplicate-live"
private def duplicateInertLocation :=
  location "mm-source-dv-pair-commit-duplicate-inert"
private def reloadLocation : Atom :=
  .expression [.symbol "36", .symbol "mm-source-dv-pair-commit-reload"]

private def pairTemplate : Atom :=
  .expression [.symbol "mm-pair", .var "left-name", .var "right-name"]

private def authorizationTemplate (status : DVEndpointStatus) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-authorized", .var "source",
      .var "statement-position", .var "pair-position", pairTemplate,
      dvEndpointStatusAtom status]

private def occurrenceKeyTemplate : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-occurrence", .var "source",
      .var "statement-position", .var "pair-position"]

private def occurrenceFrontierTemplate : Atom :=
  dvOccurrenceFrontierAtAtom (.var "source")
    (.var "occurrence-frontier")

private def occurrenceMissingTemplate (status : DVEndpointStatus) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-missing", .var "source",
      authorizationTemplate status, pairTemplate]

private def occurrenceFoundTemplate (status : DVEndpointStatus) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-found", .var "source",
      authorizationTemplate status, pairTemplate, .var "found-cursor",
      .expression
        [.symbol "mm-source-dv-occurrence-entry", pairTemplate,
          .var "found-occurrence-kind"]]

private def appendedOccurrenceLinkTemplate (kind : DVOccurrenceKind) : Atom :=
  .expression
    [.symbol "mm-source-dv-occurrence-link", .var "source",
      .var "occurrence-frontier", occurrenceKeyTemplate,
      .expression
        [.symbol "mm-source-dv-occurrence-entry", pairTemplate,
          dvOccurrenceKindAtom kind]]

private def appendedOccurrenceFrontierTemplate : Atom :=
  dvOccurrenceFrontierAtAtom (.var "source") occurrenceKeyTemplate

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-distinct-ledger", .var "source"]

private def activeFrontierTemplate : Atom :=
  sourceActivityFrontierAtom activeOwnerTemplate (.var "active-frontier")

private def appendedActiveFrontierTemplate : Atom :=
  sourceActivityFrontierAtom activeOwnerTemplate occurrenceKeyTemplate

private def leftRuntimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-caller-dv", .var "source", .var "left-name",
      .var "right-name"]

private def rightRuntimeRowTemplate : Atom :=
  .expression
    [.symbol "mm-caller-dv", .var "source", .var "right-name",
      .var "left-name"]

private def appendedActiveLinkTemplate (kind : DVOccurrenceKind)
    (capability : ActiveDistinctCapabilityKind) : Atom :=
  .expression
    [.symbol "mm-source-active-distinct-link", activeOwnerTemplate,
      .var "active-frontier", occurrenceKeyTemplate,
      dvOccurrenceKindAtom kind,
      activeDistinctCapabilityKindAtom capability,
      leftRuntimeRowTemplate, rightRuntimeRowTemplate]

private def committedTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-committed", .var "source",
      .var "statement-position", .var "pair-position", pairTemplate]

private def reloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-dv-pair-commit", .var "source"]

def dvPairCommitReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-pair-commit", owner]

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

private def firstCommitRuleFor (loc : Atom) (stem : String)
    (status : DVEndpointStatus)
    (capability : ActiveDistinctCapabilityKind) (publish : Bool) :
    Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let authorization := authorizationTemplate status
  let missing := occurrenceMissingTemplate status
  let patterns :=
    [self, authorization, missing, occurrenceFrontierTemplate,
      activeFrontierTemplate]
  let runtimeSinks : List Sink :=
    if publish then
      [.add leftRuntimeRowTemplate, .add rightRuntimeRowTemplate]
    else
      []
  let sinks : List Sink :=
    [.add self, .remove authorization, .remove missing,
      .remove occurrenceFrontierTemplate, .remove activeFrontierTemplate,
      .add (appendedOccurrenceLinkTemplate .first),
      .add appendedOccurrenceFrontierTemplate,
      .add (appendedActiveLinkTemplate .first capability),
      .add appendedActiveFrontierTemplate] ++ runtimeSinks ++
      [.add committedTemplate, .add reloadTriggerTemplate]
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

private def duplicateCommitRuleFor (loc : Atom) (stem : String)
    (status : DVEndpointStatus) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let authorization := authorizationTemplate status
  let found := occurrenceFoundTemplate status
  let patterns :=
    [self, authorization, found, occurrenceFrontierTemplate,
      activeFrontierTemplate]
  let sinks : List Sink :=
    [.add self, .remove authorization, .remove found,
      .remove occurrenceFrontierTemplate, .remove activeFrontierTemplate,
      .add (appendedOccurrenceLinkTemplate .duplicate),
      .add appendedOccurrenceFrontierTemplate,
      .add (appendedActiveLinkTemplate .duplicate .shared),
      .add appendedActiveFrontierTemplate, .add committedTemplate,
      .add reloadTriggerTemplate]
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

def firstLiveCommitRule : Atom :=
  (firstCommitRuleFor firstLiveLocation
    "mm-source-dv-pair-commit-first-live" .live .live true).1

def firstLiveCommitDirective : SourceExecFact :=
  (firstCommitRuleFor firstLiveLocation
    "mm-source-dv-pair-commit-first-live" .live .live true).2

def firstInertCommitRule : Atom :=
  (firstCommitRuleFor firstInertLocation
    "mm-source-dv-pair-commit-first-inert" .inert .inert false).1

def firstInertCommitDirective : SourceExecFact :=
  (firstCommitRuleFor firstInertLocation
    "mm-source-dv-pair-commit-first-inert" .inert .inert false).2

def duplicateLiveCommitRule : Atom :=
  (duplicateCommitRuleFor duplicateLiveLocation
    "mm-source-dv-pair-commit-duplicate-live" .live).1

def duplicateLiveCommitDirective : SourceExecFact :=
  (duplicateCommitRuleFor duplicateLiveLocation
    "mm-source-dv-pair-commit-duplicate-live" .live).2

def duplicateInertCommitRule : Atom :=
  (duplicateCommitRuleFor duplicateInertLocation
    "mm-source-dv-pair-commit-duplicate-inert" .inert).1

def duplicateInertCommitDirective : SourceExecFact :=
  (duplicateCommitRuleFor duplicateInertLocation
    "mm-source-dv-pair-commit-duplicate-inert" .inert).2

theorem extract_firstLiveCommitRule_exact :
    extractSupportedSourceExecFact firstLiveCommitRule =
      some firstLiveCommitDirective := by rfl

theorem extract_firstInertCommitRule_exact :
    extractSupportedSourceExecFact firstInertCommitRule =
      some firstInertCommitDirective := by rfl

theorem extract_duplicateLiveCommitRule_exact :
    extractSupportedSourceExecFact duplicateLiveCommitRule =
      some duplicateLiveCommitDirective := by rfl

theorem extract_duplicateInertCommitRule_exact :
    extractSupportedSourceExecFact duplicateInertCommitRule =
      some duplicateInertCommitDirective := by rfl

def dvPairCommitCoreRules : List Atom :=
  [firstLiveCommitRule, firstInertCommitRule,
    duplicateLiveCommitRule, duplicateInertCommitRule]

def dvPairCommitCoreDirectives : List SourceExecFact :=
  [firstLiveCommitDirective, firstInertCommitDirective,
    duplicateLiveCommitDirective, duplicateInertCommitDirective]

def dvPairCommitRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-pair-commit-rule", rule]

@[simp] theorem dvPairCommitRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (dvPairCommitRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-pair-commit-rule" [rule] (by decide)

def dvPairCommitStaticRows : List Atom :=
  dvPairCommitCoreRules.map dvPairCommitRuleRow

private def reloadSelf : Atom :=
  selfTemplate reloadLocation "dv-pair-commit-reload"

private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-commit-rule",
      .var "dv-pair-commit-rule"]

private def reloadPatterns : List Atom :=
  [reloadSelf, reloadTriggerTemplate, reloadRuleTemplate]

private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove reloadTriggerTemplate,
    .add (.var "dv-pair-commit-rule")]

def dvPairCommitReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def dvPairCommitReloadDirective : SourceExecFact where
  atom := dvPairCommitReloadRule
  loc := reloadLocation
  rule :=
    { priority := 36
      name := "mm-source-dv-pair-commit-reload"
      input := .compat (mkPattern reloadPatterns)
      guards := []
      tmpl := mkTemplate reloadSinks }

theorem extract_dvPairCommitReloadRule_exact :
    extractSupportedSourceExecFact dvPairCommitReloadRule =
      some dvPairCommitReloadDirective := by
  rfl

def dvPairCommitRules : List Atom :=
  dvPairCommitCoreRules ++ [dvPairCommitReloadRule]

def dvPairCommitDirectives : List SourceExecFact :=
  dvPairCommitCoreDirectives ++ [dvPairCommitReloadDirective]

theorem dvPairCommitRules_extract_exact :
    dvPairCommitRules.filterMap extractSupportedSourceExecFact =
      dvPairCommitDirectives := by
  rfl

/-! ## Complete one-pair executions -/

private def fixtureOwner : Atom := .symbol "dv-pair-commit-source"
private def fixturePair : DVPair := ("x", "y")
private def fixtureStatementPosition : Nat := 7
private def fixturePairPosition : Nat := 2
private def fixtureKey : Atom :=
  sourceDVPairOccurrenceKey fixtureOwner fixtureStatementPosition
    fixturePairPosition
private def fixtureOccurrenceFrontier : Atom := .symbol "occurrence-before"
private def fixtureActiveFrontier : Atom := .symbol "activity-before"
private def fixtureLeftRow : Atom := callerDVRow fixtureOwner "x" "y"
private def fixtureRightRow : Atom := callerDVRow fixtureOwner "y" "x"

private def firstLiveAuthorization : Atom :=
  dvPairAuthorizationAtom fixtureOwner fixtureStatementPosition
    fixturePairPosition fixturePair .live

private def firstLiveProgram : List Atom :=
  dvPairCommitRules ++
    [firstLiveAuthorization,
      lookupMissingAtom fixtureOwner firstLiveAuthorization fixturePair,
      dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        fixtureActiveFrontier]

theorem firstLiveProgram_commits_exact_capability :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 firstLiveProgram).1
    dvOccurrenceLinkAtAtom fixtureOwner fixtureOccurrenceFrontier fixtureKey
        { pair := fixturePair, kind := .first } ∈ final ∧
      dvOccurrenceFrontierAtAtom fixtureOwner fixtureKey ∈ final ∧
      activeDistinctLinkAtom fixtureOwner fixtureActiveFrontier fixtureKey
        .first .live fixtureLeftRow fixtureRightRow ∈ final ∧
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        fixtureKey ∈ final ∧
      fixtureLeftRow ∈ final ∧ fixtureRightRow ∈ final ∧
      dvPairCommittedAtom fixtureOwner fixtureStatementPosition
        fixturePairPosition fixturePair ∈ final ∧
      dvPairCommitReloadTriggerAtom fixtureOwner ∈ final ∧
      firstLiveAuthorization ∉ final := by
  decide +kernel

def firstLiveProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 1 firstLiveProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 firstLiveProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 1
    firstLiveProgram

private def firstInertAuthorization : Atom :=
  dvPairAuthorizationAtom fixtureOwner fixtureStatementPosition
    fixturePairPosition fixturePair .inert

private def firstInertProgram : List Atom :=
  dvPairCommitRules ++
    [firstInertAuthorization,
      lookupMissingAtom fixtureOwner firstInertAuthorization fixturePair,
      dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        fixtureActiveFrontier]

theorem firstInertProgram_commits_without_capability :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 2 firstInertProgram).1
    dvOccurrenceLinkAtAtom fixtureOwner fixtureOccurrenceFrontier fixtureKey
        { pair := fixturePair, kind := .first } ∈ final ∧
      activeDistinctLinkAtom fixtureOwner fixtureActiveFrontier fixtureKey
        .first .inert fixtureLeftRow fixtureRightRow ∈ final ∧
      fixtureLeftRow ∉ final ∧ fixtureRightRow ∉ final ∧
      dvPairCommittedAtom fixtureOwner fixtureStatementPosition
        fixturePairPosition fixturePair ∈ final ∧
      dvPairCommitReloadTriggerAtom fixtureOwner ∈ final := by
  decide +kernel

def firstInertProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 2 firstInertProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 2 firstInertProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 2
    firstInertProgram

private def priorOccurrence : MarkedDVOccurrence :=
  { pair := fixturePair, kind := .first }
private def priorOccurrenceCursor : Atom := .symbol "first-occurrence"
private def priorOccurrenceNext : Atom := fixtureOccurrenceFrontier
private def priorActiveCursor : Atom := .symbol "first-activity"

private def duplicateAuthorization : Atom :=
  dvPairAuthorizationAtom fixtureOwner fixtureStatementPosition
    fixturePairPosition fixturePair .live

private def duplicateProgram : List Atom :=
  dvPairCommitRules ++
    [duplicateAuthorization,
      lookupFoundAtAtom fixtureOwner duplicateAuthorization fixturePair
        priorOccurrenceCursor priorOccurrence,
      dvOccurrenceLinkAtAtom fixtureOwner priorOccurrenceCursor
        priorOccurrenceNext priorOccurrence,
      dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
      activeDistinctLinkAtom fixtureOwner priorActiveCursor
        fixtureActiveFrontier .first .live fixtureLeftRow fixtureRightRow,
      sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
        fixtureActiveFrontier,
      fixtureLeftRow, fixtureRightRow]

theorem duplicateProgram_preserves_shared_capability :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 3 duplicateProgram).1
    dvOccurrenceLinkAtAtom fixtureOwner fixtureOccurrenceFrontier fixtureKey
        { pair := fixturePair, kind := .duplicate } ∈ final ∧
      activeDistinctLinkAtom fixtureOwner fixtureActiveFrontier fixtureKey
        .duplicate .shared fixtureLeftRow fixtureRightRow ∈ final ∧
      activeDistinctLinkAtom fixtureOwner priorActiveCursor
        fixtureActiveFrontier .first .live fixtureLeftRow fixtureRightRow ∈
          final ∧
      fixtureLeftRow ∈ final ∧ fixtureRightRow ∈ final ∧
      dvPairCommittedAtom fixtureOwner fixtureStatementPosition
        fixturePairPosition fixturePair ∈ final ∧
      dvPairCommitReloadTriggerAtom fixtureOwner ∈ final ∧
      duplicateAuthorization ∉ final := by
  decide +kernel

def duplicateProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 3 duplicateProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 3 duplicateProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 3
    duplicateProgram

private def reloadProgram : List Atom :=
  [dvPairCommitReloadRule, dvPairCommitReloadTriggerAtom fixtureOwner] ++
    dvPairCommitStaticRows

theorem reloadProgram_restores_complete_rule_family :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 reloadProgram).1
    (dvPairCommitCoreRules.all fun rule => rule ∈ final) = true ∧
      dvPairCommitReloadTriggerAtom fixtureOwner ∉ final := by
  decide +kernel

def reloadProgram_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 1 reloadProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 reloadProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 1 reloadProgram

/-! ## Severance controls -/

private def otherPair : DVPair := ("u", "v")

/-- The lookup result and authorization must name the same exact pair. -/
theorem firstLiveRule_rejects_mismatched_pair :
    (cmatchInputSpec []
      [firstLiveCommitRule, firstLiveAuthorization,
        lookupMissingAtom fixtureOwner firstLiveAuthorization otherPair,
        dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
        sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
          fixtureActiveFrontier]
      firstLiveCommitDirective.rule.input).isEmpty = true := by
  decide +kernel

/-- A result owned by another source cannot extend this source's ledgers. -/
theorem firstLiveRule_rejects_wrong_result_owner :
    (cmatchInputSpec []
      [firstLiveCommitRule, firstLiveAuthorization,
        lookupMissingAtom (.symbol "other-source") firstLiveAuthorization
          fixturePair,
        dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
        sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
          fixtureActiveFrontier]
      firstLiveCommitDirective.rule.input).isEmpty = true := by
  decide +kernel

/-- A duplicate observation cannot take the first-occurrence branch. -/
theorem firstLiveRule_rejects_found_occurrence :
    (cmatchInputSpec []
      [firstLiveCommitRule, firstLiveAuthorization,
        lookupFoundAtAtom fixtureOwner firstLiveAuthorization fixturePair
          priorOccurrenceCursor priorOccurrence,
        dvOccurrenceFrontierAtAtom fixtureOwner fixtureOccurrenceFrontier,
        sourceActivityFrontierAtom (activeDistinctLedgerOwner fixtureOwner)
          fixtureActiveFrontier]
      firstLiveCommitDirective.rule.input).isEmpty = true := by
  decide +kernel

section AxiomAudit

#print axioms decodeDVEndpointStatusAtom_encoded
#print axioms decodeDVPairAuthorizationAtom_encoded
#print axioms dvPairAuthorizationAtom_not_proofNeutral
#print axioms extract_firstLiveCommitRule_exact
#print axioms extract_firstInertCommitRule_exact
#print axioms extract_duplicateLiveCommitRule_exact
#print axioms extract_duplicateInertCommitRule_exact
#print axioms extract_dvPairCommitReloadRule_exact
#print axioms dvPairCommitRules_extract_exact
#print axioms dvPairCommitRuleRow_not_proofNeutral
#print axioms firstLiveProgram_commits_exact_capability
#print axioms firstLiveProgram_has_oslf_native_trace
#print axioms firstInertProgram_commits_without_capability
#print axioms firstInertProgram_has_oslf_native_trace
#print axioms duplicateProgram_preserves_shared_capability
#print axioms duplicateProgram_has_oslf_native_trace
#print axioms reloadProgram_restores_complete_rule_family
#print axioms reloadProgram_has_oslf_native_trace
#print axioms firstLiveRule_rejects_mismatched_pair
#print axioms firstLiveRule_rejects_wrong_result_owner
#print axioms firstLiveRule_rejects_found_occurrence

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVPairCommit
