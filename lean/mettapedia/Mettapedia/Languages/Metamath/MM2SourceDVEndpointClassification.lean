import Mettapedia.Languages.Metamath.MM2SourceActiveFloatingLookup
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchWitness

/-!
# `$d` endpoint classification in ordinary MM2

After the complete pair plan has been validated, each derived pair is checked
against the scoped active floating-hypothesis ledger.  Both endpoints found
means the pair is live for proof execution; either endpoint missing means the
source-level pair is retained but inert in the proof-facing projection.

This module emits a protected status row.  It deliberately does not authorize
or commit the pair: statement-wide staging must collect every status before
any durable `$d` effect is published.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVEndpointClassification

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActiveFloatingLookup
open Mettapedia.Languages.Metamath.MM2SourceDVNameValidation
open Mettapedia.Languages.Metamath.MM2SourceDVPairCommit
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceDVPairValidation
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

abbrev DVPair := String × String

/-! ## Protected request, controls, and result -/

def dvEndpointClassificationRequestAtom (owner : Atom)
    (statementPosition pairCount pairPosition : Nat) (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-request", owner,
      natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      stringPairAtom pair]

def dvEndpointLeftControlAtom (owner : Atom)
    (statementPosition pairCount pairPosition : Nat) (pair : DVPair)
    (right : LocatedName) (frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-left", owner,
      natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      stringPairAtom pair, locatedNameAtom right, frontier]

def dvEndpointRightControlAtom (owner : Atom)
    (statementPosition pairCount pairPosition : Nat) (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-right", owner,
      natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      stringPairAtom pair]

def dvEndpointClassificationAtom (owner : Atom)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (status : DVEndpointStatus) : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-status", owner,
      natAtom statementPosition, natAtom pairPosition, stringPairAtom pair,
      dvEndpointStatusAtom status]

def decodeDVEndpointClassificationAtom (owner : Atom) :
    Atom → Option (Nat × Nat × DVPair × DVEndpointStatus)
  | .expression
      [.symbol "mm-internal-source-dv-endpoint-status", actualOwner,
        encodedStatementPosition, encodedPairPosition, encodedPair,
        encodedStatus] => do
      guard (actualOwner == owner)
      let statementPosition <- decodeNatAtom encodedStatementPosition
      let pairPosition <- decodeNatAtom encodedPairPosition
      let pair <- decodeStringPairAtom encodedPair
      let status <- decodeDVEndpointStatusAtom encodedStatus
      pure (statementPosition, pairPosition, pair, status)
  | _ => none

@[simp] theorem decodeDVEndpointClassificationAtom_encoded
    (owner : Atom) (statementPosition pairPosition : Nat) (pair : DVPair)
    (status : DVEndpointStatus) :
    decodeDVEndpointClassificationAtom owner
        (dvEndpointClassificationAtom owner statementPosition pairPosition
          pair status) =
      some (statementPosition, pairPosition, pair, status) := by
  simp [decodeDVEndpointClassificationAtom, dvEndpointClassificationAtom]

@[simp] theorem dvEndpointClassificationRequestAtom_not_proofNeutral
    (owner : Atom) (statementPosition pairCount pairPosition : Nat)
    (pair : DVPair) :
    isProofNeutralInitialAtom
      (dvEndpointClassificationRequestAtom owner statementPosition pairCount
        pairPosition pair) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-endpoint-request"
    [owner, natAtom statementPosition, natAtom pairCount, natAtom pairPosition,
      stringPairAtom pair] (by decide)

/-! ## Exact two-endpoint protocol -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def startLocation :=
  location "02" "mm-source-dv-endpoint-start"
private def leftFoundLocation :=
  location "03" "mm-source-dv-endpoint-left-found"
private def leftMissingLocation :=
  location "03" "mm-source-dv-endpoint-left-missing"
private def rightFoundLocation :=
  location "03" "mm-source-dv-endpoint-right-found"
private def rightMissingLocation :=
  location "03" "mm-source-dv-endpoint-right-missing"
private def reloadLocation :=
  location "36" "mm-source-dv-endpoint-reload"

private def leftNameTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "left-span", .var "left-name"]
private def rightNameTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "right-span", .var "right-name"]
private def pairTemplate : Atom :=
  .expression
    [.symbol "mm-pair", .var "left-name", .var "right-name"]

private def requestTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-request", .var "source",
      .var "statement-position", .var "pair-count", .var "pair-position",
      pairTemplate]

private def validatedPairTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validated", .var "source",
      .var "statement-position", .var "pair-position", pairTemplate,
      leftNameTemplate, rightNameTemplate]

private def pairValidationCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-pair-validation-complete",
      .var "source", .var "statement-position", .var "pair-count"]

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]
private def activeFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", activeOwnerTemplate,
      .var "active-floating-frontier"]

private def leftControlTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-left", .var "source",
      .var "statement-position", .var "pair-count", .var "pair-position",
      pairTemplate, rightNameTemplate, .var "active-floating-frontier"]

private def rightControlTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-right", .var "source",
      .var "statement-position", .var "pair-count", .var "pair-position",
      pairTemplate]

private def floatingLookupTemplate (control candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-lookup", .var "source",
      control, candidate, objectRootKey,
      .var "active-floating-frontier"]

private def floatingFoundTemplate (control candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-found", .var "source",
      control, candidate, .var "floating-runtime-row"]

private def floatingMissingTemplate (control candidate : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-missing", .var "source",
      control, candidate]

private def liveTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-status", .var "source",
      .var "statement-position", .var "pair-position", pairTemplate,
      .symbol "mm-source-dv-endpoints-live"]

private def inertTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-status", .var "source",
      .var "statement-position", .var "pair-position", pairTemplate,
      .symbol "mm-source-dv-endpoints-inert"]

private def activeFloatingReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-source-active-floating", .var "source"]
private def reloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-dv-endpoint", .var "source"]

def dvEndpointReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-dv-endpoint", owner]

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

private def mkCompatDirective (atom loc : Atom) (priority : Nat)
    (name : String) (patterns : List Atom) (sinks : List Sink) :
    SourceExecFact :=
  { atom
    loc
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def startSelf : Atom := selfTemplate startLocation "dv-endpoint-start"
private def startPatterns : List Atom :=
  [startSelf, requestTemplate, validatedPairTemplate,
    pairValidationCompleteTemplate, activeFrontierTemplate]
private def startSinks : List Sink :=
  [.add startSelf, .remove requestTemplate,
    .add (floatingLookupTemplate leftControlTemplate leftNameTemplate),
    .add activeFloatingReloadTemplate, .add reloadTriggerTemplate]

def endpointStartRule : Atom := mkRule startLocation startPatterns startSinks
def endpointStartDirective : SourceExecFact :=
  mkCompatDirective endpointStartRule startLocation 2
    "mm-source-dv-endpoint-start" startPatterns startSinks

private def leftFoundSelf : Atom :=
  selfTemplate leftFoundLocation "dv-endpoint-left-found"
private def leftFoundObservation : Atom :=
  floatingFoundTemplate leftControlTemplate leftNameTemplate
private def leftFoundPatterns : List Atom :=
  [leftFoundSelf, leftFoundObservation]
private def leftFoundSinks : List Sink :=
  [.add leftFoundSelf, .remove leftFoundObservation,
    .add (floatingLookupTemplate rightControlTemplate rightNameTemplate),
    .add activeFloatingReloadTemplate, .add reloadTriggerTemplate]

def endpointLeftFoundRule : Atom :=
  mkRule leftFoundLocation leftFoundPatterns leftFoundSinks
def endpointLeftFoundDirective : SourceExecFact :=
  mkCompatDirective endpointLeftFoundRule leftFoundLocation 3
    "mm-source-dv-endpoint-left-found" leftFoundPatterns leftFoundSinks

private def terminalRuleFor (loc : Atom) (stem : String)
    (observation result : Atom) : Atom × SourceExecFact :=
  let self := selfTemplate loc stem
  let patterns := [self, observation]
  let sinks : List Sink := [.add self, .remove observation, .add result]
  let atom := mkRule loc patterns sinks
  (atom, mkCompatDirective atom loc 3 stem patterns sinks)

def endpointLeftMissingRule : Atom :=
  (terminalRuleFor leftMissingLocation "mm-source-dv-endpoint-left-missing"
    (floatingMissingTemplate leftControlTemplate leftNameTemplate)
    inertTemplate).1
def endpointLeftMissingDirective : SourceExecFact :=
  (terminalRuleFor leftMissingLocation "mm-source-dv-endpoint-left-missing"
    (floatingMissingTemplate leftControlTemplate leftNameTemplate)
    inertTemplate).2

def endpointRightFoundRule : Atom :=
  (terminalRuleFor rightFoundLocation "mm-source-dv-endpoint-right-found"
    (floatingFoundTemplate rightControlTemplate rightNameTemplate)
    liveTemplate).1
def endpointRightFoundDirective : SourceExecFact :=
  (terminalRuleFor rightFoundLocation "mm-source-dv-endpoint-right-found"
    (floatingFoundTemplate rightControlTemplate rightNameTemplate)
    liveTemplate).2

def endpointRightMissingRule : Atom :=
  (terminalRuleFor rightMissingLocation "mm-source-dv-endpoint-right-missing"
    (floatingMissingTemplate rightControlTemplate rightNameTemplate)
    inertTemplate).1
def endpointRightMissingDirective : SourceExecFact :=
  (terminalRuleFor rightMissingLocation "mm-source-dv-endpoint-right-missing"
    (floatingMissingTemplate rightControlTemplate rightNameTemplate)
    inertTemplate).2

theorem extract_endpointStartRule_exact :
    extractSupportedSourceExecFact endpointStartRule =
      some endpointStartDirective := by rfl
theorem extract_endpointLeftFoundRule_exact :
    extractSupportedSourceExecFact endpointLeftFoundRule =
      some endpointLeftFoundDirective := by rfl
theorem extract_endpointLeftMissingRule_exact :
    extractSupportedSourceExecFact endpointLeftMissingRule =
      some endpointLeftMissingDirective := by rfl
theorem extract_endpointRightFoundRule_exact :
    extractSupportedSourceExecFact endpointRightFoundRule =
      some endpointRightFoundDirective := by rfl
theorem extract_endpointRightMissingRule_exact :
    extractSupportedSourceExecFact endpointRightMissingRule =
      some endpointRightMissingDirective := by rfl

def endpointStepRules : List Atom :=
  [endpointLeftFoundRule, endpointLeftMissingRule,
    endpointRightFoundRule, endpointRightMissingRule]
def endpointStepDirectives : List SourceExecFact :=
  [endpointLeftFoundDirective, endpointLeftMissingDirective,
    endpointRightFoundDirective, endpointRightMissingDirective]

def endpointRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-dv-endpoint-rule", rule]

@[simp] theorem endpointRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (endpointRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-dv-endpoint-rule" [rule] (by decide)

def endpointStaticRows : List Atom := endpointStepRules.map endpointRuleRow

private def reloadSelf : Atom :=
  selfTemplate reloadLocation "dv-endpoint-reload"
private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-dv-endpoint-rule",
      .var "dv-endpoint-rule"]
private def reloadPatterns : List Atom :=
  [reloadSelf, reloadTriggerTemplate, reloadRuleTemplate]
private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove reloadTriggerTemplate,
    .add (.var "dv-endpoint-rule")]

def endpointReloadRule : Atom := mkRule reloadLocation reloadPatterns reloadSinks
def endpointReloadDirective : SourceExecFact :=
  mkCompatDirective endpointReloadRule reloadLocation 36
    "mm-source-dv-endpoint-reload" reloadPatterns reloadSinks

theorem extract_endpointReloadRule_exact :
    extractSupportedSourceExecFact endpointReloadRule =
      some endpointReloadDirective := by rfl

def endpointRules : List Atom :=
  endpointStartRule :: endpointStepRules ++ [endpointReloadRule]
def endpointDirectives : List SourceExecFact :=
  endpointStartDirective :: endpointStepDirectives ++ [endpointReloadDirective]

theorem endpointRules_extract_exact :
    endpointRules.filterMap extractSupportedSourceExecFact =
      endpointDirectives := by rfl

/-! ## Rule-local execution receipts -/

private def fixtureOwner : Atom := .symbol "dv-endpoint-source"
private def fixturePair : DVPair := ("x", "y")
private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "dv-endpoint.mm", start, stop }
private def leftName : LocatedName :=
  { span := fixtureSpan 3 4, name := "x" }
private def rightName : LocatedName :=
  { span := fixtureSpan 5 6, name := "y" }
private def frontier : Atom := .expression [.symbol "active-hypothesis-frontier"]
private def request : Atom :=
  dvEndpointClassificationRequestAtom fixtureOwner 0 1 0 fixturePair
private def leftControl : Atom :=
  dvEndpointLeftControlAtom fixtureOwner 0 1 0 fixturePair rightName frontier
private def rightControl : Atom :=
  dvEndpointRightControlAtom fixtureOwner 0 1 0 fixturePair
private def leftRuntime : Atom :=
  hypothesisLookupRow fixtureOwner (.floating "wx" "wff" "x")
private def rightRuntime : Atom :=
  hypothesisLookupRow fixtureOwner (.floating "wy" "wff" "y")

theorem endpointStartDirective_sinks_exact :
    endpointStartDirective.rule.tmpl.sinks = startSinks := by
  rfl

private def startCertificate : Atom :=
  dvPairValidatedAtom fixtureOwner 0 0 fixturePair leftName rightName
private def startComplete : Atom :=
  dvPairValidationCompleteAtom fixtureOwner 0 1
private def startFrontier : Atom :=
  sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
    frontier
private def startData : List Atom :=
  [request, startCertificate, startComplete, startFrontier]
private def startRead : List Atom := endpointStartRule :: startData
private def startSubst₁ : Subst :=
  (cmatchAtom [] startSelf endpointStartRule).getD []
private def startSubst₂ : Subst :=
  (cmatchAtom startSubst₁ requestTemplate request).getD []
private def startSubst₃ : Subst :=
  (cmatchAtom startSubst₂ validatedPairTemplate startCertificate).getD []
private def startSubst₄ : Subst :=
  (cmatchAtom startSubst₃ pairValidationCompleteTemplate startComplete).getD []
private def startSubst₅ : Subst :=
  (cmatchAtom startSubst₄ activeFrontierTemplate startFrontier).getD []

private theorem start_match_path :
    MatchWitnessPath startRead startPatterns [] [] startSubst₅
      [startFrontier, startComplete, startCertificate, request,
        endpointStartRule] := by
  apply MatchWitnessPath.cons (witness := endpointStartRule)
    (after := startSubst₁) (by simp [startRead]) (by rfl)
  apply MatchWitnessPath.cons (witness := request)
    (after := startSubst₂) (by
      change request ∈ endpointStartRule :: startData
      apply List.mem_cons_of_mem
      change request ∈ request :: [startCertificate, startComplete,
        startFrontier]
      exact List.mem_cons_self) (by rfl)
  apply MatchWitnessPath.cons (witness := startCertificate)
    (after := startSubst₃) (by
      change startCertificate ∈ endpointStartRule :: startData
      apply List.mem_cons_of_mem
      change startCertificate ∈ request :: startCertificate ::
        [startComplete, startFrontier]
      exact List.mem_cons_of_mem _ List.mem_cons_self) (by rfl)
  apply MatchWitnessPath.cons (witness := startComplete)
    (after := startSubst₄) (by
      change startComplete ∈ endpointStartRule :: startData
      apply List.mem_cons_of_mem
      change startComplete ∈ request :: startCertificate :: startComplete ::
        [startFrontier]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)) (by rfl)
  apply MatchWitnessPath.cons (witness := startFrontier)
    (after := startSubst₅) (by
      change startFrontier ∈ endpointStartRule :: startData
      apply List.mem_cons_of_mem
      change startFrontier ∈ request :: startCertificate :: startComplete ::
        [startFrontier]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))) (by rfl)
  exact MatchWitnessPath.nil _ _

private theorem start_match_row :
    startSubst₅ ∈
      (cmatchInputSpec []
        (endpointStartDirective.atom :: startData.erase
          endpointStartDirective.atom)
        endpointStartDirective.rule.input).map Prod.fst := by
  have pathMember := matchWitnessPath_mem_cmatchInputSpec start_match_path
  have eraseExact :
      startData.erase endpointStartDirective.atom = startData := by
    decide +kernel
  rw [eraseExact]
  rw [show endpointStartDirective.atom = endpointStartRule by rfl]
  rw [show endpointStartDirective.rule.input =
    .compat { atoms := startPatterns } by rfl]
  simpa only [startRead] using pathMember

theorem startCanary_emits_exact_left_lookup :
    activeFloatingLookupAtom fixtureOwner leftControl leftName objectRootKey
        frontier ∈
      cFireReflectiveSourceExecFact startData endpointStartDirective := by
  apply mem_cFireReflectiveSourceExecFact_of_add_sink startData
    endpointStartDirective [.add startSelf, .remove requestTemplate]
    (floatingLookupTemplate leftControlTemplate leftNameTemplate)
    (activeFloatingLookupAtom fixtureOwner leftControl leftName objectRootKey
      frontier)
    [.add activeFloatingReloadTemplate, .add reloadTriggerTemplate]
    (by rfl) startSubst₅ start_match_row (by rfl)
  intro sink member
  simp at member
  rcases member with rfl | rfl <;> exact ⟨_, rfl⟩

private def leftFoundObservedAtom : Atom :=
  activeFloatingFoundAtom fixtureOwner leftControl leftName leftRuntime
private def leftFoundData : List Atom := [leftFoundObservedAtom]
private def leftFoundRead : List Atom :=
  [endpointLeftFoundRule, leftFoundObservedAtom]
private def leftFoundSubst₁ : Subst :=
  (cmatchAtom [] leftFoundSelf endpointLeftFoundRule).getD []
private def leftFoundSubst₂ : Subst :=
  (cmatchAtom leftFoundSubst₁ leftFoundObservation
    leftFoundObservedAtom).getD []

private theorem leftFound_match_path :
    MatchWitnessPath leftFoundRead leftFoundPatterns [] [] leftFoundSubst₂
      [leftFoundObservedAtom, endpointLeftFoundRule] := by
  apply MatchWitnessPath.cons (witness := endpointLeftFoundRule)
    (after := leftFoundSubst₁) (by simp [leftFoundRead]) (by rfl)
  apply MatchWitnessPath.cons (witness := leftFoundObservedAtom)
    (after := leftFoundSubst₂) (by simp [leftFoundRead]) (by rfl)
  exact MatchWitnessPath.nil _ _

private theorem leftFound_match_row :
    leftFoundSubst₂ ∈
      (cmatchInputSpec []
        (endpointLeftFoundDirective.atom :: leftFoundData.erase
          endpointLeftFoundDirective.atom)
        endpointLeftFoundDirective.rule.input).map Prod.fst := by
  have pathMember := matchWitnessPath_mem_cmatchInputSpec leftFound_match_path
  have eraseExact :
      leftFoundData.erase endpointLeftFoundDirective.atom =
        leftFoundData := by
    decide +kernel
  rw [eraseExact]
  rw [show endpointLeftFoundDirective.atom = endpointLeftFoundRule by rfl]
  rw [show endpointLeftFoundDirective.rule.input =
    .compat { atoms := leftFoundPatterns } by rfl]
  simpa only [leftFoundRead, leftFoundData] using pathMember

theorem leftFoundCanary_emits_exact_right_lookup :
    activeFloatingLookupAtom fixtureOwner rightControl rightName objectRootKey
        frontier ∈
      cFireReflectiveSourceExecFact leftFoundData
        endpointLeftFoundDirective := by
  apply mem_cFireReflectiveSourceExecFact_of_add_sink leftFoundData
    endpointLeftFoundDirective
    [.add leftFoundSelf, .remove leftFoundObservation]
    (floatingLookupTemplate rightControlTemplate rightNameTemplate)
    (activeFloatingLookupAtom fixtureOwner rightControl rightName objectRootKey
      frontier)
    [.add activeFloatingReloadTemplate, .add reloadTriggerTemplate]
    (by rfl) leftFoundSubst₂ leftFound_match_row (by rfl)
  intro sink member
  simp at member
  rcases member with rfl | rfl <;> exact ⟨_, rfl⟩

private def rightFoundSelf : Atom :=
  selfTemplate rightFoundLocation "mm-source-dv-endpoint-right-found"
private def rightFoundObservationTemplate : Atom :=
  floatingFoundTemplate rightControlTemplate rightNameTemplate
private def rightFoundPatterns : List Atom :=
  [rightFoundSelf, rightFoundObservationTemplate]
private def leftMissingSelf : Atom :=
  selfTemplate leftMissingLocation "mm-source-dv-endpoint-left-missing"
private def leftMissingObservationTemplate : Atom :=
  floatingMissingTemplate leftControlTemplate leftNameTemplate
private def leftMissingPatterns : List Atom :=
  [leftMissingSelf, leftMissingObservationTemplate]
private def rightMissingSelf : Atom :=
  selfTemplate rightMissingLocation "mm-source-dv-endpoint-right-missing"
private def rightMissingObservationTemplate : Atom :=
  floatingMissingTemplate rightControlTemplate rightNameTemplate
private def rightMissingPatterns : List Atom :=
  [rightMissingSelf, rightMissingObservationTemplate]

private def liveObservation : Atom :=
  activeFloatingFoundAtom fixtureOwner rightControl rightName rightRuntime
private def leftMissingObservation : Atom :=
  activeFloatingMissingAtom fixtureOwner leftControl leftName
private def rightMissingObservation : Atom :=
  activeFloatingMissingAtom fixtureOwner rightControl rightName

private theorem terminalCanary_emits_result
    (rule self observationPattern observed resultTemplate result : Atom)
    (directive : SourceExecFact)
    (patterns : List Atom)
    (sinks_exact : directive.rule.tmpl.sinks =
      [.add self, .remove observationPattern] ++ [.add resultTemplate])
    (first : Subst)
    (first_match : cmatchAtom [] self rule = some first)
    (final : Subst)
    (second_match :
      cmatchAtom first observationPattern observed = some final)
    (atom_exact : directive.atom = rule)
    (input_exact : directive.rule.input = .compat { atoms := patterns })
    (patterns_exact : patterns = [self, observationPattern])
    (observed_ne_rule : observed ≠ rule)
    (instantiates :
      instantiateTemplateAtom? final resultTemplate = some result) :
    result ∈ cFireReflectiveSourceExecFact [observed] directive := by
  have path : MatchWitnessPath [rule, observed] patterns [] [] final
      [observed, rule] := by
    rw [patterns_exact]
    apply MatchWitnessPath.cons (witness := rule) (after := first)
      (by simp) first_match
    apply MatchWitnessPath.cons (witness := observed) (after := final)
      (by simp) second_match
    exact MatchWitnessPath.nil _ _
  have pathMember := matchWitnessPath_mem_cmatchInputSpec path
  have rowMember : final ∈
      (cmatchInputSpec []
        (directive.atom :: [observed].erase directive.atom)
        directive.rule.input).map Prod.fst := by
    rw [atom_exact, input_exact]
    simpa [observed_ne_rule] using pathMember
  exact mem_cFireReflectiveSourceExecFact_of_last_add [observed]
    directive [.add self, .remove observationPattern] resultTemplate result
    sinks_exact final rowMember instantiates

theorem rightFoundCanary_emits_live :
    dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .live ∈
      cFireReflectiveSourceExecFact [liveObservation]
        endpointRightFoundDirective := by
  apply terminalCanary_emits_result endpointRightFoundRule rightFoundSelf
    rightFoundObservationTemplate liveObservation liveTemplate
    (dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .live)
    endpointRightFoundDirective rightFoundPatterns (by rfl)
    ((cmatchAtom [] rightFoundSelf endpointRightFoundRule).getD []) (by rfl)
    ((cmatchAtom
      ((cmatchAtom [] rightFoundSelf endpointRightFoundRule).getD [])
      rightFoundObservationTemplate liveObservation).getD []) (by rfl)
    (by rfl) (by rfl) (by rfl) (by decide) (by rfl)

private def rightFoundOSLFAtoms : List Atom :=
  [endpointRightFoundRule, liveObservation]
private def rightFoundOSLFSource : Space := rightFoundOSLFAtoms.toFinset
private theorem rightFoundOSLFAtoms_nodup : rightFoundOSLFAtoms.Nodup := by
  decide +kernel
private theorem rightFoundOSLFAtoms_supported :
    cSupportedSourceExecFacts rightFoundOSLFAtoms =
      [endpointRightFoundDirective] := by
  rfl
private theorem rightFoundOSLF_selects :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace rightFoundOSLFSource) =
      some endpointRightFoundDirective := by
  exact reflective_selects_of_computable_supported_singleton
    rightFoundOSLFAtoms endpointRightFoundDirective
    rightFoundOSLFAtoms_nodup rightFoundOSLFAtoms_supported

theorem rightFoundCanary_inhabits_target_native_type :
    let target := fireReflectiveSourceExecFact rightFoundOSLFSource
      endpointRightFoundDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies
      rightFoundOSLFSource
      (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected rightFoundOSLF_selects)

theorem leftMissingCanary_emits_inert :
    dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .inert ∈
      cFireReflectiveSourceExecFact [leftMissingObservation]
        endpointLeftMissingDirective := by
  apply terminalCanary_emits_result endpointLeftMissingRule leftMissingSelf
    leftMissingObservationTemplate leftMissingObservation inertTemplate
    (dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .inert)
    endpointLeftMissingDirective leftMissingPatterns (by rfl)
    ((cmatchAtom [] leftMissingSelf endpointLeftMissingRule).getD []) (by rfl)
    ((cmatchAtom
      ((cmatchAtom [] leftMissingSelf endpointLeftMissingRule).getD [])
      leftMissingObservationTemplate leftMissingObservation).getD []) (by rfl)
    (by rfl) (by rfl) (by rfl) (by decide) (by rfl)

theorem rightMissingCanary_emits_inert :
    dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .inert ∈
      cFireReflectiveSourceExecFact [rightMissingObservation]
        endpointRightMissingDirective := by
  apply terminalCanary_emits_result endpointRightMissingRule rightMissingSelf
    rightMissingObservationTemplate rightMissingObservation inertTemplate
    (dvEndpointClassificationAtom fixtureOwner 0 0 fixturePair .inert)
    endpointRightMissingDirective rightMissingPatterns (by rfl)
    ((cmatchAtom [] rightMissingSelf endpointRightMissingRule).getD []) (by rfl)
    ((cmatchAtom
      ((cmatchAtom [] rightMissingSelf endpointRightMissingRule).getD [])
      rightMissingObservationTemplate rightMissingObservation).getD [])
      (by rfl)
    (by rfl) (by rfl) (by rfl) (by decide) (by rfl)

section AxiomAudit

#print axioms decodeDVEndpointClassificationAtom_encoded
#print axioms dvEndpointClassificationRequestAtom_not_proofNeutral
#print axioms extract_endpointStartRule_exact
#print axioms extract_endpointLeftFoundRule_exact
#print axioms extract_endpointLeftMissingRule_exact
#print axioms extract_endpointRightFoundRule_exact
#print axioms extract_endpointRightMissingRule_exact
#print axioms extract_endpointReloadRule_exact
#print axioms endpointRules_extract_exact
#print axioms endpointRuleRow_not_proofNeutral
#print axioms endpointStartDirective_sinks_exact
#print axioms leftFoundCanary_emits_exact_right_lookup
#print axioms rightFoundCanary_emits_live
#print axioms rightFoundCanary_inhabits_target_native_type
#print axioms leftMissingCanary_emits_inert
#print axioms rightMissingCanary_emits_inert

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVEndpointClassification
