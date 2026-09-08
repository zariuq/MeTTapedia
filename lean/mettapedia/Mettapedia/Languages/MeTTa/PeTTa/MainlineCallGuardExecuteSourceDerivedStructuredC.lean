import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Source-derived hot StructuredC body for the completed-call executor

The completed-call executor is a LanguageDef of twenty-one rewrite rules.
This module lowers those rules to StructuredC through the same chain as the
cold compiler: every rule is compiled by the generic first-order rule
compiler into a rule plan; the plan's right-hand side is decoded into one hot
delta with its operand variables and validated by re-encoding; every premise
becomes one decision call; and the per-row bodies are placed in a phase
dispatcher whose binding blocks declare the projections the rows read.

The dispatcher frame is the hot admission: a rule is admitted at one of
twenty-one positions, and a right-hand side that is not one of the seventeen
delta shapes is rejected, never approximated.  `generatedHotBody` is stated
from the explicit row inventory, and `sourceDerived_eq` checks that the
generic chain produces exactly that body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan PremisePlan RulePlan compileRule? compilePattern?)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
  (decodeReason? encodeReason transitions)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics

/-! ## Event plans

The right-hand sides append events to the event log.  Each appended event is
decoded into an event plan over metavariable names. -/

inductive EventPlan where
  | fallback (reason : String)
  | beginPlan (occurrence : String)
  | rejectOccurrence (occurrence : String)
  | installOccurrence (occurrence : String)
  | evaluateCall (occurrence : String)
  | useRawArgument (index : String)
  | evaluateArgument (index : String)
  | queryExactType (index expected : String) (accepted : Bool)
  | queryMetatype (index expected : String) (accepted : Bool)
  | argumentShapeMismatch (index : String)
  | queryResultType (expected : String) (accepted : Bool)
  | queryResultMetatype (expected : String) (accepted : Bool)
deriving DecidableEq, Repr

private def m (name : String) : PatternPlan := .metavariable name

private def app (constructor : String) (arguments : List PatternPlan := []) : PatternPlan :=
  .application constructor arguments

private def mv? : PatternPlan → Option String
  | .metavariable name => some name
  | _ => none

private def flag? : PatternPlan → Option Bool
  | .application "petta-call-guard-hot:true" [] => some true
  | .application "petta-call-guard-hot:false" [] => some false
  | _ => none

private def flagPlan (accepted : Bool) : PatternPlan :=
  app (if accepted then "petta-call-guard-hot:true" else "petta-call-guard-hot:false")

def decodeEvent? : PatternPlan → Option EventPlan
  | .application "petta-call-guard-hot:event-fallback" [.application reason []] =>
      some (.fallback reason)
  | .application "petta-call-guard-hot:event-begin-plan" [occurrence] =>
      (mv? occurrence).map EventPlan.beginPlan
  | .application "petta-call-guard-hot:event-reject-occurrence" [occurrence] =>
      (mv? occurrence).map EventPlan.rejectOccurrence
  | .application "petta-call-guard-hot:event-install-occurrence" [occurrence] =>
      (mv? occurrence).map EventPlan.installOccurrence
  | .application "petta-call-guard-hot:event-evaluate-call" [occurrence] =>
      (mv? occurrence).map EventPlan.evaluateCall
  | .application "petta-call-guard-hot:event-use-raw-argument" [index] =>
      (mv? index).map EventPlan.useRawArgument
  | .application "petta-call-guard-hot:event-evaluate-argument" [index] =>
      (mv? index).map EventPlan.evaluateArgument
  | .application "petta-call-guard-hot:event-query-exact-type" [index, expected, accepted] => do
      pure (.queryExactType (← mv? index) (← mv? expected) (← flag? accepted))
  | .application "petta-call-guard-hot:event-query-metatype" [index, expected, accepted] => do
      pure (.queryMetatype (← mv? index) (← mv? expected) (← flag? accepted))
  | .application "petta-call-guard-hot:event-argument-shape-mismatch" [index] =>
      (mv? index).map EventPlan.argumentShapeMismatch
  | .application "petta-call-guard-hot:event-query-result-type" [expected, accepted] => do
      pure (.queryResultType (← mv? expected) (← flag? accepted))
  | .application "petta-call-guard-hot:event-query-result-metatype" [expected, accepted] => do
      pure (.queryResultMetatype (← mv? expected) (← flag? accepted))
  | _ => none

def EventPlan.encode : EventPlan → PatternPlan
  | .fallback reason => app "petta-call-guard-hot:event-fallback" [app reason]
  | .beginPlan occurrence => app "petta-call-guard-hot:event-begin-plan" [m occurrence]
  | .rejectOccurrence occurrence =>
      app "petta-call-guard-hot:event-reject-occurrence" [m occurrence]
  | .installOccurrence occurrence =>
      app "petta-call-guard-hot:event-install-occurrence" [m occurrence]
  | .evaluateCall occurrence => app "petta-call-guard-hot:event-evaluate-call" [m occurrence]
  | .useRawArgument index => app "petta-call-guard-hot:event-use-raw-argument" [m index]
  | .evaluateArgument index => app "petta-call-guard-hot:event-evaluate-argument" [m index]
  | .queryExactType index expected accepted =>
      app "petta-call-guard-hot:event-query-exact-type" [m index, m expected, flagPlan accepted]
  | .queryMetatype index expected accepted =>
      app "petta-call-guard-hot:event-query-metatype" [m index, m expected, flagPlan accepted]
  | .argumentShapeMismatch index =>
      app "petta-call-guard-hot:event-argument-shape-mismatch" [m index]
  | .queryResultType expected accepted =>
      app "petta-call-guard-hot:event-query-result-type" [m expected, flagPlan accepted]
  | .queryResultMetatype expected accepted =>
      app "petta-call-guard-hot:event-query-result-metatype" [m expected, flagPlan accepted]

/-- Peel a snoc chain: the base plan and the appended events in emission
order. -/
def unsnocFuel : Nat → PatternPlan → PatternPlan × List PatternPlan
  | 0, plan => (plan, [])
  | fuel + 1, .application "petta-call-guard-hot:events-snoc" [events, event] =>
      let peeled := unsnocFuel fuel events
      (peeled.1, peeled.2 ++ [event])
  | _ + 1, plan => (plan, [])

/-- No right-hand side appends more than four events. -/
def unsnoc (plan : PatternPlan) : PatternPlan × List PatternPlan := unsnocFuel 8 plan

/-- Rebuild a snoc chain from its base and its events. -/
def snocs (base : PatternPlan) (events : List EventPlan) : PatternPlan :=
  events.foldl (fun chain event => app "petta-call-guard-hot:events-snoc" [chain, event.encode])
    base

/-- The event log of a right-hand side: either a metavariable base or the
empty log, with the decoded appended events. -/
def decodeEvents? (plan : PatternPlan) : Option (Option String × List EventPlan) := do
  let peeled := unsnoc plan
  let base ← match peeled.1 with
    | .metavariable name => some (some name)
    | .application "petta-call-guard-hot:events-nil" [] => some none
    | _ => none
  let events ← peeled.2.mapM decodeEvent?
  pure (base, events)

private def eventsBase : Option String → PatternPlan
  | some name => m name
  | none => app "petta-call-guard-hot:events-nil"

/-! ## Delta calls -/

/-- One hot delta with its operand variables in ABI order and its closed
trailing operands (already StructuredC expressions). -/
structure DeltaCall where
  delta : Delta
  operands : List String
  closed : List Pattern
deriving DecidableEq, Repr

private def callVars? : PatternPlan → Option (List String)
  | .application "petta-call-guard-hot:call" [function, sources, values, result] => do
      pure [← mv? function, ← mv? sources, ← mv? values, ← mv? result]
  | _ => none

private def declarationVars? : PatternPlan → Option (List String)
  | .application "petta-call-guard:declaration" [occurrence, function, inputs, output] => do
      pure [← mv? occurrence, ← mv? function, ← mv? inputs, ← mv? output]
  | _ => none

private def planVars? : PatternPlan → Option (String × String × String × List String)
  | .application "petta-call-guard-hot:plan" [occurrence, modes, mode, declaration] => do
      pure (← mv? occurrence, ← mv? modes, ← mv? mode, ← declarationVars? declaration)
  | _ => none

/-- The closed reason operand of a fallback delta. -/
def reasonExpression (reason : GuardFallbackReason) : Pattern := symbol (fallbackSymbol reason)

def reasons : List GuardFallbackReason :=
  [.outsideFragment, .foreignOwner, .staleRevision, .wrongHead, .wrongArity]

def decodeReasonExpression? (expression : Pattern) : Option GuardFallbackReason :=
  reasons.find? fun reason => reasonExpression reason = expression

/-- Decode one right-hand side into a delta call.  Every operand must be a
metavariable at its slot and every repeated variable must agree. -/
def decodeDeltaCall? : PatternPlan → Option DeltaCall
  | .application "petta-call-guard-hot:halted"
      [.application "petta-call-guard-hot:observation" [outcome, events]] => do
      let (base, tail) ← decodeEvents? events
      match outcome, base, tail with
      | .application "petta-call-guard-hot:fallback" [.application reason []], none,
          [.fallback reason'] => do
          guard (reason = reason')
          let decoded ← decodeReason? (.apply reason [])
          pure ⟨.recordFallback, [], [reasonExpression decoded]⟩
      | .application "petta-call-guard-hot:executed" [accepted], some events, [] => do
          pure ⟨.finishExecuted, [← mv? accepted, events], []⟩
      | _, _, _ => none
  | .application "petta-call-guard-hot:plans" [snapshot, call, remaining, accepted, events] => do
      let snapshot ← mv? snapshot
      let (base, tail) ← decodeEvents? events
      match remaining, accepted, base, tail with
      | .metavariable plans, .application "petta-call-guard-hot:accepted-nil" [], none, [] => do
          let [function, sources, values, result] ← callVars? call | none
          pure ⟨.beginPlans, [snapshot, function, sources, values, result, plans], []⟩
      | .metavariable remaining, .metavariable accepted, some events, tail =>
          match tail with
          | [.beginPlan occurrence, .rejectOccurrence occurrence'] => do
              let [function, sources, values, result] ← callVars? call | none
              guard (occurrence = occurrence')
              pure ⟨.rejectPlanHead,
                [snapshot, function, sources, values, result, remaining, accepted, events,
                  occurrence], []⟩
          | [.useRawArgument index, .rejectOccurrence occurrence] => do
              let call ← mv? call
              pure ⟨.rejectRaw, [snapshot, call, remaining, accepted, events, occurrence, index], []⟩
          | [.evaluateArgument index, .queryExactType index' expected false,
              .queryMetatype index'' expected' false, .rejectOccurrence occurrence] => do
              let call ← mv? call
              guard (index = index' ∧ index' = index'' ∧ expected = expected')
              pure ⟨.rejectMetatype,
                [snapshot, call, remaining, accepted, events, occurrence, index, expected], []⟩
          | [.argumentShapeMismatch index, .rejectOccurrence occurrence] => do
              let call ← mv? call
              pure ⟨.rejectShape, [snapshot, call, remaining, accepted, events, occurrence, index],
                []⟩
          | [.queryResultType expected false, .queryResultMetatype expected' false,
              .rejectOccurrence occurrence] => do
              let [function, sources, values, result] ← callVars? call | none
              guard (expected = expected')
              pure ⟨.rejectResult,
                [snapshot, function, sources, values, result, remaining, accepted, events,
                  occurrence, expected], []⟩
          | _ => none
      | .metavariable remaining,
          .application "petta-call-guard-hot:accepted-snoc" [.metavariable accepted, declaration],
          some events, tail => do
          let [function, sources, values, result] ← callVars? call | none
          let [declarationOccurrence, declarationFunction, inputs, output] ←
            declarationVars? declaration | none
          let common := [snapshot, function, sources, values, result, remaining, accepted,
            declarationOccurrence, declarationFunction, inputs, output]
          match tail with
          | [.installOccurrence occurrence] =>
              pure ⟨.installUnchecked, common ++ [occurrence, events], []⟩
          | [.queryResultType expected true, .installOccurrence occurrence] =>
              pure ⟨.installExact, common ++ [occurrence, events, expected], []⟩
          | [.queryResultType expected false, .queryResultMetatype expected' true,
              .installOccurrence occurrence] => do
              guard (expected = expected')
              pure ⟨.installMetatype, common ++ [occurrence, events, expected], []⟩
          | _ => none
      | _, _, _, _ => none
  | .application "petta-call-guard-hot:arguments"
      [snapshot, call, plan, remaining, index, modes, sources, values, accepted, events] => do
      let snapshot ← mv? snapshot
      let (occurrence, planModes, resultMode, declaration) ← planVars? plan
      let [declarationOccurrence, declarationFunction, inputs, output] := declaration | none
      let remaining ← mv? remaining
      let modes ← mv? modes
      let sources ← mv? sources
      let values ← mv? values
      let accepted ← mv? accepted
      let (base, tail) ← decodeEvents? events
      let some events := base | none
      match index, tail with
      | .application "petta-call-guard-hot:index-zero" [], [.beginPlan occurrence'] => do
          let [function, sources', values', result] ← callVars? call | none
          guard (occurrence = occurrence' ∧ modes = planModes ∧ sources = sources' ∧
            values = values')
          pure ⟨.beginArguments,
            [snapshot, function, sources, values, result, occurrence, planModes, resultMode,
              declarationOccurrence, declarationFunction, inputs, output, remaining, accepted,
              events], []⟩
      | .application "petta-call-guard-hot:index-succ" [.metavariable index], tail => do
          let call ← mv? call
          let common := [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
            declarationFunction, inputs, output, remaining, index]
          let rest := [modes, sources, values, accepted, events]
          match tail with
          | [.useRawArgument index'] => do
              guard (index = index')
              pure ⟨.advanceRaw, common ++ rest, []⟩
          | [.evaluateArgument index'] => do
              guard (index = index')
              pure ⟨.advanceUnchecked, common ++ rest, []⟩
          | [.evaluateArgument index', .queryExactType index'' expected true] => do
              guard (index = index' ∧ index' = index'')
              pure ⟨.advanceExact, common ++ [expected] ++ rest, []⟩
          | [.evaluateArgument index', .queryExactType index'' expected false,
              .queryMetatype index''' expected' true] => do
              guard (index = index' ∧ index' = index'' ∧ index'' = index''' ∧ expected = expected')
              pure ⟨.advanceMetatype, common ++ [expected] ++ rest, []⟩
          | _ => none
      | _, _ => none
  | .application "petta-call-guard-hot:result"
      [snapshot, call, plan, remaining, accepted, events] => do
      let snapshot ← mv? snapshot
      let call ← mv? call
      let (occurrence, planModes, resultMode, declaration) ← planVars? plan
      let [declarationOccurrence, declarationFunction, inputs, output] := declaration | none
      let remaining ← mv? remaining
      let accepted ← mv? accepted
      let (base, tail) ← decodeEvents? events
      let some events := base | none
      let [.evaluateCall occurrence'] := tail | none
      guard (occurrence = occurrence')
      pure ⟨.evaluateCall,
        [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
          declarationFunction, inputs, output, remaining, accepted, events], []⟩
  | _ => none

private def callPlan (function sources values result : String) : PatternPlan :=
  app "petta-call-guard-hot:call" [m function, m sources, m values, m result]

private def declarationPlan (occurrence function inputs output : String) : PatternPlan :=
  app "petta-call-guard:declaration" [m occurrence, m function, m inputs, m output]

private def planPlan (occurrence modes mode : String) (declaration : PatternPlan) : PatternPlan :=
  app "petta-call-guard-hot:plan" [m occurrence, m modes, m mode, declaration]

private def plansPlan (snapshot call remaining accepted events : PatternPlan) : PatternPlan :=
  app "petta-call-guard-hot:plans" [snapshot, call, remaining, accepted, events]

private def argumentsPlan (snapshot call plan remaining index modes sources values accepted
    events : PatternPlan) : PatternPlan :=
  app "petta-call-guard-hot:arguments"
    [snapshot, call, plan, remaining, index, modes, sources, values, accepted, events]

private def resultPlan (snapshot call plan remaining accepted events : PatternPlan) :
    PatternPlan :=
  app "petta-call-guard-hot:result" [snapshot, call, plan, remaining, accepted, events]

private def haltedPlan (outcome events : PatternPlan) : PatternPlan :=
  app "petta-call-guard-hot:halted" [app "petta-call-guard-hot:observation" [outcome, events]]

/-- Re-encode a delta call as the right-hand side it must have come from. -/
def DeltaCall.encode : DeltaCall → Option PatternPlan
  | ⟨.recordFallback, [], [reason]⟩ => do
      let decoded ← decodeReasonExpression? reason
      let reasonPlan ← compilePattern? (encodeReason decoded)
      pure (haltedPlan (app "petta-call-guard-hot:fallback" [reasonPlan])
        (app "petta-call-guard-hot:events-snoc" [app "petta-call-guard-hot:events-nil",
          app "petta-call-guard-hot:event-fallback" [reasonPlan]]))
  | ⟨.beginPlans, [snapshot, function, sources, values, result, plans], []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m plans)
        (app "petta-call-guard-hot:accepted-nil") (app "petta-call-guard-hot:events-nil"))
  | ⟨.finishExecuted, [accepted, events], []⟩ =>
      some (haltedPlan (app "petta-call-guard-hot:executed" [m accepted]) (m events))
  | ⟨.rejectPlanHead, [snapshot, function, sources, values, result, remaining, accepted, events,
      occurrence], []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m remaining)
        (m accepted)
        (snocs (m events) [.beginPlan occurrence, .rejectOccurrence occurrence]))
  | ⟨.beginArguments, [snapshot, function, sources, values, result, occurrence, planModes,
      resultMode, declarationOccurrence, declarationFunction, inputs, output, remaining, accepted,
      events], []⟩ =>
      some (argumentsPlan (m snapshot) (callPlan function sources values result)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (app "petta-call-guard-hot:index-zero") (m planModes) (m sources)
        (m values) (m accepted) (snocs (m events) [.beginPlan occurrence]))
  | ⟨.evaluateCall, [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
      declarationFunction, inputs, output, remaining, accepted, events], []⟩ =>
      some (resultPlan (m snapshot) (m call)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (m accepted) (snocs (m events) [.evaluateCall occurrence]))
  | ⟨.advanceRaw, [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
      declarationFunction, inputs, output, remaining, index, modes, sources, values, accepted,
      events], []⟩ =>
      some (argumentsPlan (m snapshot) (m call)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (app "petta-call-guard-hot:index-succ" [m index]) (m modes) (m sources)
        (m values) (m accepted) (snocs (m events) [.useRawArgument index]))
  | ⟨.advanceUnchecked, [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
      declarationFunction, inputs, output, remaining, index, modes, sources, values, accepted,
      events], []⟩ =>
      some (argumentsPlan (m snapshot) (m call)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (app "petta-call-guard-hot:index-succ" [m index]) (m modes) (m sources)
        (m values) (m accepted) (snocs (m events) [.evaluateArgument index]))
  | ⟨.advanceExact, [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
      declarationFunction, inputs, output, remaining, index, expected, modes, sources, values,
      accepted, events], []⟩ =>
      some (argumentsPlan (m snapshot) (m call)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (app "petta-call-guard-hot:index-succ" [m index]) (m modes) (m sources)
        (m values) (m accepted)
        (snocs (m events) [.evaluateArgument index, .queryExactType index expected true]))
  | ⟨.advanceMetatype, [snapshot, call, occurrence, planModes, resultMode, declarationOccurrence,
      declarationFunction, inputs, output, remaining, index, expected, modes, sources, values,
      accepted, events], []⟩ =>
      some (argumentsPlan (m snapshot) (m call)
        (planPlan occurrence planModes resultMode
          (declarationPlan declarationOccurrence declarationFunction inputs output))
        (m remaining) (app "petta-call-guard-hot:index-succ" [m index]) (m modes) (m sources)
        (m values) (m accepted)
        (snocs (m events) [.evaluateArgument index, .queryExactType index expected false,
          .queryMetatype index expected true]))
  | ⟨.rejectRaw, [snapshot, call, remaining, accepted, events, occurrence, index], []⟩ =>
      some (plansPlan (m snapshot) (m call) (m remaining) (m accepted)
        (snocs (m events) [.useRawArgument index, .rejectOccurrence occurrence]))
  | ⟨.rejectMetatype, [snapshot, call, remaining, accepted, events, occurrence, index, expected],
      []⟩ =>
      some (plansPlan (m snapshot) (m call) (m remaining) (m accepted)
        (snocs (m events) [.evaluateArgument index, .queryExactType index expected false,
          .queryMetatype index expected false, .rejectOccurrence occurrence]))
  | ⟨.rejectShape, [snapshot, call, remaining, accepted, events, occurrence, index], []⟩ =>
      some (plansPlan (m snapshot) (m call) (m remaining) (m accepted)
        (snocs (m events) [.argumentShapeMismatch index, .rejectOccurrence occurrence]))
  | ⟨.installUnchecked, [snapshot, function, sources, values, result, remaining, accepted,
      declarationOccurrence, declarationFunction, inputs, output, occurrence, events], []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m remaining)
        (app "petta-call-guard-hot:accepted-snoc" [m accepted,
          declarationPlan declarationOccurrence declarationFunction inputs output])
        (snocs (m events) [.installOccurrence occurrence]))
  | ⟨.installExact, [snapshot, function, sources, values, result, remaining, accepted,
      declarationOccurrence, declarationFunction, inputs, output, occurrence, events, expected],
      []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m remaining)
        (app "petta-call-guard-hot:accepted-snoc" [m accepted,
          declarationPlan declarationOccurrence declarationFunction inputs output])
        (snocs (m events) [.queryResultType expected true, .installOccurrence occurrence]))
  | ⟨.installMetatype, [snapshot, function, sources, values, result, remaining, accepted,
      declarationOccurrence, declarationFunction, inputs, output, occurrence, events, expected],
      []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m remaining)
        (app "petta-call-guard-hot:accepted-snoc" [m accepted,
          declarationPlan declarationOccurrence declarationFunction inputs output])
        (snocs (m events) [.queryResultType expected false, .queryResultMetatype expected true,
          .installOccurrence occurrence]))
  | ⟨.rejectResult, [snapshot, function, sources, values, result, remaining, accepted, events,
      occurrence, expected], []⟩ =>
      some (plansPlan (m snapshot) (callPlan function sources values result) (m remaining)
        (m accepted)
        (snocs (m events) [.queryResultType expected false, .queryResultMetatype expected false,
          .rejectOccurrence occurrence]))
  | _ => none

/-- Decode and validate: the decoded call must re-encode to the source
right-hand side. -/
def compileDelta? (plan : PatternPlan) : Option DeltaCall := do
  let call ← decodeDeltaCall? plan
  let recovered ← call.encode
  guard (recovered.erase = plan.erase)
  pure call

/-! ## Lowering to StructuredC -/

/-- C identifier spelling for one authored schema variable. -/
def targetVariable : String → String
  | "familyOwner" => "family_owner"
  | "familyRevision" => "family_revision"
  | "familyHead" => "family_head"
  | "familyArity" => "family_arity"
  | "sourceArguments" => "source_arguments"
  | "evaluatedArguments" => "evaluated_arguments"
  | "planModes" => "plan_modes"
  | "resultMode" => "result_mode"
  | "declarationOccurrence" => "declaration_occurrence"
  | "declarationFunction" => "declaration_function"
  | name => name

def variableExpressions (names : List String) : List Pattern :=
  names.map fun name => variableExpression (targetVariable name)

/-- Operand count of each decision, fixed by its relation. -/
def decisionArity : Decision → Nat
  | .ownerDiffers => 2
  | .revisionStale => 4
  | .headWrong => 6
  | .arityWrong => 8
  | .familyCurrent => 8
  | .planHeadMatches => 2
  | .planHeadDiffers => 2
  | .rawEqual => 2
  | .rawDiffers => 2
  | .exactType => 3
  | .metatypeAccepts => 3
  | .metatypeRejects => 3
  | .shapeMismatched => 3

def decisionOfRelation? (relation : String) : Option Decision :=
  decisions.find? fun decision => decision.relation = relation

/-- Compile one source relation premise to one visible decision call. -/
def lowerPremiseCondition? (premise : PremisePlan) : Option Pattern := do
  let decision ← decisionOfRelation? premise.relation
  guard (premise.arguments.length = decisionArity decision)
  pure (call decision.externalName (variableExpressions premise.arguments))

/-- Wrap a successful action in every authored guard, retaining premise
order. -/
def lowerPremises? : List PremisePlan → Pattern → Option Pattern
  | [], success => some success
  | premise :: premises, success => do
      let condition ← lowerPremiseCondition? premise
      let guardedTail ← lowerPremises? premises success
      pure (statements [ifThenElse condition guardedTail (statements [])])

def advancedOutcome : String := "CETTA_PETTA_CALL_GUARD_HOT_ADVANCED_V1"
def haltedOutcome : String := "CETTA_PETTA_CALL_GUARD_HOT_HALTED_V1"
def noTransitionOutcome : String := "CETTA_PETTA_CALL_GUARD_HOT_NO_TRANSITION_V1"
def terminalOutcome : String := "CETTA_PETTA_CALL_GUARD_HOT_TERMINAL_V1"
def engineFaultOutcome : String := "CETTA_PETTA_CALL_GUARD_HOT_ENGINE_FAULT_V1"

/-- The outcome a delta returns: halting deltas report the halt. -/
def deltaOutcome : Delta → String
  | .recordFallback | .finishExecuted => haltedOutcome
  | _ => advancedOutcome

def stateArgument : List Pattern := [variableExpression "state"]

/-- The statements of one delta call: the update, then the outcome. -/
def deltaStatements (deltaCall : DeltaCall) : Pattern :=
  statements [
    effect (call deltaCall.delta.externalName
      (stateArgument ++ variableExpressions deltaCall.operands ++ deltaCall.closed)),
    returnSymbol (deltaOutcome deltaCall.delta)]

/-- Lower one compiled rule to its row body. -/
def lowerRow? (plan : RulePlan) : Option Pattern := do
  let deltaCall ← compileDelta? plan.right
  lowerPremises? plan.premises (deltaStatements deltaCall)

/-! ## The dispatcher frame -/

def projectionVariable : Projection → String
  | .owner => "owner"
  | .snapshot => "snapshot"
  | .function => "function"
  | .sourceArguments => "source_arguments"
  | .evaluatedArguments => "evaluated_arguments"
  | .result => "result"
  | .familyOwner => "family_owner"
  | .familyRevision => "family_revision"
  | .familyHead => "family_head"
  | .familyArity => "family_arity"
  | .plans => "plans"
  | .call => "call"
  | .remaining => "remaining"
  | .accepted => "accepted"
  | .events => "events"
  | .occurrence => "occurrence"
  | .planModes => "plan_modes"
  | .resultMode => "result_mode"
  | .declarationOccurrence => "declaration_occurrence"
  | .declarationFunction => "declaration_function"
  | .inputs => "inputs"
  | .output => "output"
  | .index => "index"
  | .allModes => "modes"
  | .allSources => "sources"
  | .allValues => "values"
  | .modes => "modes"
  | .source => "source"
  | .sources => "sources"
  | .value => "value"
  | .values => "values"
  | .expected => "expected"

def ownerType : String := "CettaPeTTaCallGuardOwnerV1"
def natType : String := "CettaPeTTaCallGuardNatV1"
def nameType : String := "CettaPeTTaCallGuardNameV1"
def termType : String := "CettaPeTTaCallGuardTermV1"
def termsType : String := "CettaPeTTaCallGuardTermsV1"
def snapshotType : String := "CettaPeTTaCallGuardHotSnapshotV1"
def callType : String := "CettaPeTTaCallGuardHotCallV1"
def plansType : String := "CettaPeTTaCallGuardHotPlansV1"
def modesType : String := "CettaPeTTaCallGuardHotModesV1"
def resultModeType : String := "CettaPeTTaCallGuardHotResultModeV1"
def acceptedType : String := "CettaPeTTaCallGuardHotAcceptedV1"
def eventsType : String := "CettaPeTTaCallGuardHotEventsV1"
def indexType : String := "CettaPeTTaCallGuardHotIndexV1"
def tagType : String := "CettaTagV1"
def boolType : String := "CettaBoolV1"
def unitType : String := "CettaUnitV1"

def projectionType : Projection → String
  | .owner | .familyOwner => ownerType
  | .snapshot => snapshotType
  | .function | .familyHead | .declarationFunction => nameType
  | .sourceArguments | .evaluatedArguments | .inputs | .allSources | .allValues | .sources
  | .values => termsType
  | .result | .output | .source | .value | .expected => termType
  | .familyRevision | .familyArity | .occurrence | .declarationOccurrence => natType
  | .plans | .remaining => plansType
  | .call => callType
  | .accepted => acceptedType
  | .events => eventsType
  | .planModes | .allModes | .modes => modesType
  | .resultMode => resultModeType
  | .index => indexType

/-- One visible declaration binding a projection of the state. -/
def bindProjection (projection : Projection) : Pattern :=
  declare (projectionVariable projection) (namedType (projectionType projection))
    (call projection.externalName stateArgument)

def bindProjections (projections : List Projection) : Pattern :=
  statements (projections.map bindProjection)

def frameQuery (query : FrameQuery) : Pattern := call query.externalName stateArgument

def outcomeBody (outcome : String) : Pattern := statements [returnSymbol outcome]

/-- Splice statement lists at the Lean level so that every branch stays one
flat statement list. -/
def spliceStatements : Pattern → Pattern → Pattern
  | .apply "structured-c:statements-nil" [], continuation => continuation
  | .apply "structured-c:statements-cons" [statement, rest], continuation =>
      node "structured-c:statements-cons" [statement, spliceStatements rest continuation]
  | .apply "structured-c:statements-append" [first, second], continuation =>
      spliceStatements first (spliceStatements second continuation)
  | block, continuation => appendStatements block continuation

def sequence : List Pattern → Pattern
  | [] => statements []
  | one :: rest => spliceStatements one (sequence rest)

/-- The twenty-one row bodies, one per executor rule, in rule order. -/
structure HotRows where
  requestOutsideFragment : Pattern
  requestForeignOwner : Pattern
  requestStaleRevision : Pattern
  requestWrongHead : Pattern
  requestWrongArity : Pattern
  requestCurrent : Pattern
  plansFinished : Pattern
  planHeadMismatch : Pattern
  planHeadMatches : Pattern
  argumentsFinished : Pattern
  rawArgumentAccepted : Pattern
  rawArgumentRejected : Pattern
  uncheckedArgument : Pattern
  checkedArgumentExact : Pattern
  checkedArgumentMetatypeAccepted : Pattern
  checkedArgumentMetatypeRejected : Pattern
  argumentShapeMismatch : Pattern
  uncheckedResult : Pattern
  checkedResultExact : Pattern
  checkedResultMetatypeAccepted : Pattern
  checkedResultMetatypeRejected : Pattern
deriving DecidableEq, Repr

def HotRows.ofList? : List Pattern → Option HotRows
  | [requestOutsideFragment, requestForeignOwner, requestStaleRevision, requestWrongHead,
      requestWrongArity, requestCurrent, plansFinished, planHeadMismatch, planHeadMatches,
      argumentsFinished, rawArgumentAccepted, rawArgumentRejected, uncheckedArgument,
      checkedArgumentExact, checkedArgumentMetatypeAccepted, checkedArgumentMetatypeRejected,
      argumentShapeMismatch, uncheckedResult, checkedResultExact, checkedResultMetatypeAccepted,
      checkedResultMetatypeRejected] =>
      some ⟨requestOutsideFragment, requestForeignOwner, requestStaleRevision, requestWrongHead,
        requestWrongArity, requestCurrent, plansFinished, planHeadMismatch, planHeadMatches,
        argumentsFinished, rawArgumentAccepted, rawArgumentRejected, uncheckedArgument,
        checkedArgumentExact, checkedArgumentMetatypeAccepted, checkedArgumentMetatypeRejected,
        argumentShapeMismatch, uncheckedResult, checkedResultExact,
        checkedResultMetatypeAccepted, checkedResultMetatypeRejected⟩
  | _ => none

/-- Request phase: the call projections, then the outside-fragment row or the
family projections and the five family rows. -/
def requestDispatcher (rows : HotRows) : Pattern :=
  sequence [
    bindProjections [.owner, .snapshot, .function, .sourceArguments, .evaluatedArguments,
      .result],
    statements [ifThenElse (frameQuery .compilationIsOutside)
      rows.requestOutsideFragment
      (sequence [
        bindProjections [.familyOwner, .familyRevision, .familyHead, .familyArity, .plans],
        rows.requestForeignOwner, rows.requestStaleRevision, rows.requestWrongHead,
        rows.requestWrongArity, rows.requestCurrent])],
    outcomeBody noTransitionOutcome]

/-- Plans phase: the finished row when no plan remains, else the head plan's
projections and the two head rows. -/
def plansDispatcher (rows : HotRows) : Pattern :=
  sequence [
    bindProjections [.snapshot, .function, .sourceArguments, .evaluatedArguments, .result,
      .accepted, .events],
    statements [ifThenElse (frameQuery .plansAreEmpty)
      rows.plansFinished
      (sequence [
        bindProjections [.remaining, .occurrence, .planModes, .resultMode,
          .declarationOccurrence, .declarationFunction, .inputs, .output],
        rows.planHeadMismatch, rows.planHeadMatches])],
    outcomeBody noTransitionOutcome]

/-- Arguments phase: the finished row; else the whole argument lists for the
shape-mismatch row; else the tails and heads, shadowing the whole lists, and
the mode-dispatched rows. -/
def argumentsDispatcher (rows : HotRows) : Pattern :=
  sequence [
    bindProjections [.snapshot, .call, .occurrence, .planModes, .resultMode,
      .declarationOccurrence, .declarationFunction, .inputs, .output, .remaining, .index,
      .accepted, .events],
    statements [ifThenElse (frameQuery .argumentsAreFinished)
      rows.argumentsFinished
      (sequence [
        bindProjections [.allModes, .allSources, .allValues],
        statements [ifThenElse (frameQuery .argumentsAreMismatched)
          rows.argumentShapeMismatch
          (sequence [
            bindProjections [.modes, .sources, .values, .source, .value],
            statements [switch (frameQuery .argumentModeTag)
              [ caseBranch (valueSymbol rawModeTag)
                  (sequence [rows.rawArgumentAccepted, rows.rawArgumentRejected])
              , caseBranch (valueSymbol uncheckedModeTag) rows.uncheckedArgument
              , caseBranch (valueSymbol checkedModeTag)
                  (sequence [bindProjections [.expected], rows.checkedArgumentExact,
                    rows.checkedArgumentMetatypeAccepted,
                    rows.checkedArgumentMetatypeRejected]) ]
              (outcomeBody engineFaultOutcome)]])]])],
    outcomeBody noTransitionOutcome]

/-- Result phase: the plan's projections and the result-mode-dispatched rows. -/
def resultDispatcher (rows : HotRows) : Pattern :=
  sequence [
    bindProjections [.snapshot, .function, .sourceArguments, .evaluatedArguments, .result,
      .occurrence, .declarationOccurrence, .declarationFunction, .inputs, .output, .remaining,
      .accepted, .events],
    statements [switch (frameQuery .resultModeTag)
      [ caseBranch (valueSymbol uncheckedResultTag) rows.uncheckedResult
      , caseBranch (valueSymbol checkedResultTag)
          (sequence [bindProjections [.expected], rows.checkedResultExact,
            rows.checkedResultMetatypeAccepted, rows.checkedResultMetatypeRejected]) ]
      (outcomeBody engineFaultOutcome)],
    outcomeBody noTransitionOutcome]

/-- The whole body: a phase switch over the four live phases and the halted
phase. -/
def assembleHotBody (rows : HotRows) : Pattern :=
  statements [switch (frameQuery .phase)
    [ caseBranch (valueSymbol requestPhase) (requestDispatcher rows)
    , caseBranch (valueSymbol plansPhase) (plansDispatcher rows)
    , caseBranch (valueSymbol argumentsPhase) (argumentsDispatcher rows)
    , caseBranch (valueSymbol resultPhase) (resultDispatcher rows)
    , caseBranch (valueSymbol haltedPhase) (outcomeBody terminalOutcome) ]
    (outcomeBody engineFaultOutcome)]

/-! ## The source-derived chain -/

/-- Every executor rule compiled by the generic rule compiler. -/
def rulePlans? : Option (List RulePlan) :=
  MainlineCallGuardExecuteOperational.transitions.mapM compileRule?

def sourceDerivedRows? : Option HotRows := do
  let plans ← rulePlans?
  let bodies ← plans.mapM lowerRow?
  HotRows.ofList? bodies

def sourceDerivedHotBody? : Option Pattern := (sourceDerivedRows?).map assembleHotBody

/-! ## The explicit row inventory -/

/-- One row: its decisions with their operand variables, then its delta. -/
structure RowSpec where
  decisions : List (Decision × List String)
  delta : DeltaCall
deriving DecidableEq, Repr

def guardedBody (decisions : List (Decision × List String)) (success : Pattern) : Pattern :=
  decisions.foldr
    (fun decision inner =>
      statements [ifThenElse (call decision.1.externalName (variableExpressions decision.2))
        inner (statements [])])
    success

def rowBody (spec : RowSpec) : Pattern := guardedBody spec.decisions (deltaStatements spec.delta)

def callVariables : List String :=
  ["function", "sourceArguments", "evaluatedArguments", "result"]

def familyVariables : List String :=
  ["familyOwner", "owner", "familyRevision", "snapshot", "familyHead", "function",
    "familyArity", "sourceArguments"]

def declarationVariables : List String :=
  ["declarationOccurrence", "declarationFunction", "inputs", "output"]

def planVariables : List String :=
  ["occurrence", "planModes", "resultMode"] ++ declarationVariables

def fallbackRow (decisions : List (Decision × List String))
    (reason : GuardFallbackReason) : RowSpec :=
  ⟨decisions, ⟨.recordFallback, [], [reasonExpression reason]⟩⟩

def advanceOperands (expected : List String) : List String :=
  ["snapshot", "call"] ++ planVariables ++ ["remaining", "index"] ++ expected ++
    ["modes", "sources", "values", "accepted", "events"]

def installOperands : List String :=
  ["snapshot"] ++ callVariables ++ ["remaining", "accepted"] ++ declarationVariables ++
    ["occurrence", "events"]

def requestOutsideFragmentRow : RowSpec := fallbackRow [] .outsideFragment
def requestForeignOwnerRow : RowSpec :=
  fallbackRow [(.ownerDiffers, familyVariables.take 2)] .foreignOwner
def requestStaleRevisionRow : RowSpec :=
  fallbackRow [(.revisionStale, familyVariables.take 4)] .staleRevision
def requestWrongHeadRow : RowSpec :=
  fallbackRow [(.headWrong, familyVariables.take 6)] .wrongHead
def requestWrongArityRow : RowSpec :=
  fallbackRow [(.arityWrong, familyVariables)] .wrongArity
def requestCurrentRow : RowSpec :=
  ⟨[(.familyCurrent, familyVariables)],
    ⟨.beginPlans, ["snapshot"] ++ callVariables ++ ["plans"], []⟩⟩
def plansFinishedRow : RowSpec := ⟨[], ⟨.finishExecuted, ["accepted", "events"], []⟩⟩
def planHeadMismatchRow : RowSpec :=
  ⟨[(.planHeadDiffers, ["declarationFunction", "function"])],
    ⟨.rejectPlanHead,
      ["snapshot"] ++ callVariables ++ ["remaining", "accepted", "events", "occurrence"], []⟩⟩
def planHeadMatchesRow : RowSpec :=
  ⟨[(.planHeadMatches, ["declarationFunction", "function"])],
    ⟨.beginArguments,
      ["snapshot"] ++ callVariables ++ planVariables ++ ["remaining", "accepted", "events"],
      []⟩⟩
def argumentsFinishedRow : RowSpec :=
  ⟨[], ⟨.evaluateCall,
    ["snapshot", "call"] ++ planVariables ++ ["remaining", "accepted", "events"], []⟩⟩
def rawArgumentAcceptedRow : RowSpec :=
  ⟨[(.rawEqual, ["source", "value"])], ⟨.advanceRaw, advanceOperands [], []⟩⟩
def rawArgumentRejectedRow : RowSpec :=
  ⟨[(.rawDiffers, ["source", "value"])],
    ⟨.rejectRaw, ["snapshot", "call", "remaining", "accepted", "events", "occurrence", "index"],
      []⟩⟩
def uncheckedArgumentRow : RowSpec := ⟨[], ⟨.advanceUnchecked, advanceOperands [], []⟩⟩
def checkedArgumentExactRow : RowSpec :=
  ⟨[(.exactType, ["snapshot", "value", "expected"])],
    ⟨.advanceExact, advanceOperands ["expected"], []⟩⟩
def checkedArgumentMetatypeAcceptedRow : RowSpec :=
  ⟨[(.metatypeAccepts, ["snapshot", "value", "expected"])],
    ⟨.advanceMetatype, advanceOperands ["expected"], []⟩⟩
def checkedArgumentMetatypeRejectedRow : RowSpec :=
  ⟨[(.metatypeRejects, ["snapshot", "value", "expected"])],
    ⟨.rejectMetatype,
      ["snapshot", "call", "remaining", "accepted", "events", "occurrence", "index", "expected"],
      []⟩⟩
def argumentShapeMismatchRow : RowSpec :=
  ⟨[(.shapeMismatched, ["modes", "sources", "values"])],
    ⟨.rejectShape, ["snapshot", "call", "remaining", "accepted", "events", "occurrence", "index"],
      []⟩⟩
def uncheckedResultRow : RowSpec := ⟨[], ⟨.installUnchecked, installOperands, []⟩⟩
def checkedResultExactRow : RowSpec :=
  ⟨[(.exactType, ["snapshot", "result", "expected"])],
    ⟨.installExact, installOperands ++ ["expected"], []⟩⟩
def checkedResultMetatypeAcceptedRow : RowSpec :=
  ⟨[(.metatypeAccepts, ["snapshot", "result", "expected"])],
    ⟨.installMetatype, installOperands ++ ["expected"], []⟩⟩
def checkedResultMetatypeRejectedRow : RowSpec :=
  ⟨[(.metatypeRejects, ["snapshot", "result", "expected"])],
    ⟨.rejectResult,
      ["snapshot"] ++ callVariables ++ ["remaining", "accepted", "events", "occurrence",
        "expected"], []⟩⟩

/-- The inventory: the twenty-one rows in rule order. -/
def rowSpecs : List RowSpec := [
  requestOutsideFragmentRow, requestForeignOwnerRow, requestStaleRevisionRow,
  requestWrongHeadRow, requestWrongArityRow, requestCurrentRow, plansFinishedRow,
  planHeadMismatchRow, planHeadMatchesRow, argumentsFinishedRow, rawArgumentAcceptedRow,
  rawArgumentRejectedRow, uncheckedArgumentRow, checkedArgumentExactRow,
  checkedArgumentMetatypeAcceptedRow, checkedArgumentMetatypeRejectedRow,
  argumentShapeMismatchRow, uncheckedResultRow, checkedResultExactRow,
  checkedResultMetatypeAcceptedRow, checkedResultMetatypeRejectedRow]

def generatedRows : HotRows := {
  requestOutsideFragment := rowBody requestOutsideFragmentRow
  requestForeignOwner := rowBody requestForeignOwnerRow
  requestStaleRevision := rowBody requestStaleRevisionRow
  requestWrongHead := rowBody requestWrongHeadRow
  requestWrongArity := rowBody requestWrongArityRow
  requestCurrent := rowBody requestCurrentRow
  plansFinished := rowBody plansFinishedRow
  planHeadMismatch := rowBody planHeadMismatchRow
  planHeadMatches := rowBody planHeadMatchesRow
  argumentsFinished := rowBody argumentsFinishedRow
  rawArgumentAccepted := rowBody rawArgumentAcceptedRow
  rawArgumentRejected := rowBody rawArgumentRejectedRow
  uncheckedArgument := rowBody uncheckedArgumentRow
  checkedArgumentExact := rowBody checkedArgumentExactRow
  checkedArgumentMetatypeAccepted := rowBody checkedArgumentMetatypeAcceptedRow
  checkedArgumentMetatypeRejected := rowBody checkedArgumentMetatypeRejectedRow
  argumentShapeMismatch := rowBody argumentShapeMismatchRow
  uncheckedResult := rowBody uncheckedResultRow
  checkedResultExact := rowBody checkedResultExactRow
  checkedResultMetatypeAccepted := rowBody checkedResultMetatypeAcceptedRow
  checkedResultMetatypeRejected := rowBody checkedResultMetatypeRejectedRow }

/-- The generated hot body, stated from the inventory. -/
def generatedHotBody : Pattern := assembleHotBody generatedRows

/-- The inventory is in rule order. -/
theorem generatedRows_ofList : HotRows.ofList? (rowSpecs.map rowBody) = some generatedRows := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The generic source-derived chain produces exactly the inventory body. -/
theorem sourceDerived_eq : sourceDerivedHotBody? = some generatedHotBody := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC
