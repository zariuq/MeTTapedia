import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.Primitives
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution

/-! Native execution of original general-premise codecs, checkers, and administrative operations. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

attribute [local simp]
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution.schedulerExpansionTerm
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution.schedulerStateTerm

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)
open CettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open GeneralPremise (Environment)
open GeneralPremise.Execution (Goal Result StepCall Continuation Task Obligation)
open scoped ProgramQuotation

private def preparedSource : Program := RuleExecutionProgram.premiseAssignmentProgram

private def preparedMachine : Program := RuleExecutionProgram.premiseAdministrationProgram

private def preparedEnvironment : Program := RuleExecutionProgram.premiseEnvironmentProgram

private def preparedGround : Program := RuleExecutionProgram.premiseGroundProgram

private def preparedProgram : Program :=
  ((preparedSource.append preparedMachine).append preparedEnvironment).append preparedGround

def Base.runtime : Program := RuleExecutionProgram.program.append preparedProgram

def Base.previousHeads (head : String) : Bool :=
  head != "eval" && head != "gslt:premise:type-context-lookup" && head != "gslt:premise:check-assignment" &&
  head != "gslt:premise:context-next" && head != "gslt:premise:context-quantified" &&
  head != "gslt:premise:machine-deliver" && head != "gslt:premise:machine-evaluate" &&
  head != "gslt:premise:machine-expand" && head != "gslt:premise:constructor-declarations" &&
  head != "gslt:premise:source-type" && head != "gslt:premise:specification" &&
  head != "gslt:premise:signature-candidates" && head != "gslt:premise:signature" &&
  head != "gslt:premise:check-values" && head != "gslt:premise:check-row" &&
  head != "gslt:premise:ground-at" && head != "gslt:premise:ground-list-at"

private theorem retained_closed : ProgramClosed Base.previousHeads RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !Base.previousHeads equation.head || codeWithin Base.previousHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem retained_agreement : ProgramAgreementOn Base.previousHeads RuleExecutionProgram.program Base.runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : preparedProgram.equations.all (fun equation => !Base.previousHeads equation.head) = true := by
      decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : Base.previousHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : preparedProgram.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !Base.previousHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : Base.previousHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem Base.previous_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin Base.previousHeads code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns Base.runtime caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

abbrev Base.a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
abbrev Base.v (name : String) : Atom := .var name
abbrev Base.encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev Base.stringValue (name : String) : Atom := Base.encoded (.string name)
abbrev Base.typeValue (type : TypeExpr) : Atom := Base.encoded (InferenceCettaWire.AuthoredRule.typeTerm type)
abbrev Base.typesValue (types : List (String × TypeExpr)) : Atom :=
  Base.encoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm types)
abbrev Base.typeOptionValue (result : Option TypeExpr) : Atom :=
  Base.encoded (encodeOption InferenceCettaWire.AuthoredRule.typeTerm result)

private inductive Helper where | typeLookup | assignment | next | quantified | deliver | evaluate | expand
private def Helper.head : Helper → String
  | .typeLookup => "gslt:premise:type-context-lookup"
  | .assignment => "gslt:premise:check-assignment"
  | .next => "gslt:premise:context-next"
  | .quantified => "gslt:premise:context-quantified"
  | .deliver => "gslt:premise:machine-deliver"
  | .evaluate => "gslt:premise:machine-evaluate"
  | .expand => "gslt:premise:machine-expand"
private def Helper.names : Helper → List String
  | .typeLookup => ["name", "context"]
  | .assignment => ["declarations", "free", "bound", "rule", "spec", "assignment"]
  | .next | .quantified => ["context"]
  | .deliver => ["result", "continuation"]
  | .evaluate => ["declarations", "free", "goal", "continuation"]
  | .expand => ["declarations", "free", "task"]
def Base.equations (head : String) : List SpaceSemantics.Equation :=
  Base.runtime.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (Base.equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses Base.runtime helper.head values =
      [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause Base.runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw Base.runtime helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns Base.runtime (environment helper values) state (equation helper).body state answer) :
    PureReturns Base.runtime caller state (Base.a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return Base.runtime caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns Base.runtime [] state (Base.a helper.head values) state answer) :
    PureReturns Base.runtime caller state (Base.a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns Base.runtime [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

theorem Base.captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

theorem Base.bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns Base.runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns Base.runtime caller state (if value then yes else no) state answer) :
    PureReturns Base.runtime caller state (Base.a "if" [condition, yes, no]) state answer := by
  apply if_returns Base.runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem Base.branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns Base.runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns Base.runtime selected state body state answer) :
    PureReturns Base.runtime caller state
      (Base.a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns Base.runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem some_type_returns (caller : Subst) (state : State) (name : String) (type : TypeExpr)
    (read : applySubst caller (Base.v name) = Base.typeValue type) :
    PureReturns Base.runtime caller state (Base.a "Some" [Base.v name]) state (Base.typeOptionValue (some type)) := by
  have returned := PureData.template_return Base.runtime caller state (Base.a "Some" [Base.v name])
    (.constructor "Some" [Base.v name] (by decide +kernel) (by decide)
      (by intro value member; simp only [List.mem_singleton] at member; subst value; exact .captured name))
  have substituted : applySubst caller (Base.a "Some" [Base.v name]) = Base.a "Some" [Base.typeValue type] := by
    simpa only [Base.a, applySubst, applySubst.applySubstList] using
      congrArg (fun value => Base.a "Some" [value]) read
  simpa only [substituted, Base.a, Base.typeOptionValue, encodeOption,
    CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned

private def lookupCons : Atom :=
  Base.a "if" [Base.a "==" [Base.v "declared", Base.v "name"], Base.a "Some" [Base.v "type"],
    Base.a Helper.typeLookup.head [Base.v "name", Base.v "rest"]]
private def lookupCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
   (Base.a "LCons" [Base.a "TypeBinding" [Base.v "declared", Base.v "type"], Base.v "rest"], lookupCons),
   (Base.v "bad", .symbol "None")]
private theorem lookup_shape : (equation .typeLookup).body =
    Base.a "case" [Base.v "context", .expression (lookupCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem type_context_lookup_returns (state : State) (name : String) (context : List (String × TypeExpr)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:type-context-lookup" [Base.stringValue name, Base.typesValue context]) state
      (Base.typeOptionValue (List.lookup name context)) := by
  induction context with
  | nil =>
      let caller := environment .typeLookup [Base.stringValue name, Base.typesValue []]
      apply helper_call .typeLookup [] state _ _ _ rfl (Base.captured_closed _)
      rw [lookup_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") lookupCases (.symbol "None") _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup, Base.typesValue,
          InferenceCettaWire.encodeList, CettaWireAtom.encode] using variable_returns Base.runtime caller state "context"
      · simp [lookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns Base.runtime caller state "None"
  | cons entry rest ih =>
      rcases entry with ⟨declared, type⟩
      let caller := environment .typeLookup [Base.stringValue name, Base.typesValue ((declared, type) :: rest)]
      let selected := ("rest", Base.typesValue rest) :: ("type", Base.typeValue type) :: ("declared", Base.stringValue declared) :: caller
      apply helper_call .typeLookup [] state _ _ _ rfl (Base.captured_closed _)
      rw [lookup_shape]
      apply Base.branch_returns caller selected state _ (Base.typesValue ((declared, type) :: rest)) lookupCases lookupCons _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns Base.runtime caller state "context"
      · simp [lookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment, Helper.names,
          Base.typesValue, Base.typeValue, Base.stringValue, InferenceCettaWire.encodeList,
          InferenceCettaWire.AuthoredRule.typeBindingTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have tested := CettaWireAtom.equality_captured_returns Base.runtime selected state
          (.string declared) (.string name) "declared" "name"
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        have wireEqual : Term.string declared = Term.string name ↔ declared = name := by simp
        have equal : PureReturns Base.runtime selected state (Base.a "==" [Base.v "declared", Base.v "name"]) state
            (Effects.boolean (decide (declared = name))) := by simpa only [wireEqual] using tested
        change PureReturns Base.runtime selected state lookupCons state _
        apply Base.bool_if_returns selected state _ _ _ _ _ equal
        by_cases same : declared = name
        · subst declared
          simp only [decide_true, ↓reduceIte, List.lookup_cons, beq_self_eq_true]
          exact some_type_returns selected state "type" type (by
            simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · simp only [same, decide_false]
          have lookup : List.lookup name ((declared, type) :: rest) = List.lookup name rest := by
            cases compared : name == declared with
            | false => simp only [List.lookup_cons, compared]
            | true => exact False.elim (same (beq_iff_eq.mp compared).symm)
          rw [lookup]
          exact helper_capture .typeLookup selected state [Base.v "name", Base.v "rest"]
            [Base.stringValue name, Base.typesValue rest] _ rfl
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih

theorem type_context_lookup_captured_returns (caller : Subst) (state : State)
    (name : String) (context : List (String × TypeExpr)) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [Base.stringValue name, Base.typesValue context]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:type-context-lookup" [one, two]) state
      (Base.typeOptionValue (List.lookup name context)) :=
  helper_capture .typeLookup caller state _ _ _ rfl captured (type_context_lookup_returns state name context)

theorem type_context_lookup_completed_iff (state after : State) (name : String)
    (context : List (String × TypeExpr)) (answers input output : List Atom) :
    (∃ fuel, run Base.runtime fuel {state, control := .evaluate [] (Base.a "gslt:premise:type-context-lookup" [Base.stringValue name, Base.typesValue context])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [Base.typeOptionValue (List.lookup name context)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff Base.runtime [] state state _ _
    (type_context_lookup_returns state name context) after answers input output

theorem type_context_lookup_derivation_iff (state after : State) (name : String)
    (context : List (String × TypeExpr)) (answers input output : List Atom) :
    DeclarativeSpec.Runs Base.runtime {state, control := .evaluate [] (Base.a "gslt:premise:type-context-lookup" [Base.stringValue name, Base.typesValue context])}
      (.complete after answers input output) ↔
      after = state ∧ answers = [Base.typeOptionValue (List.lookup name context)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff Base.runtime [] state state _ _
    (type_context_lookup_returns state name context) after answers input output

#print axioms type_context_lookup_returns
#print axioms type_context_lookup_captured_returns
#print axioms type_context_lookup_completed_iff
#print axioms type_context_lookup_derivation_iff


abbrev Base.typesTerm (types : List TypeExpr) : Term :=
  encodeList InferenceCettaWire.AuthoredRule.typeTerm types
abbrev Base.patternsTerm (patterns : List Pattern) : Term := InferenceCettaWire.encodePatterns patterns
private abbrev assignmentTerm (assignment : Assignment) : Term :=
  RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment
private abbrev naturalsTerm (indices : List Nat) : Term := encodeList Term.natural indices

def contextTerm (context : GeneralPremise.Context) : Term :=
  .application "PremiseContext" [.natural context.ruleIndex,
    InferenceCettaWire.AuthoredRule.rewriteTerm context.rule,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm context.spec, Base.typesTerm context.bound,
    .natural context.premiseIndex, .natural context.quantifierDepth]

private def readNatural? : Term → Option Nat
  | .natural value => some value
  | _ => none

def decodeContext? : Term → Option GeneralPremise.Context
  | .application "PremiseContext" [ruleIndex, rule, spec, bound, premiseIndex, quantifierDepth] => do
      pure ⟨← readNatural? ruleIndex, ← InferenceCettaWire.AuthoredRule.decodeRewrite? rule,
        ← InferenceCettaWire.AuthoredRule.decodeBindingSpec? spec,
        ← InferenceCettaWire.decodeList InferenceCettaWire.AuthoredRule.decodeType? bound,
        ← readNatural? premiseIndex, ← readNatural? quantifierDepth⟩
  | _ => none

@[simp] theorem decodeContext?_contextTerm (context : GeneralPremise.Context) :
    decodeContext? (contextTerm context) = some context := by
  have decoded (types : List TypeExpr) :
      InferenceCettaWire.decodeList InferenceCettaWire.AuthoredRule.decodeType?
        (Base.typesTerm types) = some types :=
    InferenceCettaWire.decodeList_encodeList _ _
      InferenceCettaWire.AuthoredRule.decodeType?_typeTerm types
  cases context
  simp [contextTerm, decodeContext?, readNatural?, decoded]

def goalTerm : Goal → Term
  | .premise context premise initial => .application "PremiseGoal"
      [contextTerm context, InferenceCettaWire.AuthoredRule.premiseTerm premise, assignmentTerm initial]
  | .premises context premises initial => .application "PremisesGoal"
      [contextTerm context, encodeList InferenceCettaWire.AuthoredRule.premiseTerm premises, assignmentTerm initial]
  | .quantified context parameter body index elements initial => .application "QuantifiedGoal"
      [contextTerm context, .string parameter, InferenceCettaWire.AuthoredRule.premiseTerm body,
        .natural index, Base.patternsTerm elements, assignmentTerm initial]
  | .root bound type source index => .application "RootGoal"
      [Base.typesTerm bound, InferenceCettaWire.AuthoredRule.typeTerm type,
        InferenceCettaWire.encodePattern source, .natural index]
  | .steps bound type source limit => .application "StepsGoal"
      [Base.typesTerm bound, InferenceCettaWire.AuthoredRule.typeTerm type,
        InferenceCettaWire.encodePattern source, .natural limit]

abbrev bagChoiceTerm := RuleInstantiationExecution.GeneralExecution.bagChoiceTerm

abbrev traceTerm := RuleInstantiationExecution.GeneralExecution.traceTerm

def originsTerm (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) : Term :=
  encodeList (fun origin => .application "ArgumentOrigin" [.natural origin.1, traceTerm origin.2]) origins

mutual
def eventTerm : GeneralPremise.Event → Term
  | .query index quantifiers row origins => .application "PremiseQueryEvent"
      [.natural index, .natural quantifiers, .natural row, originsTerm origins]
  | .freshness index quantifiers atom subject => .application "PremiseFreshnessEvent"
      [.natural index, .natural quantifiers, .string atom, InferenceCettaWire.encodePattern subject]
  | .quantified index quantifiers kind elements => .application "PremiseQuantifiedEvent"
      [.natural index, .natural quantifiers, InferenceCettaWire.encodeCollectionType kind,
        quantifiedEventsTerm elements]
  | .child index quantifiers declaration bound source target trace targetTrace captured completed history =>
      .application "PremiseChildEvent" [.natural index, .natural quantifiers, .natural declaration,
        Base.typesTerm bound, InferenceCettaWire.encodePattern source, InferenceCettaWire.encodePattern target,
        traceTerm trace, traceTerm targetTrace, assignmentTerm captured, assignmentTerm completed,
        eventsTerm history]
termination_by event => sizeOf event

def eventsTerm : List GeneralPremise.Event → Term
  | [] => .symbol "LNil"
  | event :: events => .application "LCons" [eventTerm event, eventsTerm events]
termination_by events => sizeOf events

def quantifiedEventsTerm : List (Nat × Pattern × List GeneralPremise.Event) → Term
  | [] => .symbol "LNil"
  | (index, element, history) :: rest => .application "LCons"
      [.application "QuantifiedElement" [.natural index, InferenceCettaWire.encodePattern element,
        eventsTerm history], quantifiedEventsTerm rest]
termination_by elements => sizeOf elements
end

def resultTerm {environment : Environment} {goal : Goal} (result : Result environment goal) : Term :=
  .application "PremiseResult" [goalTerm goal, match result with
    | .premise assignment event _ => .application "PremiseAnswer" [assignmentTerm assignment, eventTerm event]
    | .premises assignment events _ => .application "PremisesAnswer" [assignmentTerm assignment, eventsTerm events]
    | .quantified assignment events _ => .application "QuantifiedAnswer" [assignmentTerm assignment, quantifiedEventsTerm events]
    | .root trace captured completed events target _ => .application "RootAnswer"
        [traceTerm trace, assignmentTerm captured, assignmentTerm completed, eventsTerm events,
          InferenceCettaWire.encodePattern target]
    | .steps index trace captured completed events target _ _ => .application "StepsAnswer"
        [.natural index, traceTerm trace, assignmentTerm captured, assignmentTerm completed, eventsTerm events,
          InferenceCettaWire.encodePattern target]]

def stepCallTerm {environment : Environment} (call : StepCall environment) : Term :=
  .application "PremiseStepCall" [contextTerm call.context, InferenceCettaWire.AuthoredRule.premiseTerm call.premise,
    assignmentTerm call.initial, Base.typesTerm call.binders, InferenceCettaWire.AuthoredRule.typeTerm call.type,
    InferenceCettaWire.encodePattern call.source, InferenceCettaWire.encodePattern call.targetSchema]

def continuationTerm {environment : Environment} {goal outer : Goal} :
    Continuation environment goal outer → Term
  | .done goal => .application "PremiseDone" [goalTerm goal]
  | .nextPremise context premise premises initial tail => .application "PremiseNext"
      [contextTerm context, InferenceCettaWire.AuthoredRule.premiseTerm premise,
        encodeList InferenceCettaWire.AuthoredRule.premiseTerm premises, assignmentTerm initial,
        continuationTerm tail]
  | .prepend context premise premises initial middle event _ tail => .application "PremisePrepend"
      [contextTerm context, InferenceCettaWire.AuthoredRule.premiseTerm premise,
        encodeList InferenceCettaWire.AuthoredRule.premiseTerm premises, assignmentTerm initial,
        assignmentTerm middle, eventTerm event, continuationTerm tail]
  | .quantifier context collection parameter body initial kind elements _ tail =>
      .application "PremiseQuantifier" [contextTerm context, .string collection, .string parameter,
        InferenceCettaWire.AuthoredRule.premiseTerm body, assignmentTerm initial,
        InferenceCettaWire.encodeCollectionType kind, Base.patternsTerm elements, continuationTerm tail]
  | .element context parameter body index element elements initial _ tail => .application "PremiseElement"
      [contextTerm context, .string parameter, InferenceCettaWire.AuthoredRule.premiseTerm body,
        .natural index, InferenceCettaWire.encodePattern element, Base.patternsTerm elements,
        assignmentTerm initial, continuationTerm tail]
  | .prependElement context parameter body index element elements initial middle event _ _ tail =>
      .application "PremisePrependElement" [contextTerm context, .string parameter,
        InferenceCettaWire.AuthoredRule.premiseTerm body, .natural index,
        InferenceCettaWire.encodePattern element, Base.patternsTerm elements, assignmentTerm initial,
        assignmentTerm middle, eventTerm event, continuationTerm tail]
  | .rootBody bound type source index rule spec _ _ _ _ trace captured _ _ tail =>
      .application "PremiseRootBody" [Base.typesTerm bound, InferenceCettaWire.AuthoredRule.typeTerm type,
        InferenceCettaWire.encodePattern source, .natural index, InferenceCettaWire.AuthoredRule.rewriteTerm rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, traceTerm trace, assignmentTerm captured,
        continuationTerm tail]
  | .searchedRoot bound type source index limit _ tail => .application "PremiseSearchedRoot"
      [Base.typesTerm bound, InferenceCettaWire.AuthoredRule.typeTerm type, InferenceCettaWire.encodePattern source,
        .natural index, .natural limit, continuationTerm tail]
  | .stepped call tail => .application "PremiseStepped" [stepCallTerm call, continuationTerm tail]

abbrev matcherRequestTerm := RuleInstantiationExecution.GeneralExecution.matcherRequestTerm

abbrev matcherTaskTerm := RuleInstantiationExecution.GeneralExecution.matcherTaskTerm

abbrev matcherStateTerm := RuleInstantiationExecution.GeneralExecution.matcherStateTerm

def modeTerm : RelationArgMode → Term
  | .input => .symbol "RelationInput"
  | .output => .symbol "RelationOutput"

def signatureTerm (signature : GeneralPremise.Signature) : Term :=
  .application "PremiseSignature" [.string signature.relation, Base.typesTerm signature.argumentTypes,
    encodeList modeTerm signature.modes]

def queryRequestTerm (request : GeneralPremise.Query.Request) : Term :=
  .application "PremiseQueryRequest" [contextTerm request.context, .string request.relation,
    Base.patternsTerm request.arguments, assignmentTerm request.initial]

def queryTaskTerm {environment : Environment} {request : GeneralPremise.Query.Request} :
    GeneralPremise.Query.Task environment request → Term
  | .start => .symbol "PremiseQueryStart"
  | .rows frame => .application "PremiseQueryRows" [signatureTerm frame.signature, .natural frame.cursor]
  | .dynamicInputs frame => .application "PremiseQueryDynamicInputs"
      [signatureTerm frame.signature, .natural frame.index,
        Base.patternsTerm frame.schemas, encodeList modeTerm frame.modes,
        Base.patternsTerm frame.resolvedRev]
  | .dynamicRows frame => .application "PremiseQueryDynamicRows"
      [signatureTerm frame.signature, Base.patternsTerm frame.resolved,
        encodeList Base.patternsTerm frame.rows, .natural frame.cursor]
  | .arguments frame => .application "PremiseQueryArguments"
      [.natural frame.rowIndex, .natural frame.index, assignmentTerm frame.assignment,
        Base.patternsTerm frame.schemas, Base.patternsTerm frame.values, encodeList modeTerm frame.modes,
        originsTerm frame.origins]
  | .matcher frame => .application "PremiseQueryMatcher"
      [.natural frame.rowIndex, .natural frame.argumentIndex, Base.patternsTerm frame.schemas,
        Base.patternsTerm frame.values, encodeList modeTerm frame.modes, originsTerm frame.origins,
        matcherRequestTerm frame.query, matcherStateTerm frame.state, .natural frame.cursor]

def queryObligationTerm : GeneralPremise.Query.Obligation → Term
  | .signatureUnavailable relation arity => .application "PremiseSignatureUnavailable" [.string relation, .natural arity]
  | .inputUnavailable row argument => .application "PremiseInputUnavailable" [.natural row, .natural argument]
  | .argumentShape row argument => .application "PremiseArgumentShape" [.natural row, .natural argument]
  | .dynamicInputUnavailable argument => .application "PremiseDynamicInputUnavailable" [.natural argument]
  | .dynamicArgumentShape argument => .application "PremiseDynamicArgumentShape" [.natural argument]
  | .dynamicUnavailable relation => .application "PremiseDynamicUnavailable" [.string relation]

namespace QueryExecution

def queryAnswerTerm {environment : Environment} {request : GeneralPremise.Query.Request}
    (answer : GeneralPremise.Query.Answer environment request) : Term :=
  .application "PremiseQueryAnswer" [.natural answer.rowIndex,
    RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm answer.assignment, originsTerm answer.origins]

end QueryExecution

def queryStateTerm {environment : Environment} {request : GeneralPremise.Query.Request}
    (state : GeneralPremise.Query.State environment request) : Term :=
  PremiseSchedulerExecution.schedulerStateTerm queryTaskTerm QueryExecution.queryAnswerTerm queryObligationTerm state

def taskTerm {environment : Environment} {outer : Goal} : Task environment outer → Term
  | .evaluate goal tail => .application "PremiseEvaluate" [goalTerm goal, continuationTerm tail]
  | .deliver result tail => .application "PremiseDeliver" [resultTerm result, continuationTerm tail]
  | .query request state cursor tail => .application "PremiseQuery"
      [queryRequestTerm request, queryStateTerm state, .natural cursor, continuationTerm tail]
  | .rootMatch frame => .application "PremiseRootMatch"
      [Base.typesTerm frame.bound, InferenceCettaWire.AuthoredRule.typeTerm frame.type,
        InferenceCettaWire.encodePattern frame.source, .natural frame.index,
        InferenceCettaWire.AuthoredRule.rewriteTerm frame.rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm frame.spec, matcherStateTerm frame.state,
        .natural frame.cursor, continuationTerm frame.tail]
  | .targetMatch frame => .application "PremiseTargetMatch" [stepCallTerm frame.call, .natural frame.index,
      traceTerm frame.trace, assignmentTerm frame.captured, assignmentTerm frame.completed,
      eventsTerm frame.history, InferenceCettaWire.encodePattern frame.target, matcherStateTerm frame.state,
      .natural frame.cursor, continuationTerm frame.tail]
  | .scanChildren bound type source limit cursor tail => .application "PremiseScanChildren"
      [Base.typesTerm bound, InferenceCettaWire.AuthoredRule.typeTerm type, InferenceCettaWire.encodePattern source,
        .natural limit, .natural cursor, continuationTerm tail]

def obligationTerm : Obligation → Term
  | .query reason => .application "PremiseQueryObligation" [queryObligationTerm reason]
  | .freshnessProjection index quantifiers => .application "PremiseFreshnessProjection" [.natural index, .natural quantifiers]
  | .collectionProjection index quantifiers collection => .application "PremiseCollectionProjection"
      [.natural index, .natural quantifiers, .string collection]
  | .quantifiedAssignment index quantifiers element => .application "PremiseQuantifiedAssignment"
      [.natural index, .natural quantifiers, .natural element]
  | .stepProjection index quantifiers => .application "PremiseStepProjection" [.natural index, .natural quantifiers]
  | .stepSort index quantifiers => .application "PremiseStepSort" [.natural index, .natural quantifiers]
  | .ruleUnavailable index => .application "PremiseRuleUnavailable" [.natural index]
  | .bindingUnavailable index => .application "PremiseBindingUnavailable" [.natural index]
  | .bindingRejected index => .application "PremiseBindingRejected" [.natural index]
  | .sourceRejected index => .application "PremiseSourceRejected" [.natural index]
  | .targetProjection index => .application "PremiseTargetProjection" [.natural index]

def expansionTerm {environment : Environment} {outer : Goal}
    (expansion : GeneralPremise.Scheduler.Expansion (Task environment outer) (Result environment outer) Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm taskTerm resultTerm obligationTerm expansion

def stateTerm {environment : Environment} {outer : Goal} (state : GeneralPremise.Execution.State environment outer) : Term :=
  PremiseSchedulerExecution.schedulerStateTerm taskTerm resultTerm obligationTerm state



abbrev Base.number (value : Nat) : Atom := Base.encoded (.natural value)
private abbrev contextValue (context : GeneralPremise.Context) : Atom := Base.encoded (contextTerm context)
private abbrev goalValue (goal : Goal) : Atom := Base.encoded (goalTerm goal)
private abbrev continuationValue {env : Environment} {goal outer : Goal}
    (continuation : Continuation env goal outer) : Atom := Base.encoded (continuationTerm continuation)
private abbrev expansionValue {env : Environment} {outer : Goal}
    (expansion : GeneralPremise.Scheduler.Expansion (Task env outer) (Result env outer) Obligation) : Atom :=
  Base.encoded (encodeOption expansionTerm (some expansion))

theorem Base.add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (Base.v name) = Base.number value) :
    PureReturns Base.runtime caller state (Base.a "+" [Base.v name, Base.number 1]) state (Base.number (value + 1)) := by
  apply native_binary_call_returns Base.runtime caller state state state state "+"
    (Base.v name) (Base.number 1) (Base.number value) (Base.number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns Base.runtime caller state name
  · exact grounded_returns Base.runtime caller state (.int 1)
  · simpa only [Base.number, Base.encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

private def contextPattern : Atom :=
  Base.a "PremiseContext" [Base.v "index", Base.v "rule", Base.v "spec", Base.v "bound", Base.v "premise", Base.v "quantifiers"]
private def contextNextData : Atom :=
  Base.a "PremiseContext" [Base.v "index", Base.v "rule", Base.v "spec", Base.v "bound", Base.v "next", Base.number 0]
private def contextQuantifiedData : Atom :=
  Base.a "PremiseContext" [Base.v "index", Base.v "rule", Base.v "spec", Base.v "bound", Base.v "premise", Base.v "next"]
private def contextNextBody : Atom :=
  Base.a "let" [Base.v "next", Base.a "+" [Base.v "premise", Base.number 1], contextNextData]
private def contextQuantifiedBody : Atom :=
  Base.a "let" [Base.v "next", Base.a "+" [Base.v "quantifiers", Base.number 1], contextQuantifiedData]
private def contextNextCases : SpaceSemantics.Cases :=
  [(contextPattern, contextNextBody), (Base.v "bad", .symbol "None")]
private def contextQuantifiedCases : SpaceSemantics.Cases :=
  [(contextPattern, contextQuantifiedBody), (Base.v "bad", .symbol "None")]
private def contextCaptured (context : GeneralPremise.Context) (caller : Subst) : Subst :=
  [("quantifiers", Base.number context.quantifierDepth), ("premise", Base.number context.premiseIndex),
   ("bound", Base.encoded (Base.typesTerm context.bound)),
   ("spec", Base.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm context.spec)),
   ("rule", Base.encoded (InferenceCettaWire.AuthoredRule.rewriteTerm context.rule)),
   ("index", Base.number context.ruleIndex)] ++ caller

private theorem context_next_shape : (equation .next).body =
    Base.a "case" [Base.v "context", .expression (contextNextCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem context_quantified_shape : (equation .quantified).body =
    Base.a "case" [Base.v "context", .expression (contextQuantifiedCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem context_template (arguments : List Atom)
    (children : ∀ child ∈ arguments, PureData.Template Base.runtime child) :
    PureData.Template Base.runtime (Base.a "PremiseContext" arguments) :=
  .constructor "PremiseContext" arguments (by decide +kernel) (by decide) children

/-- The actual continuation context update advances the physical authored
premise position and resets the quantifier depth. -/
theorem context_next_returns (state : State) (context : GeneralPremise.Context) :
    PureReturns Base.runtime [] state (Base.a "gslt:premise:context-next" [contextValue context]) state
      (contextValue context.next) := by
  let caller := environment .next [contextValue context]
  let selected := contextCaptured context caller
  let bound := ("next", Base.number (context.premiseIndex + 1)) :: selected
  apply helper_call .next [] state _ _ _ rfl (Base.captured_closed _)
  rw [context_next_shape]
  apply Base.branch_returns caller selected state _ (contextValue context) contextNextCases contextNextBody _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "context"
  · simp [contextNextCases, contextPattern, contextCaptured, contextValue, contextTerm,
      selected, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, Subst.lookup]
  · apply let_returns Base.runtime selected bound state state state (Base.v "next")
      (Base.a "+" [Base.v "premise", Base.number 1]) contextNextData (Base.number (context.premiseIndex + 1)) _
    · exact Base.add_one_returns selected state context.premiseIndex "premise" (by
        simp [selected, contextCaptured, applySubst, Subst.lookup])
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, bound, selected, contextCaptured, caller, environment, Helper.names, Subst.lookup]
    · have templated : PureData.Template Base.runtime contextNextData := by
        apply context_template
        intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact .captured _ | exact .grounded _
      simpa [contextNextData, contextValue, contextTerm, GeneralPremise.Context.next,
        bound, selected, contextCaptured, caller, environment, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
        CettaWireAtom.encodeMany] using PureData.template_return Base.runtime bound state _ templated

/-- Quantifier entry increments its lexical occurrence depth without changing
the caller's rule, binding specification, bound context or premise position. -/
theorem context_quantified_returns (state : State) (context : GeneralPremise.Context) :
    PureReturns Base.runtime [] state (Base.a "gslt:premise:context-quantified" [contextValue context]) state
      (contextValue context.quantified) := by
  let caller := environment .quantified [contextValue context]
  let selected := contextCaptured context caller
  let bound := ("next", Base.number (context.quantifierDepth + 1)) :: selected
  apply helper_call .quantified [] state _ _ _ rfl (Base.captured_closed _)
  rw [context_quantified_shape]
  apply Base.branch_returns caller selected state _ (contextValue context) contextQuantifiedCases contextQuantifiedBody _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "context"
  · simp [contextQuantifiedCases, contextPattern, contextCaptured, contextValue, contextTerm,
      selected, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, Subst.lookup]
  · apply let_returns Base.runtime selected bound state state state (Base.v "next")
      (Base.a "+" [Base.v "quantifiers", Base.number 1]) contextQuantifiedData (Base.number (context.quantifierDepth + 1)) _
    · exact Base.add_one_returns selected state context.quantifierDepth "quantifiers" (by
        simp [selected, contextCaptured, applySubst, Subst.lookup])
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, bound, selected, contextCaptured, caller, environment, Helper.names, Subst.lookup]
    · have templated : PureData.Template Base.runtime contextQuantifiedData := by
        apply context_template
        intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals exact .captured _
      simpa [contextQuantifiedData, contextValue, contextTerm, GeneralPremise.Context.quantified,
        bound, selected, contextCaptured, caller, environment, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
        CettaWireAtom.encodeMany] using PureData.template_return Base.runtime bound state _ templated

#print axioms context_next_returns
#print axioms context_quantified_returns

private abbrev assignmentValue (assignment : Assignment) : Atom := Base.encoded (assignmentTerm assignment)
abbrev Base.patternValue (pattern : Pattern) : Atom := Base.encoded (InferenceCettaWire.encodePattern pattern)
abbrev Base.specValue (spec : RuleBindingSpec) : Atom := Base.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)
abbrev Base.ruleValue (rule : RewriteRule) : Atom := Base.encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
abbrev Base.boundValue (bound : List TypeExpr) : Atom := Base.encoded (Base.typesTerm bound)
abbrev Base.freeValue (free : List (String × TypeExpr)) : Atom := Base.encoded (DeclarationTyping.freeContextTerm free)
abbrev Base.declarationsValue (language : LanguageDef) : Atom := Base.encoded (DeclarationTyping.declarationsTerm language.terms)

private def assignmentFinalChecks : Atom :=
  Base.a "if" [Base.a "==" [Base.v "actualDependencies", Base.v "dependencies"],
    Base.a "if" [Base.a "==" [Base.v "ambient", Base.v "actualAmbient"],
      Base.a "if" [Base.a "gslt:premise:object-pattern" [Base.v "body"],
        Base.a "if" [Base.a "gslt:premise:type-has"
            [Base.v "declarations", Base.v "free", Base.v "bodyBound", Base.v "body", Base.v "expected"],
          Base.a "gslt:premise:check-assignment"
            [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "rule", Base.v "spec", Base.v "rest"],
          Effects.boolean false], Effects.boolean false], Effects.boolean false], Effects.boolean false]
private def assignmentChecks : Atom :=
  Base.a "let*" [.expression [
      .expression [Base.v "actualAmbient", Base.a "gslt:automata:length" [Base.v "bound"]],
      .expression [Base.v "bodyBound", Base.a "gslt:automata:append" [Base.v "dependencies", Base.v "bound"]]],
    assignmentFinalChecks]
private def assignmentTypeCases : SpaceSemantics.Cases :=
  [(.symbol "None", Effects.boolean false), (Base.a "Some" [Base.v "expected"], assignmentChecks)]
private def assignmentTypeLookup : Atom :=
  Base.a "case" [Base.a "gslt:premise:type-context-lookup" [Base.v "name", Base.v "types"],
    .expression (assignmentTypeCases.map fun row => .expression [row.1, row.2])]
private def assignmentRuleCases : SpaceSemantics.Cases :=
  [(Base.a "ScopedRewriteRuleV1" [Base.v "ruleName", Base.v "types", Base.v "premises", Base.v "left", Base.v "right", Base.v "bindings"],
      assignmentTypeLookup), (Base.v "badRule", Effects.boolean false)]
private def assignmentRuleRead : Atom :=
  Base.a "case" [Base.v "rule", .expression (assignmentRuleCases.map fun row => .expression [row.1, row.2])]
private def assignmentDependencyCases : SpaceSemantics.Cases :=
  [(.symbol "None", Effects.boolean false), (Base.a "Some" [Base.v "dependencies"], assignmentRuleRead)]
private def assignmentDependencyRead : Atom :=
  Base.a "case" [Base.a "gslt:rule:scope-metadata-dependencies" [Base.v "spec", Base.v "name"],
    .expression (assignmentDependencyCases.map fun row => .expression [row.1, row.2])]
private def assignmentCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
   (Base.a "LCons" [Base.a "Binding" [Base.v "name", Base.a "ContextualValue" [Base.v "actualDependencies", Base.v "ambient", Base.v "body"]],
      Base.v "rest"], assignmentDependencyRead), (Base.v "bad", Effects.boolean false)]
private theorem assignment_shape : (equation .assignment).body =
    Base.a "case" [Base.v "assignment", .expression (assignmentCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem typesTerm_equal (first second : List TypeExpr) : Base.typesTerm first = Base.typesTerm second ↔ first = second := by
  constructor
  · intro same
    have decoded := congrArg (InferenceCettaWire.decodeList InferenceCettaWire.AuthoredRule.decodeType?) same
    have decode (types : List TypeExpr) :
        InferenceCettaWire.decodeList InferenceCettaWire.AuthoredRule.decodeType? (Base.typesTerm types) = some types :=
      InferenceCettaWire.decodeList_encodeList _ _ InferenceCettaWire.AuthoredRule.decodeType?_typeTerm types
    simpa only [decode, Option.some.injEq] using decoded
  · intro same; subst second; rfl

private theorem types_equal_returns (caller : Subst) (state : State) (first second : List TypeExpr)
    (firstName secondName : String)
    (firstCaptured : applySubst caller (Base.v firstName) = Base.boundValue first)
    (secondCaptured : applySubst caller (Base.v secondName) = Base.boundValue second) :
    PureReturns Base.runtime caller state (Base.a "==" [Base.v firstName, Base.v secondName]) state
      (Effects.boolean (first == second)) := by
  have returned := CettaWireAtom.equality_captured_returns Base.runtime caller state
    (Base.typesTerm first) (Base.typesTerm second) firstName secondName firstCaptured secondCaptured
  have compared : decide (Base.typesTerm first = Base.typesTerm second) = (first == second) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, typesTerm_equal, beq_iff_eq]
  simpa only [compared] using returned

theorem Base.natural_equal_returns (caller : Subst) (state : State) (first second : Nat)
    (firstName secondName : String)
    (firstCaptured : applySubst caller (Base.v firstName) = Base.number first)
    (secondCaptured : applySubst caller (Base.v secondName) = Base.number second) :
    PureReturns Base.runtime caller state (Base.a "==" [Base.v firstName, Base.v secondName]) state
      (Effects.boolean (first == second)) := by
  have returned := CettaWireAtom.equality_captured_returns Base.runtime caller state
    (.natural first) (.natural second) firstName secondName firstCaptured secondCaptured
  have compared : decide (Term.natural first = Term.natural second) = (first == second) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Term.natural.injEq, beq_iff_eq]
  simpa only [compared] using returned

private theorem assignment_dependencies_returns (caller : Subst) (state : State)
    (spec : RuleBindingSpec) (name : String)
    (captured : [Base.v "spec", Base.v "name"].map (applySubst caller) = [Base.specValue spec, Base.stringValue name]) :
    PureReturns Base.runtime caller state (Base.a "gslt:rule:scope-metadata-dependencies" [Base.v "spec", Base.v "name"]) state
      (Base.encoded (encodeOption Base.typesTerm (RuleBinding.dependencies? spec name))) := by
  have returned := RuleInstantiationExecution.ScopedMetadata.dependencies_captured_returns caller state
    spec name (Base.v "spec") (Base.v "name") captured
  have transferred := Base.previous_returns (by decide +kernel) returned
  cases selected : RuleBinding.dependencies? spec name <;>
    simpa only [RuleInstantiationExecution.ScopedMetadata.dependencyOptionTerm, selected,
      encodeOption, Base.typesTerm, InferenceCettaWire.encodeList] using transferred

private theorem assignment_length_returns (caller : Subst) (state : State)
    (bound : List TypeExpr) (captured : applySubst caller (Base.v "bound") = Base.boundValue bound) :
    PureReturns Base.runtime caller state (Base.a "gslt:automata:length" [Base.v "bound"]) state (Base.number bound.length) := by
  have returned := MatchAutomataSourceExecution.length_captured_returns caller state
    (bound.map InferenceCettaWire.AuthoredRule.typeTerm) (Base.v "bound") (by
      simpa only [Base.boundValue, Base.typesTerm, MatchAutomataSourceExecution.listValue,
        CettaWire.encodeList_map, Function.id_comp] using captured)
  have transferred := Base.previous_returns (by decide +kernel)
    (RuleExecutionProgram.automata_captured_returns (by decide +kernel) returned)
  simpa only [List.length_map] using transferred

private theorem assignment_append_returns (caller : Subst) (state : State)
    (dependencies bound : List TypeExpr)
    (captured : [Base.v "dependencies", Base.v "bound"].map (applySubst caller) =
      [Base.boundValue dependencies, Base.boundValue bound]) :
    PureReturns Base.runtime caller state (Base.a "gslt:automata:append" [Base.v "dependencies", Base.v "bound"]) state
      (Base.boundValue (dependencies ++ bound)) := by
  have returned := MatchAutomataSourceExecution.append_captured_returns caller state
    (dependencies.map InferenceCettaWire.AuthoredRule.typeTerm)
    (bound.map InferenceCettaWire.AuthoredRule.typeTerm) (Base.v "dependencies") (Base.v "bound") (by
      simpa only [Base.boundValue, Base.typesTerm, MatchAutomataSourceExecution.listValue,
        CettaWire.encodeList_map, Function.id_comp] using captured)
  have transferred := Base.previous_returns (by decide +kernel)
    (RuleExecutionProgram.automata_captured_returns (by decide +kernel) returned)
  simpa only [Base.boundValue, Base.typesTerm, MatchAutomataSourceExecution.listValue,
    ← List.map_append, CettaWire.encodeList_map, Function.id_comp] using transferred

private theorem assignment_object_returns (caller : Subst) (state : State)
    (pattern : Pattern) (captured : applySubst caller (Base.v "body") = Base.patternValue pattern) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:object-pattern" [Base.v "body"]) state
      (Effects.boolean (isObjectPattern pattern)) := by
  exact Base.previous_returns (by decide +kernel)
    (OpenAdmission.object_pattern_captured_returns caller state pattern (Base.v "body") captured)

private theorem assignment_typed_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (pattern : Pattern) (expected : TypeExpr)
    (captured : [Base.v "declarations", Base.v "free", Base.v "bodyBound", Base.v "body", Base.v "expected"].map (applySubst caller) =
      [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, Base.patternValue pattern, Base.typeValue expected]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:type-has"
      [Base.v "declarations", Base.v "free", Base.v "bodyBound", Base.v "body", Base.v "expected"]) state
      (Effects.boolean (Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound pattern expected)) := by
  exact Base.previous_returns (by decide +kernel)
    (DeclarationTyping.check_has_type_captured_returns caller state language free bound pattern expected
      (Base.v "declarations") (Base.v "free") (Base.v "bodyBound") (Base.v "body") (Base.v "expected") captured)


private theorem assignment_final_checks_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (value : ContextualValue) (dependencies : List TypeExpr) (expected : TypeExpr) (restCheck : Bool)
    (declarationsCaptured : applySubst caller (Base.v "declarations") = Base.declarationsValue language)
    (freeCaptured : applySubst caller (Base.v "free") = Base.freeValue free)
    (actualDependenciesCaptured : applySubst caller (Base.v "actualDependencies") = Base.boundValue value.dependencies)
    (dependenciesCaptured : applySubst caller (Base.v "dependencies") = Base.boundValue dependencies)
    (ambientCaptured : applySubst caller (Base.v "ambient") = Base.number value.ambient)
    (actualAmbientCaptured : applySubst caller (Base.v "actualAmbient") = Base.number bound.length)
    (bodyCaptured : applySubst caller (Base.v "body") = Base.patternValue value.body)
    (bodyBoundCaptured : applySubst caller (Base.v "bodyBound") = Base.boundValue (dependencies ++ bound))
    (expectedCaptured : applySubst caller (Base.v "expected") = Base.typeValue expected)
    (continued : PureReturns Base.runtime caller state
      (Base.a "gslt:premise:check-assignment"
        [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "rule", Base.v "spec", Base.v "rest"])
      state (Effects.boolean restCheck)) :
    PureReturns Base.runtime caller state assignmentFinalChecks state
      (Effects.boolean ((value.dependencies == dependencies) && (value.ambient == bound.length) &&
        isObjectPattern value.body &&
        Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType language
          (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free)
          (dependencies ++ bound) value.body expected && restCheck)) := by
  have dependencyEquality := types_equal_returns caller state value.dependencies dependencies
    "actualDependencies" "dependencies" actualDependenciesCaptured dependenciesCaptured
  have ambientEquality := Base.natural_equal_returns caller state value.ambient bound.length
    "ambient" "actualAmbient" ambientCaptured actualAmbientCaptured
  have objectReturned := assignment_object_returns caller state value.body bodyCaptured
  have typingReturned := assignment_typed_returns caller state language free (dependencies ++ bound)
    value.body expected (by simp only [List.map_cons, List.map_nil, declarationsCaptured,
      freeCaptured, bodyBoundCaptured, bodyCaptured, expectedCaptured])
  unfold assignmentFinalChecks
  apply Base.bool_if_returns caller state _ (value.dependencies == dependencies) _ _ _ dependencyEquality
  cases dependenciesEqual : value.dependencies == dependencies with
  | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact grounded_returns Base.runtime caller state (.bool false)
  | true =>
      simp only [Bool.true_and, ↓reduceIte]
      apply Base.bool_if_returns caller state _ (value.ambient == bound.length) _ _ _ ambientEquality
      cases ambientEqual : value.ambient == bound.length with
      | false =>
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact grounded_returns Base.runtime caller state (.bool false)
      | true =>
          simp only [Bool.true_and, ↓reduceIte]
          apply Base.bool_if_returns caller state _ (isObjectPattern value.body) _ _ _ objectReturned
          cases objectChecked : isObjectPattern value.body with
          | false =>
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact grounded_returns Base.runtime caller state (.bool false)
          | true =>
              simp only [Bool.true_and, ↓reduceIte]
              apply Base.bool_if_returns caller state _ _ _ _ _ typingReturned
              cases typed : Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType language
                  (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free)
                  (dependencies ++ bound) value.body expected with
              | false =>
                  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  exact grounded_returns Base.runtime caller state (.bool false)
              | true =>
                  simpa only [Bool.true_and, ↓reduceIte] using continued

private def assignmentOriginalCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment) : Subst :=
  environment .assignment [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound,
    Base.ruleValue rule, Base.specValue spec, assignmentValue assignment]
private def assignmentConsCaller (name : String) (value : ContextualValue)
    (rest : Assignment) (caller : Subst) : Subst :=
  [("rest", assignmentValue rest), ("body", Base.patternValue value.body),
    ("ambient", Base.number value.ambient), ("actualDependencies", Base.boundValue value.dependencies),
    ("name", Base.stringValue name)] ++ caller
def Base.assignmentRuleCaller (rule : RewriteRule) (caller : Subst) : Subst :=
  [("bindings", Base.encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)),
    ("right", Base.patternValue rule.right), ("left", Base.patternValue rule.left),
    ("premises", Base.encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)),
    ("types", Base.typesValue rule.typeContext), ("ruleName", Base.stringValue rule.name)] ++ caller



/-- The actual source folds every stored capture against its declared
parameter and ambient contexts, object guard and authored declaration typing. -/
theorem check_assignment_returns (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (assignment : Assignment) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:check-assignment" [Base.declarationsValue language, Base.freeValue free,
        Base.boundValue bound, Base.ruleValue rule, Base.specValue spec, assignmentValue assignment]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound rule spec assignment)) := by
  induction assignment with
  | nil =>
      let caller := assignmentOriginalCaller language free bound rule spec []
      apply helper_call .assignment [] state _ _ _ rfl (Base.captured_closed _)
      rw [assignment_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") assignmentCases (Effects.boolean true) _
      · simpa [caller, assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup,
          assignmentValue, assignmentTerm, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, CettaWireAtom.encode] using
          variable_returns Base.runtime caller state "assignment"
      · simp [assignmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns Base.runtime caller state (.bool true)
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      let caller := assignmentOriginalCaller language free bound rule spec ((name, value) :: rest)
      let selected := assignmentConsCaller name value rest caller
      apply helper_call .assignment [] state _ _ _ rfl (Base.captured_closed _)
      rw [assignment_shape]
      apply Base.branch_returns caller selected state _ (assignmentValue ((name, value) :: rest))
        assignmentCases assignmentDependencyRead _
      · simpa [caller, assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "assignment"
      · simp [assignmentCases, selected, caller, assignmentConsCaller, assignmentOriginalCaller,
          environment, Helper.names, assignmentValue, assignmentTerm,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          InferenceCettaWire.AuthoredRule.contextualValueTerm, InferenceCettaWire.encodeList,
          Base.boundValue, Base.typesTerm, Base.patternValue,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, Subst.lookup]
      · have dependenciesReturned := assignment_dependencies_returns selected state spec name (by
          simp [selected, assignmentConsCaller, caller, assignmentOriginalCaller,
            environment, Helper.names, applySubst, Subst.lookup])
        change PureReturns Base.runtime selected state assignmentDependencyRead state _
        cases dependenciesSelected : RuleBinding.dependencies? spec name with
        | none =>
            simp only [ConditionalEquationExecution.checkAssignment, List.all_cons,
              dependenciesSelected, Bool.false_and]
            apply Base.branch_returns selected selected state _ (.symbol "None")
              assignmentDependencyCases (Effects.boolean false) _
            · simpa only [dependenciesSelected, encodeOption, CettaWireAtom.encode] using dependenciesReturned
            · simp [assignmentDependencyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact grounded_returns Base.runtime selected state (.bool false)
        | some dependencies =>
            let dependencyCaller := ("dependencies", Base.boundValue dependencies) :: selected
            apply Base.branch_returns selected dependencyCaller state _ (Base.encoded (encodeOption Base.typesTerm (some dependencies)))
              assignmentDependencyCases assignmentRuleRead _
            · simpa only [dependenciesSelected] using dependenciesReturned
            · simp [assignmentDependencyCases, dependencyCaller, selected, assignmentConsCaller, caller,
                assignmentOriginalCaller, environment, Helper.names, encodeOption, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, Base.boundValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · let ruleCaller := Base.assignmentRuleCaller rule dependencyCaller
              apply Base.branch_returns dependencyCaller ruleCaller state _ (Base.ruleValue rule)
                assignmentRuleCases assignmentTypeLookup _
              · simpa [dependencyCaller, selected, assignmentConsCaller, caller,
                  assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup] using
                  variable_returns Base.runtime dependencyCaller state "rule"
              · simp [assignmentRuleCases, Base.ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
                  InferenceCettaWire.encodeList, ruleCaller, Base.assignmentRuleCaller,
                  dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                  environment, Helper.names, Base.typesValue, Base.patternValue, Base.stringValue,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
              · have typeReturned := type_context_lookup_captured_returns ruleCaller state name rule.typeContext
                  (Base.v "name") (Base.v "types") (by
                    simp [ruleCaller, Base.assignmentRuleCaller, dependencyCaller, selected, assignmentConsCaller,
                      caller, assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup])
                cases typeSelected : List.lookup name rule.typeContext with
                | none =>
                    simp only [ConditionalEquationExecution.checkAssignment, List.all_cons,
                      dependenciesSelected, typeSelected, Bool.false_and]
                    apply Base.branch_returns ruleCaller ruleCaller state _ (.symbol "None")
                      assignmentTypeCases (Effects.boolean false) _
                    · simpa only [typeSelected, Base.typeOptionValue, encodeOption, CettaWireAtom.encode] using typeReturned
                    · simp [assignmentTypeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                    · exact grounded_returns Base.runtime ruleCaller state (.bool false)
                | some expected =>
                    let typeCaller := ("expected", Base.typeValue expected) :: ruleCaller
                    apply Base.branch_returns ruleCaller typeCaller state _ (Base.typeOptionValue (some expected))
                      assignmentTypeCases assignmentChecks _
                    · simpa only [typeSelected] using typeReturned
                    · simp [assignmentTypeCases, typeCaller, Base.typeOptionValue, encodeOption,
                        ruleCaller, Base.assignmentRuleCaller, dependencyCaller, selected, assignmentConsCaller,
                        caller, assignmentOriginalCaller, environment, Helper.names,
                        SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                        SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
                        CettaWireAtom.encodeMany, Base.typeValue, Subst.lookup]
                    · let lengthCaller := ("actualAmbient", Base.number bound.length) :: typeCaller
                      let checksCaller := ("bodyBound", Base.boundValue (dependencies ++ bound)) :: lengthCaller
                      apply PureData.let_bindings_return (pairs := [
                        (Base.v "actualAmbient", Base.a "gslt:automata:length" [Base.v "bound"]),
                        (Base.v "bodyBound", Base.a "gslt:automata:append" [Base.v "dependencies", Base.v "bound"])])
                        (final := checksCaller) (middle := state) _ state assignmentFinalChecks _ _
                      · apply PureData.BindingsReturn.cons (bound := lengthCaller) (middle := state)
                          (value := Base.number bound.length)
                        · exact assignment_length_returns typeCaller state bound (by
                            simp [typeCaller, ruleCaller, Base.assignmentRuleCaller, dependencyCaller, selected,
                              assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                            lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller, dependencyCaller,
                            selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                            environment, Helper.names, Subst.lookup]
                        · apply PureData.BindingsReturn.cons (bound := checksCaller) (middle := state)
                            (value := Base.boundValue (dependencies ++ bound))
                          · exact assignment_append_returns lengthCaller state dependencies bound (by
                              simp [lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                                dependencyCaller, selected, assignmentConsCaller, caller,
                                assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup])
                          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                              checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller,
                              assignmentOriginalCaller, environment, Helper.names, Subst.lookup]
                          · exact .nil checksCaller state
                      · have continued : PureReturns Base.runtime checksCaller state
                            (Base.a "gslt:premise:check-assignment" [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "rule", Base.v "spec", Base.v "rest"])
                            state (Effects.boolean (ConditionalEquationExecution.checkAssignment language
                              (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound rule spec rest)) := by
                          apply helper_capture .assignment checksCaller state _ _ _ rfl _ ih
                          simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                            dependencyCaller, selected, assignmentConsCaller, caller,
                            assignmentOriginalCaller, environment, Helper.names, applySubst, Subst.lookup]
                        simpa only [ConditionalEquationExecution.checkAssignment, List.all_cons,
                          dependenciesSelected, typeSelected] using
                          assignment_final_checks_returns checksCaller state language free bound value dependencies expected
                            (ConditionalEquationExecution.checkAssignment language
                              (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound rule spec rest)
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup])
                            (by simp [checksCaller, lengthCaller, typeCaller, ruleCaller, Base.assignmentRuleCaller,
                              dependencyCaller, selected, assignmentConsCaller, caller, assignmentOriginalCaller,
                              environment, Helper.names, applySubst, Subst.lookup]) continued

#print axioms check_assignment_returns


#print axioms decodeContext?_contextTerm

/-- Captured assignment values remain literal source data, including bodies
with free-variable constructors and genuinely nonempty dependency contexts. -/
theorem check_assignment_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment)
    (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, Base.ruleValue rule,
       Base.specValue spec, assignmentValue assignment]) :
    PureReturns Base.runtime caller state
      (Base.a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free)
        bound rule spec assignment)) :=
  helper_capture .assignment caller state _ _ _ rfl captured
    (check_assignment_returns state language free bound rule spec assignment)

/-- A finite lookup footprint is extracted from the actual stored bodies;
the mathematical environment's free-name context may remain infinite. -/
def assignmentFreeContext (environment : Environment) (assignment : Assignment) :
    List (String × TypeExpr) :=
  environment.free.entriesOn (ConditionalEquationExecution.assignmentFreeNames assignment)

/-- The checked fold realizes the original typed-assignment predicate after
the required finite context has been earned from the actual stored values. -/
theorem check_typed_assignment_returns (state : State) (environment : Environment)
    (context : GeneralPremise.Context) (assignment : Assignment) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:check-assignment" [Base.declarationsValue environment.language,
        Base.freeValue (assignmentFreeContext environment assignment), Base.boundValue context.bound,
        Base.ruleValue context.rule, Base.specValue context.spec, assignmentValue assignment]) state
      (Effects.boolean (GeneralPremise.checkTypedAssignment environment context assignment)) := by
  simpa only [assignmentFreeContext, GeneralPremise.checkTypedAssignment,
    ConditionalEquationExecution.checkAssignment_finiteFree] using
    check_assignment_returns state environment.language
      (assignmentFreeContext environment assignment) context.bound context.rule context.spec assignment

theorem check_typed_assignment_captured_returns (caller : Subst) (state : State)
    (environment : Environment) (context : GeneralPremise.Context) (assignment : Assignment)
    (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [Base.declarationsValue environment.language, Base.freeValue (assignmentFreeContext environment assignment),
        Base.boundValue context.bound, Base.ruleValue context.rule, Base.specValue context.spec,
        assignmentValue assignment]) :
    PureReturns Base.runtime caller state
      (Base.a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (GeneralPremise.checkTypedAssignment environment context assignment)) :=
  helper_capture .assignment caller state _ _ _ rfl captured
    (check_typed_assignment_returns state environment context assignment)


theorem check_typed_assignment_free_returns (state : State) (env : Environment)
    (context : GeneralPremise.Context) (assignment : Assignment) (free : List (String × TypeExpr))
    (same : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames assignment,
      (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) name = env.free name) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:check-assignment" [Base.declarationsValue env.language, Base.freeValue free, Base.boundValue context.bound,
        Base.ruleValue context.rule, Base.specValue context.spec, assignmentValue assignment]) state
      (Effects.boolean (GeneralPremise.checkTypedAssignment env context assignment)) := by
  have agrees := ConditionalEquationExecution.checkAssignment_congrFree env.language
    (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) env.free context.bound context.rule context.spec assignment
    (fun captureName value member name occurs => same name (List.mem_flatMap.mpr ⟨(captureName, value), member, occurs⟩))
  simpa only [GeneralPremise.checkTypedAssignment, agrees] using
    check_assignment_returns state env.language free context.bound context.rule context.spec assignment

theorem check_typed_assignment_free_captured_returns (caller : Subst) (state : State)
    (env : Environment) (context : GeneralPremise.Context) (assignment : Assignment) (free : List (String × TypeExpr))
    (same : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames assignment,
      (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) name = env.free name)
    (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [Base.declarationsValue env.language, Base.freeValue free, Base.boundValue context.bound, Base.ruleValue context.rule,
        Base.specValue context.spec, assignmentValue assignment]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (GeneralPremise.checkTypedAssignment env context assignment)) :=
  helper_capture .assignment caller state _ _ _ rfl captured
    (check_typed_assignment_free_returns state env context assignment free same)

#print axioms check_typed_assignment_free_returns
#print axioms check_typed_assignment_free_captured_returns

theorem context_next_captured_returns (caller : Subst) (state : State)
    (context : GeneralPremise.Context) (input : Atom)
    (captured : applySubst caller input = contextValue context) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:context-next" [input]) state
      (contextValue context.next) :=
  helper_capture .next caller state _ _ _ rfl
    (by simpa only [List.map_cons, List.map_nil] using congrArg (fun value => [value]) captured)
    (context_next_returns state context)

theorem context_quantified_captured_returns (caller : Subst) (state : State)
    (context : GeneralPremise.Context) (input : Atom)
    (captured : applySubst caller input = contextValue context) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:context-quantified" [input]) state
      (contextValue context.quantified) :=
  helper_capture .quantified caller state _ _ _ rfl
    (by simpa only [List.map_cons, List.map_nil] using congrArg (fun value => [value]) captured)
    (context_quantified_returns state context)

/-- This predicate records which original continuations the administrative
source transition currently realizes. Its false cases remain pending tasks. -/
def administrativeContinuation {environment : Environment} {goal outer : Goal} :
    Continuation environment goal outer → Bool
  | .rootBody _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => false
  | .stepped _ _ => false
  | _ => true

/-- Query, freshness, child-step and root evaluation retain their original
goals until their dedicated machine transitions are implemented. -/
def administrativeGoal : Goal → Bool
  | .premises _ _ _ => true
  | .quantified _ _ _ _ _ _ => true
  | .premise _ (.forAll _ _ _) _ => true
  | .steps _ _ _ _ => true
  | _ => false

def administrativeTask {environment : Environment} {outer : Goal} :
    Task environment outer → Bool
  | .evaluate goal _ => administrativeGoal goal
  | .deliver _ tail => administrativeContinuation tail
  | .scanChildren _ _ _ _ _ _ => true
  | _ => false

/-- Only quantified nonempty entry checks a new assignment in this profile;
its exact newly bound parameter participates in the finite free-name footprint. -/
def evaluationFreeContext (environment : Environment) : Goal → List (String × TypeExpr)
  | .quantified context parameter _ _ (element :: _) initial =>
      assignmentFreeContext environment
        (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial)
  | _ => []

#print axioms check_assignment_captured_returns
#print axioms check_typed_assignment_returns
#print axioms check_typed_assignment_captured_returns
#print axioms context_next_captured_returns
#print axioms context_quantified_captured_returns


private abbrev resultValue {environment : Environment} {goal : Goal}
    (result : Result environment goal) : Atom := Base.encoded (resultTerm result)
private abbrev eventValue (event : GeneralPremise.Event) : Atom := Base.encoded (eventTerm event)
private abbrev eventsValue (events : List GeneralPremise.Event) : Atom := Base.encoded (eventsTerm events)
private abbrev premiseValue (premise : Premise) : Atom :=
  Base.encoded (InferenceCettaWire.AuthoredRule.premiseTerm premise)
private abbrev premisesValue (premises : List Premise) : Atom :=
  Base.encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm premises)

abbrev Base.caseData (input : Atom) (cases : SpaceSemantics.Cases) : Atom :=
  Base.a "case" [input, .expression (cases.map fun row => .expression [row.1, row.2])]
private abbrev singletonData (value : Atom) : Atom := Base.a "LCons" [value, .symbol "LNil"]
private abbrev expansionData (tasks answers unresolved : Atom) : Atom :=
  Base.a "Some" [Base.a "PremiseExpansion" [tasks, answers, unresolved]]
private abbrev tasksData (task : Atom) : Atom :=
  expansionData (singletonData task) (.symbol "LNil") (.symbol "LNil")

private def deliverDoneData : Atom :=
  expansionData (.symbol "LNil") (singletonData (Base.v "result")) (.symbol "LNil")

private def deliverNextData : Atom := tasksData
  (Base.a "PremiseEvaluate" [Base.a "PremisesGoal" [Base.v "next", Base.v "premises", Base.v "assignment"],
    Base.a "PremisePrepend" [Base.v "context", Base.v "premise", Base.v "premises", Base.v "initial",
      Base.v "assignment", Base.v "event", Base.v "tail"]])
private def deliverNextBody : Atom :=
  Base.a "let" [Base.v "next", Base.a "gslt:premise:context-next" [Base.v "context"], deliverNextData]
private def deliverNextCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "PremiseAnswer" [Base.v "assignment", Base.v "event"]], deliverNextBody),
    (Base.v "badResult", .symbol "None")]

private def deliverPrependData : Atom := tasksData
  (Base.a "PremiseDeliver" [Base.a "PremiseResult"
    [Base.a "PremisesGoal" [Base.v "context", Base.a "LCons" [Base.v "premise", Base.v "premises"], Base.v "initial"],
      Base.a "PremisesAnswer" [Base.v "assignment", Base.a "LCons" [Base.v "event", Base.v "events"]]], Base.v "tail"])
private def deliverPrependCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "PremisesAnswer" [Base.v "assignment", Base.v "events"]], deliverPrependData),
    (Base.v "badResult", .symbol "None")]

private def deliverQuantifierData : Atom := tasksData
  (Base.a "PremiseDeliver" [Base.a "PremiseResult"
    [Base.a "PremiseGoal" [Base.v "context", Base.a "ForAll" [Base.v "collection", Base.v "parameter", Base.v "body"], Base.v "initial"],
      Base.a "PremiseAnswer" [Base.v "assignment", Base.a "PremiseQuantifiedEvent"
        [Base.v "premise", Base.v "quantifiers", Base.v "kind", Base.v "events"]]], Base.v "tail"])
private def deliverQuantifierContextCases : SpaceSemantics.Cases :=
  [(contextPattern, deliverQuantifierData), (Base.v "badContext", .symbol "None")]
private def deliverQuantifierCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "QuantifiedAnswer" [Base.v "assignment", Base.v "events"]],
    Base.caseData (Base.v "context") deliverQuantifierContextCases), (Base.v "badResult", .symbol "None")]

private def deliverElementData : Atom := tasksData
  (Base.a "PremiseEvaluate"
    [Base.a "QuantifiedGoal" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "next", Base.v "elements", Base.v "restored"],
      Base.a "PremisePrependElement" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "element",
        Base.v "elements", Base.v "initial", Base.v "assignment", Base.v "event", Base.v "tail"]])
private def deliverElementBody : Atom :=
  Base.a "let*" [.expression
    [.expression [Base.v "restored", Base.v "initial"],
      .expression [Base.v "next", Base.a "+" [Base.v "index", Base.number 1]]], deliverElementData]
private def deliverElementCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "PremiseAnswer" [Base.v "assignment", Base.v "event"]], deliverElementBody),
    (Base.v "badResult", .symbol "None")]

private def deliverPrependElementData : Atom := tasksData
  (Base.a "PremiseDeliver" [Base.a "PremiseResult"
    [Base.a "QuantifiedGoal" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index",
      Base.a "LCons" [Base.v "element", Base.v "elements"], Base.v "initial"],
      Base.a "QuantifiedAnswer" [Base.v "assignment", Base.a "LCons"
        [Base.a "QuantifiedElement" [Base.v "index", Base.v "element", singletonData (Base.v "event")], Base.v "events"]]], Base.v "tail"])
private def deliverPrependElementCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "QuantifiedAnswer" [Base.v "assignment", Base.v "events"]], deliverPrependElementData),
    (Base.v "badResult", .symbol "None")]

private def deliverSearchedRootData : Atom := tasksData
  (Base.a "PremiseDeliver" [Base.a "PremiseResult"
    [Base.a "StepsGoal" [Base.v "bound", Base.v "type", Base.v "source", Base.v "limit"],
      Base.a "StepsAnswer" [Base.v "index", Base.v "trace", Base.v "captured", Base.v "completed", Base.v "events", Base.v "target"]], Base.v "tail"])
private def deliverSearchedRootCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseResult" [Base.v "goal", Base.a "RootAnswer"
      [Base.v "trace", Base.v "captured", Base.v "completed", Base.v "events", Base.v "target"]], deliverSearchedRootData),
    (Base.v "badResult", .symbol "None")]

private def deliverCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseDone" [Base.v "outer"], deliverDoneData),
    (Base.a "PremiseNext" [Base.v "context", Base.v "premise", Base.v "premises", Base.v "initial", Base.v "tail"],
      Base.caseData (Base.v "result") deliverNextCases),
    (Base.a "PremisePrepend" [Base.v "context", Base.v "premise", Base.v "premises", Base.v "initial", Base.v "middle", Base.v "event", Base.v "tail"],
      Base.caseData (Base.v "result") deliverPrependCases),
    (Base.a "PremiseQuantifier" [Base.v "context", Base.v "collection", Base.v "parameter", Base.v "body", Base.v "initial",
      Base.v "kind", Base.v "elements", Base.v "tail"], Base.caseData (Base.v "result") deliverQuantifierCases),
    (Base.a "PremiseElement" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "element", Base.v "elements",
      Base.v "initial", Base.v "tail"], Base.caseData (Base.v "result") deliverElementCases),
    (Base.a "PremisePrependElement" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "element",
      Base.v "elements", Base.v "initial", Base.v "middle", Base.v "event", Base.v "tail"], Base.caseData (Base.v "result") deliverPrependElementCases),
    (Base.a "PremiseSearchedRoot" [Base.v "bound", Base.v "type", Base.v "source", Base.v "index", Base.v "limit", Base.v "tail"],
      Base.caseData (Base.v "result") deliverSearchedRootCases), (Base.v "unsupported", .symbol "None")]

private theorem deliver_shape : (equation .deliver).body = Base.caseData (Base.v "continuation") deliverCases := by
  decide +kernel

private def machineDataHeads : List String :=
  ["Some", "LCons", "PremiseExpansion", "PremiseEvaluate", "PremiseDeliver", "PremiseResult",
    "PremiseGoal", "PremisesGoal", "QuantifiedGoal", "StepsGoal", "PremiseAnswer", "PremisesAnswer",
    "QuantifiedAnswer", "StepsAnswer", "PremisePrepend", "ForAll", "PremiseQuantifiedEvent",
    "PremisePrependElement", "QuantifiedElement", "PremiseNext", "PremiseElement", "PremiseQuantifier",
    "PremiseScanChildren", "RootGoal", "PremiseSearchedRoot", "PremiseQuantifiedAssignment",
    "PremiseCollectionProjection", "GrammarTypingV1", "GrammarTypingWrappedV1", "TBase", "PremiseSignature", "PremiseProviderRow"]

private theorem machine_data_template (head : String) (arguments : List Atom)
    (supported : head ∈ machineDataHeads)
    (children : ∀ child ∈ arguments, PureData.Template Base.runtime child) :
    PureData.Template Base.runtime (Base.a head arguments) := by
  have checked : machineDataHeads.all (fun name => decide
      ((ioHead name || StdLib.known name || Base.runtime.equations.any (·.head == name)) = false ∧
        name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])) = true := by
    decide +kernel
  have row := List.all_eq_true.mp checked head supported
  rw [decide_eq_true_eq] at row
  exact .constructor head arguments row.1 row.2 children

local macro "machine_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply machine_data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

/-- Delivery through the original terminal continuation preserves the exact
typed result and its authored histories as the sole completed answer. -/
theorem delivered_done_returns (state : State) (env : Environment) (goal : Goal)
    (result : Result env goal) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result, continuationValue (env := env) (.done goal)]) state
      (expansionValue (GeneralPremise.Execution.delivered env goal result (.done goal))) := by
  let caller := environment .deliver [resultValue result, continuationValue (env := env) (.done goal)]
  let selected := ("outer", goalValue goal) :: caller
  apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
  rw [deliver_shape]
  apply Base.branch_returns caller selected state _ (continuationValue (env := env) (.done goal)) deliverCases deliverDoneData _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "continuation"
  · simp [deliverCases, continuationValue, continuationTerm, selected, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, goalValue, Subst.lookup]
  · have templated : PureData.Template Base.runtime deliverDoneData := by
      unfold deliverDoneData
      machine_template
    simpa [deliverDoneData, expansionValue, expansionTerm, GeneralPremise.Execution.delivered,
      encodeOption, encodeList, selected, caller, environment, Helper.names, applySubst,
      applySubst.applySubstList, Subst.lookup, resultValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return Base.runtime selected state _ templated

#print axioms delivered_done_returns


/-- A completed original premise schedules the original ordered remainder
and records the exact assignment and event in its continuation. -/
theorem delivered_next_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (premise : Premise) (premises : List Premise)
    (initial : Assignment)
    (tail : Continuation env (.premises context (premise :: premises) initial) outer)
    (result : Result env (.premise context premise initial)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver"
        [resultValue result, continuationValue (.nextPremise context premise premises initial tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.nextPremise context premise premises initial tail))) := by
  cases result with
  | premise assignment event valid =>
      let result : Result env (.premise context premise initial) := .premise assignment event valid
      let caller := environment .deliver
        [resultValue result, continuationValue (.nextPremise context premise premises initial tail)]
      let framed := [("tail", continuationValue tail), ("initial", assignmentValue initial),
        ("premises", premisesValue premises), ("premise", premiseValue premise),
        ("context", contextValue context)] ++ caller
      let selected := [("event", eventValue event), ("assignment", assignmentValue assignment),
        ("goal", goalValue (.premise context premise initial))] ++ framed
      let bound := ("next", contextValue context.next) :: selected
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.nextPremise context premise premises initial tail)) deliverCases
        (Base.caseData (Base.v "result") deliverNextCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, contextValue, premiseValue,
          premisesValue, assignmentValue, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverNextCases deliverNextBody _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverNextCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, assignmentValue, eventValue, Subst.lookup]
        · apply let_returns Base.runtime selected bound state state state (Base.v "next")
            (Base.a "gslt:premise:context-next" [Base.v "context"]) deliverNextData
            (contextValue context.next) _
          · exact context_next_captured_returns selected state context (Base.v "context") (by
              simp [selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              bound, selected, framed, caller, environment, Helper.names, Subst.lookup]
          · have templated : PureData.Template Base.runtime deliverNextData := by
              unfold deliverNextData
              machine_template
            simpa [deliverNextData, expansionValue, expansionTerm, GeneralPremise.Execution.delivered,
              taskTerm, continuationTerm, goalTerm, encodeOption, encodeList, InferenceCettaWire.encodeList,
              bound, selected, framed, caller, environment, Helper.names, applySubst,
              applySubst.applySubstList, Subst.lookup, contextValue, premiseValue, premisesValue,
              assignmentValue, eventValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return Base.runtime bound state _ templated

/-- The original head event is prepended once, retaining the ordered tail
history and the exact completed assignment. -/
theorem delivered_prepend_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (premise : Premise) (premises : List Premise)
    (initial middle : Assignment) (event : GeneralPremise.Event)
    (head : GeneralPremise.PremiseHolds env context premise initial middle event)
    (tail : Continuation env (.premises context (premise :: premises) initial) outer)
    (result : Result env (.premises context.next premises middle)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver"
        [resultValue result, continuationValue (.prepend context premise premises initial middle event head tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.prepend context premise premises initial middle event head tail))) := by
  cases result with
  | premises assignment events valid =>
      change PureReturns Base.runtime [] state
        (Base.a "gslt:premise:machine-deliver"
          [resultValue (.premises assignment events valid),
            continuationValue (.prepend context premise premises initial middle event head tail)]) state
        (expansionValue (env := env) (outer := outer)
          { tasks := [.deliver (.premises assignment (event :: events) (.cons head valid)) tail] })
      let result : Result env (.premises context.next premises middle) := .premises assignment events valid
      let caller := environment .deliver
        [resultValue result, continuationValue (.prepend context premise premises initial middle event head tail)]
      let framed := [("tail", continuationValue tail), ("event", eventValue event),
        ("middle", assignmentValue middle), ("initial", assignmentValue initial),
        ("premises", premisesValue premises), ("premise", premiseValue premise),
        ("context", contextValue context)] ++ caller
      let selected := [("events", eventsValue events), ("assignment", assignmentValue assignment),
        ("goal", goalValue (.premises context.next premises middle))] ++ framed
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.prepend context premise premises initial middle event head tail)) deliverCases
        (Base.caseData (Base.v "result") deliverPrependCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, contextValue, premiseValue,
          premisesValue, assignmentValue, eventValue, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverPrependCases deliverPrependData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverPrependCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, assignmentValue, eventsValue, Subst.lookup]
        · have templated : PureData.Template Base.runtime deliverPrependData := by
            unfold deliverPrependData
            machine_template
          simpa [deliverPrependData, result, expansionValue, expansionTerm, GeneralPremise.Execution.delivered,
            taskTerm, resultTerm, goalTerm, encodeOption, encodeList, InferenceCettaWire.encodeList,
            eventsTerm, selected, framed, caller, environment, Helper.names, applySubst,
            applySubst.applySubstList, Subst.lookup, contextValue, premiseValue, premisesValue,
            assignmentValue, eventValue, eventsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime selected state _ templated

#print axioms delivered_next_returns
#print axioms delivered_prepend_returns


private abbrev quantifiedEventsValue (events : List (Nat × Pattern × List GeneralPremise.Event)) : Atom :=
  Base.encoded (quantifiedEventsTerm events)
private abbrev collectionValue (kind : CollType) : Atom := Base.encoded (InferenceCettaWire.encodeCollectionType kind)
abbrev Base.patternsValue (patterns : List Pattern) : Atom := Base.encoded (Base.patternsTerm patterns)

theorem delivered_quantifier_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise)
    (initial : Assignment) (kind : CollType) (elements : List Pattern)
    (read : GeneralPremise.finiteCollection? context.bound.length initial collection = some (kind, elements))
    (tail : Continuation env (.premise context (.forAll collection parameter body) initial) outer)
    (result : Result env (.quantified context parameter body 0 elements initial)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result,
        continuationValue (.quantifier context collection parameter body initial kind elements read tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.quantifier context collection parameter body initial kind elements read tail))) := by
  cases result with
  | quantified assignment events valid =>
      let result : Result env (.quantified context parameter body 0 elements initial) := .quantified assignment events valid
      let caller := environment .deliver [resultValue result,
        continuationValue (.quantifier context collection parameter body initial kind elements read tail)]
      let framed := [("tail", continuationValue tail), ("elements", Base.patternsValue elements),
        ("kind", collectionValue kind), ("initial", assignmentValue initial), ("body", premiseValue body),
        ("parameter", Base.stringValue parameter), ("collection", Base.stringValue collection),
        ("context", contextValue context)] ++ caller
      let selected := [("events", quantifiedEventsValue events), ("assignment", assignmentValue assignment),
        ("goal", goalValue (.quantified context parameter body 0 elements initial))] ++ framed
      let contextual := contextCaptured context selected
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.quantifier context collection parameter body initial kind elements read tail)) deliverCases
        (Base.caseData (Base.v "result") deliverQuantifierCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, contextValue, premiseValue,
          Base.patternsValue, collectionValue, assignmentValue, Base.stringValue, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverQuantifierCases (Base.caseData (Base.v "context") deliverQuantifierContextCases) _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverQuantifierCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, assignmentValue, quantifiedEventsValue, Subst.lookup]
        · apply Base.branch_returns selected contextual state _ (contextValue context)
            deliverQuantifierContextCases deliverQuantifierData _
          · simpa [selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns Base.runtime selected state "context"
          · simp [deliverQuantifierContextCases, contextPattern, contextual, contextCaptured,
              selected, framed, caller, environment, Helper.names, contextValue, contextTerm,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Base.number, Subst.lookup]
          · have templated : PureData.Template Base.runtime deliverQuantifierData := by
              unfold deliverQuantifierData
              machine_template
            simpa [deliverQuantifierData, result, expansionValue, expansionTerm, GeneralPremise.Execution.delivered,
              taskTerm, resultTerm, goalTerm, InferenceCettaWire.AuthoredRule.premiseTerm,
              InferenceCettaWire.CettaTerm.string, encodeOption, encodeList, eventTerm,
              contextual, contextCaptured, selected, framed, caller, environment, Helper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, contextValue, premiseValue,
              Base.patternsValue, assignmentValue, quantifiedEventsValue, collectionValue, Base.stringValue,
              Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return Base.runtime contextual state _ templated

/-- Returning from one quantified body resumes the original enclosing
assignment. The complete body event remains in the retained history. -/
theorem delivered_element_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
    (localTyped : GeneralPremise.TypedAssignment env context.quantified
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial))
    (tail : Continuation env (.quantified context parameter body index (element :: elements) initial) outer)
    (result : Result env (.premise context.quantified body
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial))) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result,
        continuationValue (.element context parameter body index element elements initial localTyped tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.element context parameter body index element elements initial localTyped tail))) := by
  cases result with
  | premise assignment event valid =>
      change PureReturns Base.runtime [] state
        (Base.a "gslt:premise:machine-deliver" [resultValue (.premise assignment event valid),
          continuationValue (.element context parameter body index element elements initial localTyped tail)]) state
        (expansionValue (env := env) (outer := outer)
          { tasks := [.evaluate
              (.quantified context parameter body (index + 1) elements
                initial)
              (.prependElement context parameter body index element elements initial assignment
                event localTyped valid tail)] })
      let result : Result env (.premise context.quantified body
          (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial)) :=
        .premise assignment event valid
      let caller := environment .deliver [resultValue result,
        continuationValue (.element context parameter body index element elements initial localTyped tail)]
      let framed := [("tail", continuationValue tail), ("initial", assignmentValue initial),
        ("elements", Base.patternsValue elements), ("element", Base.patternValue element), ("index", Base.number index),
        ("body", premiseValue body), ("parameter", Base.stringValue parameter), ("context", contextValue context)] ++ caller
      let selected := [("event", eventValue event), ("assignment", assignmentValue assignment),
        ("goal", goalValue (.premise context.quantified body
          (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial)))] ++ framed
      let restored := ("restored", assignmentValue initial) :: selected
      let bound := ("next", Base.number (index + 1)) :: restored
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.element context parameter body index element elements initial localTyped tail)) deliverCases
        (Base.caseData (Base.v "result") deliverElementCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, contextValue, premiseValue,
          Base.patternsValue, Base.patternValue, Base.number, assignmentValue, Base.stringValue, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverElementCases deliverElementBody _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverElementCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, assignmentValue, eventValue, Subst.lookup]
        · apply PureData.let_bindings_return (pairs := [
            (Base.v "restored", Base.v "initial"),
            (Base.v "next", Base.a "+" [Base.v "index", Base.number 1])]) (final := bound) (middle := state)
            _ state deliverElementData _ _
          · apply PureData.BindingsReturn.cons (bound := restored) (middle := state)
              (value := assignmentValue initial)
            · simpa [selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
                variable_returns Base.runtime selected state "initial"
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                restored, selected, framed, caller, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := bound) (middle := state)
                (value := Base.number (index + 1))
              · exact Base.add_one_returns restored state index "index" (by
                  simp [restored, selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  bound, restored, selected, framed, caller, environment, Helper.names, Subst.lookup]
              · exact .nil bound state
          · have templated : PureData.Template Base.runtime deliverElementData := by
              unfold deliverElementData
              machine_template
            simpa [deliverElementData, result, expansionValue, expansionTerm, GeneralPremise.Execution.delivered,
              taskTerm, continuationTerm, goalTerm, encodeOption, encodeList, bound, restored,
              selected, framed, caller, environment, Helper.names, applySubst,
              applySubst.applySubstList, Subst.lookup, contextValue, premiseValue, Base.patternsValue,
              Base.patternValue, assignmentValue, eventValue, Base.stringValue, Base.number,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return Base.runtime bound state _ templated

#print axioms delivered_quantifier_returns
#print axioms delivered_element_returns

/-- Quantified element histories preserve the original occurrence index,
raw element and its one body event before the ordered remainder. -/
theorem delivered_prepend_element_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (element : Pattern) (elements : List Pattern) (initial middle : Assignment)
    (event : GeneralPremise.Event)
    (localTyped : GeneralPremise.TypedAssignment env context.quantified
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial))
    (head : GeneralPremise.PremiseHolds env context.quantified body
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial) middle event)
    (tail : Continuation env (.quantified context parameter body index (element :: elements) initial) outer)
    (result : Result env (.quantified context parameter body (index + 1) elements
      initial)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result,
        continuationValue (.prependElement context parameter body index element elements initial middle
          event localTyped head tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.prependElement context parameter body index element elements initial middle event localTyped head tail))) := by
  cases result with
  | quantified assignment events valid =>
      change PureReturns Base.runtime [] state
        (Base.a "gslt:premise:machine-deliver" [resultValue (.quantified assignment events valid),
          continuationValue (.prependElement context parameter body index element elements initial middle
            event localTyped head tail)]) state
        (expansionValue (env := env) (outer := outer)
          { tasks := [.deliver (.quantified assignment ((index, element, [event]) :: events)
              (.cons localTyped head valid)) tail] })
      let result : Result env (.quantified context parameter body (index + 1) elements
          initial) := .quantified assignment events valid
      let caller := environment .deliver [resultValue result,
        continuationValue (.prependElement context parameter body index element elements initial middle
          event localTyped head tail)]
      let framed := [("tail", continuationValue tail), ("event", eventValue event),
        ("middle", assignmentValue middle), ("initial", assignmentValue initial),
        ("elements", Base.patternsValue elements), ("element", Base.patternValue element), ("index", Base.number index),
        ("body", premiseValue body), ("parameter", Base.stringValue parameter), ("context", contextValue context)] ++ caller
      let selected := [("events", quantifiedEventsValue events), ("assignment", assignmentValue assignment),
        ("goal", goalValue (.quantified context parameter body (index + 1) elements
          initial))] ++ framed
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.prependElement context parameter body index element elements initial middle
          event localTyped head tail)) deliverCases (Base.caseData (Base.v "result") deliverPrependElementCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, contextValue, premiseValue,
          Base.patternsValue, Base.patternValue, Base.number, assignmentValue, eventValue, Base.stringValue, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverPrependElementCases deliverPrependElementData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverPrependElementCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, assignmentValue, quantifiedEventsValue, Subst.lookup]
        · have templated : PureData.Template Base.runtime deliverPrependElementData := by
            unfold deliverPrependElementData
            machine_template
          simpa [deliverPrependElementData, expansionValue, expansionTerm, taskTerm, resultTerm,
            goalTerm, encodeOption, encodeList, eventsTerm, quantifiedEventsTerm, selected, framed,
            caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            contextValue, premiseValue, Base.patternsValue, Base.patternsTerm, InferenceCettaWire.encodePatterns,
            Base.patternValue, assignmentValue, eventValue, quantifiedEventsValue, Base.stringValue, Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime selected state _ templated

private abbrev traceValue (trace : List GeneralScopedMatchMachine.BagChoice) : Atom := Base.encoded (traceTerm trace)

/-- A child root result is retained with its original declaration index,
captured and completed assignments, trace and premise history. -/
theorem delivered_searched_root_returns (state : State) (env : Environment) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index limit : Nat)
    (earlier : index < limit)
    (tail : Continuation env (.steps bound type source limit) outer)
    (result : Result env (.root bound type source index)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result,
        continuationValue (.searchedRoot bound type source index limit earlier tail)]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result
        (.searchedRoot bound type source index limit earlier tail))) := by
  cases result with
  | root trace captured completed events target valid =>
      change PureReturns Base.runtime [] state
        (Base.a "gslt:premise:machine-deliver" [resultValue (.root trace captured completed events target valid),
          continuationValue (.searchedRoot bound type source index limit earlier tail)]) state
        (expansionValue (env := env) (outer := outer)
          { tasks := [.deliver (.steps index trace captured completed events target earlier valid) tail] })
      let result : Result env (.root bound type source index) := .root trace captured completed events target valid
      let caller := environment .deliver [resultValue result,
        continuationValue (.searchedRoot bound type source index limit earlier tail)]
      let framed := [("tail", continuationValue tail), ("limit", Base.number limit), ("index", Base.number index),
        ("source", Base.patternValue source), ("type", Base.typeValue type), ("bound", Base.boundValue bound)] ++ caller
      let selected := [("target", Base.patternValue target), ("events", eventsValue events),
        ("completed", assignmentValue completed), ("captured", assignmentValue captured),
        ("trace", traceValue trace), ("goal", goalValue (.root bound type source index))] ++ framed
      apply helper_call .deliver [] state _ _ _ rfl (Base.captured_closed _)
      rw [deliver_shape]
      apply Base.branch_returns caller framed state _
        (continuationValue (.searchedRoot bound type source index limit earlier tail)) deliverCases
        (Base.caseData (Base.v "result") deliverSearchedRootCases) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "continuation"
      · simp [deliverCases, continuationValue, continuationTerm, framed, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Base.boundValue, Base.typeValue, Base.patternValue,
          Base.number, Subst.lookup]
      · apply Base.branch_returns framed selected state _ (resultValue result)
          deliverSearchedRootCases deliverSearchedRootData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime framed state "result"
        · simp [deliverSearchedRootCases, resultValue, result, resultTerm, selected, framed, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, goalValue, Base.patternValue, assignmentValue, eventsValue, traceValue, Subst.lookup]
        · have templated : PureData.Template Base.runtime deliverSearchedRootData := by
            unfold deliverSearchedRootData
            machine_template
          simpa [deliverSearchedRootData, expansionValue, expansionTerm, taskTerm, resultTerm,
            goalTerm, encodeOption, encodeList, selected, framed, caller, environment, Helper.names,
            applySubst, applySubst.applySubstList, Subst.lookup, Base.boundValue, Base.typeValue, Base.patternValue,
            assignmentValue, eventsValue, traceValue, Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime selected state _ templated

#print axioms delivered_prepend_element_returns
#print axioms delivered_searched_root_returns

private def evaluatePremisesNilData : Atom :=
  Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseDeliver" [Base.a "PremiseResult" [Base.v "goal", Base.a "PremisesAnswer" [Base.v "initial", .symbol "LNil"]], Base.v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def evaluatePremisesConsData : Atom :=
  Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseEvaluate" [Base.a "PremiseGoal" [Base.v "context", Base.v "premise", Base.v "initial"], Base.a "PremiseNext" [Base.v "context", Base.v "premise", Base.v "rest", Base.v "initial", Base.v "continuation"]], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def evaluateQuantifiedNilData : Atom :=
  Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseDeliver" [Base.a "PremiseResult" [Base.v "goal", Base.a "QuantifiedAnswer" [Base.v "initial", .symbol "LNil"]], Base.v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def evaluateQuantifiedConsBody : Atom :=
  Base.a "let*" [.expression [.expression [Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"]], .expression [Base.v "local", Base.a "gslt:premise:scope-local-value" [Base.v "ambient", Base.v "element"]], .expression [Base.v "assignment", Base.a "gslt:premise:scope-bind" [Base.v "parameter", Base.v "local", Base.v "initial"]], .expression [Base.v "quantified", Base.a "gslt:premise:context-quantified" [Base.v "context"]]], Base.a "if" [Base.a "gslt:premise:check-assignment" [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "rule", Base.v "spec", Base.v "assignment"], Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseEvaluate" [Base.a "PremiseGoal" [Base.v "quantified", Base.v "body", Base.v "assignment"], Base.a "PremiseElement" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "element", Base.v "rest", Base.v "initial", Base.v "continuation"]], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]], Base.a "Some" [Base.a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", Base.a "LCons" [Base.a "PremiseQuantifiedAssignment" [Base.v "premise", Base.v "quantifiers", Base.v "index"], .symbol "LNil"]]]]]

private def evaluateForAllBody : Atom :=
  Base.a "let" [Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"], Base.a "case" [Base.a "gslt:premise:scope-collection" [Base.v "ambient", Base.v "initial", Base.v "collection"], .expression [Base.a "None" [Base.a "Some" [Base.a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", Base.a "LCons" [Base.a "PremiseCollectionProjection" [Base.v "premise", Base.v "quantifiers", Base.v "collection"], .symbol "LNil"]]]], .expression [Base.a "Some" [Base.a "FiniteCollection" [Base.v "kind", Base.v "elements"]], Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseEvaluate" [Base.a "QuantifiedGoal" [Base.v "context", Base.v "parameter", Base.v "body", Base.number 0, Base.v "elements", Base.v "initial"], Base.a "PremiseQuantifier" [Base.v "context", Base.v "collection", Base.v "parameter", Base.v "body", Base.v "initial", Base.v "kind", Base.v "elements", Base.v "continuation"]], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]]]]]

private def evaluateStepsData : Atom :=
  Base.a "Some" [Base.a "PremiseExpansion" [Base.a "LCons" [Base.a "PremiseScanChildren" [Base.v "bound", Base.v "type", Base.v "source", Base.v "limit", Base.number 0, Base.v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def evaluatePremisesCases : SpaceSemantics.Cases :=
  [( .symbol "LNil", evaluatePremisesNilData),
    (Base.a "LCons" [Base.v "premise", Base.v "rest"], evaluatePremisesConsData), (Base.v "badPremises", .symbol "None")]

private def evaluateQuantifiedContextCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseContext" [Base.v "ruleIndex", Base.v "rule", Base.v "spec", Base.v "bound", Base.v "premise", Base.v "quantifiers"], evaluateQuantifiedConsBody), (Base.v "badContext", .symbol "None")]

private def evaluateQuantifiedCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", evaluateQuantifiedNilData),
    (Base.a "LCons" [Base.v "element", Base.v "rest"], Base.caseData (Base.v "context") evaluateQuantifiedContextCases),
    (Base.v "badElements", .symbol "None")]

private def evaluateForAllContextCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseContext" [Base.v "index", Base.v "rule", Base.v "spec", Base.v "bound", Base.v "premise", Base.v "quantifiers"], evaluateForAllBody), (Base.v "badContext", .symbol "None")]

private def evaluateCases : SpaceSemantics.Cases :=
  [(Base.a "PremisesGoal" [Base.v "context", Base.v "premises", Base.v "initial"], Base.caseData (Base.v "premises") evaluatePremisesCases),
    (Base.a "QuantifiedGoal" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "elements", Base.v "initial"], Base.caseData (Base.v "elements") evaluateQuantifiedCases),
    (Base.a "PremiseGoal" [Base.v "context", Base.a "ForAll" [Base.v "collection", Base.v "parameter", Base.v "body"], Base.v "initial"], Base.caseData (Base.v "context") evaluateForAllContextCases),
    (Base.a "StepsGoal" [Base.v "bound", Base.v "type", Base.v "source", Base.v "limit"], evaluateStepsData), (Base.v "unsupported", .symbol "None")]

private theorem evaluate_shape : (equation .evaluate).body = Base.caseData (Base.v "goal") evaluateCases := by
  decide +kernel

/-- The ordered premise-list transition enters precisely its first premise,
or schedules the original empty-list result. -/
theorem evaluate_premises_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (premises : List Premise) (initial : Assignment)
    (tail : Continuation env (.premises context premises initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue [],
        goalValue (.premises context premises initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer (.premises context premises initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue [],
    goalValue (.premises context premises initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("premises", premisesValue premises),
    ("context", contextValue context)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.premises context premises initial))
    evaluateCases (Base.caseData (Base.v "premises") evaluatePremisesCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, premisesValue,
      contextValue, Subst.lookup]
  · cases premises with
    | nil =>
        apply Base.branch_returns framed framed state _ (.symbol "LNil") evaluatePremisesCases evaluatePremisesNilData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, premisesValue,
            encodeList, CettaWireAtom.encode] using variable_returns Base.runtime framed state "premises"
        · simp [evaluatePremisesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · have templated : PureData.Template Base.runtime evaluatePremisesNilData := by
            unfold evaluatePremisesNilData
            machine_template
          simpa [evaluatePremisesNilData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
            taskTerm, resultTerm, goalTerm, eventsTerm, encodeOption, encodeList, framed, caller, environment,
            Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, assignmentValue,
            goalValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime framed state _ templated
    | cons premise premises =>
        let selected := [("rest", premisesValue premises), ("premise", premiseValue premise)] ++ framed
        apply Base.branch_returns framed selected state _
          (Base.a "LCons" [premiseValue premise, premisesValue premises]) evaluatePremisesCases evaluatePremisesConsData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, premisesValue,
            premiseValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            variable_returns Base.runtime framed state "premises"
        · simp [evaluatePremisesCases, selected, framed, caller, environment, Helper.names,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · have templated : PureData.Template Base.runtime evaluatePremisesConsData := by
            unfold evaluatePremisesConsData
            machine_template
          simpa [evaluatePremisesConsData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
            taskTerm, continuationTerm, goalTerm, encodeOption, encodeList, selected, framed, caller,
            environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            assignmentValue, premisesValue, premiseValue, contextValue,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime selected state _ templated

/-- An empty quantified collection schedules its independently certified
empty result; the surrounding quantifier continuation remains suspended. -/
theorem evaluate_quantified_nil_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (initial : Assignment)
    (tail : Continuation env (.quantified context parameter body index [] initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue [],
        goalValue (.quantified context parameter body index [] initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.quantified context parameter body index [] initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue [],
    goalValue (.quantified context parameter body index [] initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("elements", Base.patternsValue []), ("index", Base.number index),
    ("body", premiseValue body), ("parameter", Base.stringValue parameter), ("context", contextValue context)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.quantified context parameter body index [] initial))
    evaluateCases (Base.caseData (Base.v "elements") evaluateQuantifiedCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, Base.patternsValue,
      premiseValue, contextValue, Base.number, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed framed state _ (.symbol "LNil") evaluateQuantifiedCases evaluateQuantifiedNilData _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, Base.patternsValue,
        Base.patternsTerm, InferenceCettaWire.encodePatterns, encodeList, CettaWireAtom.encode] using
        variable_returns Base.runtime framed state "elements"
    · simp [evaluateQuantifiedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · have templated : PureData.Template Base.runtime evaluateQuantifiedNilData := by
        unfold evaluateQuantifiedNilData
        machine_template
      simpa [evaluateQuantifiedNilData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
        taskTerm, resultTerm, goalTerm, encodeOption, encodeList, quantifiedEventsTerm, framed, caller,
        environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
        assignmentValue, goalValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return Base.runtime framed state _ templated

/-- A child search starts at declaration position zero while retaining its
actual caller limit and typed root inputs. -/
theorem evaluate_steps_returns (state : State) (env : Environment) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Continuation env (.steps bound type source limit) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue [],
        goalValue (.steps bound type source limit), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer (.steps bound type source limit) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue [],
    goalValue (.steps bound type source limit), continuationValue tail]
  let framed := [("limit", Base.number limit), ("source", Base.patternValue source),
    ("type", Base.typeValue type), ("bound", Base.boundValue bound)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.steps bound type source limit))
    evaluateCases evaluateStepsData _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Base.boundValue, Base.typeValue,
      Base.patternValue, Base.number, Subst.lookup]
  · have templated : PureData.Template Base.runtime evaluateStepsData := by
      unfold evaluateStepsData
      machine_template
    simpa [evaluateStepsData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
      taskTerm, goalTerm, encodeOption, encodeList, framed, caller, environment, Helper.names,
      applySubst, applySubst.applySubstList, Subst.lookup, Base.boundValue, Base.typeValue, Base.patternValue,
      Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return Base.runtime framed state _ templated

#print axioms evaluate_premises_returns
#print axioms evaluate_quantified_nil_returns
#print axioms evaluate_steps_returns

private abbrev contextualValueValue (value : ContextualValue) : Atom :=
  Base.encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value)

private def evaluateQuantifiedAcceptedData : Atom := tasksData
  (Base.a "PremiseEvaluate" [Base.a "PremiseGoal" [Base.v "quantified", Base.v "body", Base.v "assignment"],
    Base.a "PremiseElement" [Base.v "context", Base.v "parameter", Base.v "body", Base.v "index", Base.v "element",
      Base.v "rest", Base.v "initial", Base.v "continuation"]])
private def evaluateQuantifiedRejectedData : Atom :=
  expansionData (.symbol "LNil") (.symbol "LNil")
    (singletonData (Base.a "PremiseQuantifiedAssignment" [Base.v "premise", Base.v "quantifiers", Base.v "index"]))
private def evaluateQuantifiedCheckData : Atom :=
  Base.a "if" [Base.a "gslt:premise:check-assignment"
    [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "rule", Base.v "spec", Base.v "assignment"],
    evaluateQuantifiedAcceptedData, evaluateQuantifiedRejectedData]

private theorem quantified_cons_shape : evaluateQuantifiedConsBody =
    Base.a "let*" [.expression [
      .expression [Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"]],
      .expression [Base.v "local", Base.a "gslt:premise:scope-local-value" [Base.v "ambient", Base.v "element"]],
      .expression [Base.v "assignment", Base.a "gslt:premise:scope-bind" [Base.v "parameter", Base.v "local", Base.v "initial"]],
      .expression [Base.v "quantified", Base.a "gslt:premise:context-quantified" [Base.v "context"]]],
      evaluateQuantifiedCheckData] := by decide +kernel

/-- Entering a quantified body validates every retained capture, including
its newly bound element. A failed check records the original obligation. -/
theorem evaluate_quantified_cons_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
    (tail : Continuation env (.quantified context parameter body index (element :: elements) initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language,
        Base.freeValue (evaluationFreeContext env (.quantified context parameter body index (element :: elements) initial)),
        goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.quantified context parameter body index (element :: elements) initial) tail)) := by
  let assignment := GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial
  let caller := environment .evaluate [Base.declarationsValue env.language,
    Base.freeValue (assignmentFreeContext env assignment),
    goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("elements", Base.patternsValue (element :: elements)),
    ("index", Base.number index), ("body", premiseValue body), ("parameter", Base.stringValue parameter),
    ("context", contextValue context)] ++ caller
  let selected := [("rest", Base.patternsValue elements), ("element", Base.patternValue element)] ++ framed
  let contextual := [("quantifiers", Base.number context.quantifierDepth), ("premise", Base.number context.premiseIndex),
    ("bound", Base.boundValue context.bound), ("spec", Base.specValue context.spec), ("rule", Base.ruleValue context.rule),
    ("ruleIndex", Base.number context.ruleIndex)] ++ selected
  let ambient := ("ambient", Base.number context.bound.length) :: contextual
  let localized := ("local", contextualValueValue (GeneralPremise.localValue context.bound element)) :: ambient
  let assigned := ("assignment", assignmentValue assignment) :: localized
  let quantified := ("quantified", contextValue context.quantified) :: assigned
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _
    (goalValue (.quantified context parameter body index (element :: elements) initial))
    evaluateCases (Base.caseData (Base.v "elements") evaluateQuantifiedCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, Base.patternsValue,
      premiseValue, contextValue, Base.number, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed selected state _
      (Base.a "LCons" [Base.patternValue element, Base.patternsValue elements]) evaluateQuantifiedCases
      (Base.caseData (Base.v "context") evaluateQuantifiedContextCases) _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, Base.patternsValue,
        Base.patternsTerm, InferenceCettaWire.encodePatterns, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany] using variable_returns Base.runtime framed state "elements"
    · simp [evaluateQuantifiedCases, selected, framed, caller, environment, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup]
    · apply Base.branch_returns selected contextual state _ (contextValue context)
        evaluateQuantifiedContextCases evaluateQuantifiedConsBody _
      · simpa [selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime selected state "context"
      · simp [evaluateQuantifiedContextCases, contextual, selected, framed, caller, environment, Helper.names,
          contextValue, contextTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Base.number, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, Subst.lookup]
      · rw [quantified_cons_shape]
        apply PureData.let_bindings_return (pairs := [
          (Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"]),
          (Base.v "local", Base.a "gslt:premise:scope-local-value" [Base.v "ambient", Base.v "element"]),
          (Base.v "assignment", Base.a "gslt:premise:scope-bind" [Base.v "parameter", Base.v "local", Base.v "initial"]),
          (Base.v "quantified", Base.a "gslt:premise:context-quantified" [Base.v "context"])])
          (final := quantified) (middle := state) _ state evaluateQuantifiedCheckData _ _
        · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state) (value := Base.number context.bound.length)
          · exact assignment_length_returns contextual state context.bound (by
              simp [contextual, selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := localized) (middle := state)
              (value := contextualValueValue (GeneralPremise.localValue context.bound element))
            · exact Base.previous_returns (by decide +kernel)
                (QuantifiedLocal.local_value_captured_returns ambient state context.bound element
                  (Base.v "ambient") (Base.v "element") (by
                    simp [ambient, contextual, selected, framed, caller, environment, Helper.names,
                      applySubst, Subst.lookup]))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                localized, ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := assigned) (middle := state)
                (value := assignmentValue assignment)
              · exact Base.previous_returns (by decide +kernel)
                  (QuantifiedLocal.bind_parameter_captured_returns localized state parameter
                    (GeneralPremise.localValue context.bound element) initial
                    (Base.v "parameter") (Base.v "local") (Base.v "initial") (by
                      simp [localized, ambient, contextual, selected, framed, caller, environment, Helper.names,
                        applySubst, Subst.lookup]))
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  assigned, localized, ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := quantified) (middle := state)
                  (value := contextValue context.quantified)
                · exact context_quantified_captured_returns assigned state context (Base.v "context") (by
                    simp [assigned, localized, ambient, contextual, selected, framed, caller,
                      environment, Helper.names, applySubst, Subst.lookup])
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    quantified, assigned, localized, ambient, contextual, selected, framed, caller,
                    environment, Helper.names, Subst.lookup]
                · exact .nil quantified state
        · unfold evaluateQuantifiedCheckData
          apply Base.bool_if_returns quantified state _
            (GeneralPremise.checkTypedAssignment env context.quantified assignment)
            evaluateQuantifiedAcceptedData evaluateQuantifiedRejectedData _
          · exact check_typed_assignment_captured_returns quantified state env context.quantified assignment
              (Base.v "declarations") (Base.v "free") (Base.v "bound") (Base.v "rule") (Base.v "spec") (Base.v "assignment") (by
                simp [GeneralPremise.Context.quantified, quantified, assigned, localized, ambient, contextual,
                  selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
          · cases checked : GeneralPremise.checkTypedAssignment env context.quantified assignment with
            | false =>
                have templated : PureData.Template Base.runtime evaluateQuantifiedRejectedData := by
                  unfold evaluateQuantifiedRejectedData
                  machine_template
                simpa [checked, evaluateQuantifiedRejectedData, expansionValue, expansionTerm,
                  GeneralPremise.Execution.evaluate, assignment, encodeOption, encodeList, obligationTerm,
                  quantified, assigned, localized, ambient, contextual, selected, framed, caller,
                  environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                  Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return Base.runtime quantified state _ templated
            | true =>
                have templated : PureData.Template Base.runtime evaluateQuantifiedAcceptedData := by
                  unfold evaluateQuantifiedAcceptedData
                  machine_template
                simpa [checked, evaluateQuantifiedAcceptedData, expansionValue, expansionTerm,
                  GeneralPremise.Execution.evaluate, taskTerm, continuationTerm, goalTerm, assignment,
                  encodeOption, encodeList, quantified, assigned, localized, ambient, contextual, selected,
                  framed, caller, environment, Helper.names, applySubst, applySubst.applySubstList,
                  Subst.lookup, assignmentValue, contextValue, premiseValue, Base.patternsValue, Base.patternValue,
                  Base.stringValue, Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return Base.runtime quantified state _ templated

#print axioms evaluate_quantified_cons_returns

private def evaluateForAllNoneData : Atom :=
  expansionData (.symbol "LNil") (.symbol "LNil")
    (singletonData (Base.a "PremiseCollectionProjection" [Base.v "premise", Base.v "quantifiers", Base.v "collection"]))
private def evaluateForAllSomeData : Atom := tasksData
  (Base.a "PremiseEvaluate" [Base.a "QuantifiedGoal"
    [Base.v "context", Base.v "parameter", Base.v "body", Base.number 0, Base.v "elements", Base.v "initial"],
    Base.a "PremiseQuantifier" [Base.v "context", Base.v "collection", Base.v "parameter", Base.v "body",
      Base.v "initial", Base.v "kind", Base.v "elements", Base.v "continuation"]])
private def evaluateForAllCollectionCases : SpaceSemantics.Cases :=
  [(.symbol "None", evaluateForAllNoneData),
    (Base.a "Some" [Base.a "FiniteCollection" [Base.v "kind", Base.v "elements"]], evaluateForAllSomeData)]
private theorem forall_body_shape : evaluateForAllBody =
    Base.a "let" [Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"],
      Base.caseData (Base.a "gslt:premise:scope-collection" [Base.v "ambient", Base.v "initial", Base.v "collection"])
        evaluateForAllCollectionCases] := by decide +kernel

private theorem evaluate_forall_none_eq (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise)
    (initial : Assignment)
    (tail : Continuation env (.premise context (.forAll collection parameter body) initial) outer)
    (found : GeneralPremise.finiteCollection? context.bound.length initial collection = none) :
    GeneralPremise.Execution.evaluate env outer (.premise context (.forAll collection parameter body) initial) tail =
      { unresolved := [.collectionProjection context.premiseIndex context.quantifierDepth collection] } := by
  change ((match read : GeneralPremise.finiteCollection? context.bound.length initial collection with
    | none => { unresolved := [.collectionProjection context.premiseIndex context.quantifierDepth collection] }
    | some (kind, elements) =>
        { tasks := [.evaluate (.quantified context parameter body 0 elements initial)
            (.quantifier context collection parameter body initial kind elements read tail)] }) :
      GeneralPremise.Scheduler.Expansion (Task env outer) (Result env outer) Obligation) = _
  split <;> simp_all

private theorem evaluate_forall_some_eq (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise)
    (initial : Assignment) (kind : CollType) (elements : List Pattern)
    (tail : Continuation env (.premise context (.forAll collection parameter body) initial) outer)
    (found : GeneralPremise.finiteCollection? context.bound.length initial collection = some (kind, elements)) :
    GeneralPremise.Execution.evaluate env outer (.premise context (.forAll collection parameter body) initial) tail =
      { tasks := [.evaluate (.quantified context parameter body 0 elements initial)
          (.quantifier context collection parameter body initial kind elements found tail)] } := by
  change ((match read : GeneralPremise.finiteCollection? context.bound.length initial collection with
    | none => { unresolved := [.collectionProjection context.premiseIndex context.quantifierDepth collection] }
    | some (kind, elements) =>
        { tasks := [.evaluate (.quantified context parameter body 0 elements initial)
            (.quantifier context collection parameter body initial kind elements read tail)] }) :
      GeneralPremise.Scheduler.Expansion (Task env outer) (Result env outer) Obligation) = _
  split
  · simp_all
  · rename_i actualKind actualElements actualFound
    have same := Option.some.inj (actualFound.symm.trans found)
    have sameKind := congrArg Prod.fst same
    have sameElements := congrArg Prod.snd same
    dsimp only at sameKind sameElements
    subst actualKind actualElements
    rfl

/-- A quantified premise reads the retained concrete collection without
inventing elements or interpreting an unavailable residual as empty. -/
theorem evaluate_forall_returns (state : State) (env : Environment) (outer : Goal)
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise)
    (initial : Assignment)
    (tail : Continuation env (.premise context (.forAll collection parameter body) initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue [],
        goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.premise context (.forAll collection parameter body) initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue [],
    goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("body", premiseValue body),
    ("parameter", Base.stringValue parameter), ("collection", Base.stringValue collection), ("context", contextValue context)] ++ caller
  let contextual := contextCaptured context framed
  let ambient := ("ambient", Base.number context.bound.length) :: contextual
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _
    (goalValue (.premise context (.forAll collection parameter body) initial))
    evaluateCases (Base.caseData (Base.v "context") evaluateForAllContextCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, InferenceCettaWire.AuthoredRule.premiseTerm,
      framed, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      assignmentValue, premiseValue, contextValue, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed contextual state _ (contextValue context)
      evaluateForAllContextCases evaluateForAllBody _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns Base.runtime framed state "context"
    · simp [evaluateForAllContextCases, contextual, contextCaptured, framed, caller, environment, Helper.names,
        contextValue, contextTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Base.number, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, Subst.lookup]
    · rw [forall_body_shape]
      apply let_returns Base.runtime contextual ambient state state state (Base.v "ambient")
        (Base.a "gslt:automata:length" [Base.v "bound"])
        (Base.caseData (Base.a "gslt:premise:scope-collection" [Base.v "ambient", Base.v "initial", Base.v "collection"])
          evaluateForAllCollectionCases) (Base.number context.bound.length) _
      · exact assignment_length_returns contextual state context.bound (by
          simp [contextual, contextCaptured, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, contextual, contextCaptured, framed, caller, environment, Helper.names, Subst.lookup]
      · have collectionReturned := Base.previous_returns (by decide +kernel)
          (QuantifiedLocal.finite_collection_captured_returns ambient state context.bound.length initial collection
            (Base.v "ambient") (Base.v "initial") (Base.v "collection") (by
              simp [ambient, contextual, contextCaptured, framed, caller, environment, Helper.names,
                applySubst, Subst.lookup]))
        cases found : GeneralPremise.finiteCollection? context.bound.length initial collection with
        | none =>
            apply Base.branch_returns ambient ambient state _ (.symbol "None")
              evaluateForAllCollectionCases evaluateForAllNoneData _
            · simpa only [found, QuantifiedLocal.finiteCollectionOptionTerm, encodeOption, CettaWireAtom.encode] using collectionReturned
            · simp [evaluateForAllCollectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · rw [evaluate_forall_none_eq env outer context collection parameter body initial tail found]
              have templated : PureData.Template Base.runtime evaluateForAllNoneData := by
                unfold evaluateForAllNoneData
                machine_template
              simpa [evaluateForAllNoneData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
                GeneralPremise.Execution.evaluatePremise, found, encodeOption, encodeList, obligationTerm,
                ambient, contextual, contextCaptured, framed, caller, environment, Helper.names,
                applySubst, applySubst.applySubstList, Subst.lookup, Base.stringValue, Base.number,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return Base.runtime ambient state _ templated
        | some value =>
            rcases value with ⟨kind, elements⟩
            let selected := [("elements", Base.patternsValue elements), ("kind", collectionValue kind)] ++ ambient
            apply Base.branch_returns ambient selected state _
              (Base.a "Some" [Base.a "FiniteCollection" [collectionValue kind, Base.patternsValue elements]])
              evaluateForAllCollectionCases evaluateForAllSomeData _
            · simpa only [found, QuantifiedLocal.finiteCollectionOptionTerm, encodeOption, CettaWireAtom.encode,
                CettaWireAtom.encodeMany] using collectionReturned
            · simp [evaluateForAllCollectionCases, selected, ambient, contextual, contextCaptured,
                framed, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · rw [evaluate_forall_some_eq env outer context collection parameter body initial kind elements tail found]
              have templated : PureData.Template Base.runtime evaluateForAllSomeData := by
                unfold evaluateForAllSomeData
                machine_template
              simpa [evaluateForAllSomeData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
                GeneralPremise.Execution.evaluatePremise, found, taskTerm, continuationTerm, goalTerm,
                encodeOption, encodeList, selected, ambient, contextual, contextCaptured, framed, caller,
                environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                contextValue, assignmentValue, premiseValue, Base.patternsValue, collectionValue, Base.stringValue,
                Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return Base.runtime selected state _ templated

#print axioms evaluate_forall_returns

def providerRowTerm (row : GeneralPremise.ProviderRow) : Term :=
  .application "PremiseProviderRow" [.string row.relation, Base.patternsTerm row.values]

def providerTerm (provider : GeneralPremise.ProviderSnapshot) : Term :=
  .application "PremiseProvider" [encodeList signatureTerm provider.signatures,
    encodeList providerRowTerm provider.rows]

def specificationTerm (specification : Nat × RuleBindingSpec) : Term :=
  .application "PremiseSpecification" [.natural specification.1,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm specification.2]

def reflectiveRuleTerm (declaration : ReflectiveRuleDecl) : Term :=
  .application "ReflectiveRule" [.string declaration.name, .string declaration.rewriteRule,
    .string declaration.matchingPresentation, .string declaration.substitutionPresentation]

def reflectionTerm (profile : Reflection.ReflectionProfile) : Term :=
  .application "PremiseReflection" [encodeList InferenceCettaWire.AuthoredRule.reflectivePresentationTerm profile.presentations,
    encodeList reflectiveRuleTerm profile.rules]

/-- Finite operational environment data. The free lookup list is supplied
explicitly, so each execution theorem can state its earned footprint. -/
def environmentTerm (environment : Environment) (free : List (String × TypeExpr)) : Term :=
  .application "PremiseEnvironment"
    [encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm environment.language.terms,
     encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites,
     encodeList specificationTerm environment.specifications, providerTerm environment.provider,
     reflectionTerm environment.reflection,
     DeclarationTyping.freeContextTerm free]

private def scanNextData : Atom := expansionData
  (Base.a "LCons" [Base.a "PremiseEvaluate" [Base.a "RootGoal" [Base.v "bound", Base.v "type", Base.v "source", Base.v "cursor"],
    Base.a "PremiseSearchedRoot" [Base.v "bound", Base.v "type", Base.v "source", Base.v "cursor", Base.v "limit", Base.v "continuation"]],
    singletonData (Base.a "PremiseScanChildren"
      [Base.v "bound", Base.v "type", Base.v "source", Base.v "limit", Base.v "next", Base.v "continuation"])])
  (.symbol "LNil") (.symbol "LNil")
private def scanEmptyData : Atom := expansionData (.symbol "LNil") (.symbol "LNil") (.symbol "LNil")
private def scanNextBody : Atom := Base.a "let" [Base.v "next", Base.a "+" [Base.v "cursor", Base.number 1], scanNextData]
private def scanBody : Atom := Base.a "if" [Base.a "<" [Base.v "cursor", Base.v "limit"], scanNextBody, scanEmptyData]
private def expandCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseEvaluate" [Base.v "goal", Base.v "continuation"],
      Base.a "gslt:premise:machine-evaluate" [Base.v "declarations", Base.v "free", Base.v "goal", Base.v "continuation"]),
    (Base.a "PremiseDeliver" [Base.v "result", Base.v "continuation"],
      Base.a "gslt:premise:machine-deliver" [Base.v "result", Base.v "continuation"]),
    (Base.a "PremiseScanChildren" [Base.v "bound", Base.v "type", Base.v "source", Base.v "limit", Base.v "cursor", Base.v "continuation"], scanBody),
    (Base.v "unsupported", .symbol "None")]
private theorem expand_shape : (equation .expand).body = Base.caseData (Base.v "task") expandCases := by decide +kernel

private theorem natural_lt_returns (caller : Subst) (state : State) (left right : Nat)
    (one two : String)
    (first : applySubst caller (Base.v one) = Base.number left)
    (second : applySubst caller (Base.v two) = Base.number right) :
    PureReturns Base.runtime caller state (Base.a "<" [Base.v one, Base.v two]) state
      (Effects.boolean (left < right)) := by
  apply native_binary_call_returns Base.runtime caller state state state state "<"
    (Base.v one) (Base.v two) (Base.number left) (Base.number right) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [first] using variable_returns Base.runtime caller state one
  · simpa only [second] using variable_returns Base.runtime caller state two
  · have calculated : StdLib.apply state "<"
        [.grounded (.int (left : Int)), .grounded (.int (right : Int))] =
        .ok (state, [Effects.boolean ((left : Int) < (right : Int))]) := rfl
    have order : decide ((left : Int) < (right : Int)) = decide (left < right) := by
      by_cases ordered : left < right
      · have castOrdered : (left : Int) < (right : Int) := by omega
        simp [ordered, castOrdered]
      · have castUnordered : ¬ (left : Int) < (right : Int) := by omega
        simp [ordered, castUnordered]
    simpa only [Base.number, Base.encoded, CettaWireAtom.encode, order] using calculated

/-- Child declarations are visited below the actual caller's index.
Reaching that limit ends only this exhausted scan; earlier positions retain
both the child root request and the continuation of the ordered search. -/
theorem expand_scan_children_returns (state : State) (env : Environment) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Continuation env (.steps bound type source limit) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-expand" [Base.declarationsValue env.language, Base.freeValue [],
        Base.encoded (taskTerm (.scanChildren bound type source limit cursor tail))]) state
      (expansionValue (GeneralPremise.Execution.expand env outer
        (.scanChildren bound type source limit cursor tail))) := by
  let caller := environment .expand [Base.declarationsValue env.language, Base.freeValue [],
    Base.encoded (taskTerm (.scanChildren bound type source limit cursor tail))]
  let framed := [("continuation", continuationValue tail), ("cursor", Base.number cursor), ("limit", Base.number limit),
    ("source", Base.patternValue source), ("type", Base.typeValue type), ("bound", Base.boundValue bound)] ++ caller
  let advanced := ("next", Base.number (cursor + 1)) :: framed
  apply helper_call .expand [] state _ _ _ rfl (Base.captured_closed _)
  rw [expand_shape]
  apply Base.branch_returns caller framed state _
    (Base.encoded (taskTerm (.scanChildren bound type source limit cursor tail))) expandCases scanBody _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "task"
  · simp [expandCases, taskTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Base.boundValue, Base.typeValue,
      Base.patternValue, Base.number, Subst.lookup]
  · unfold scanBody
    apply Base.bool_if_returns framed state _ (decide (cursor < limit)) scanNextBody scanEmptyData _
    · exact natural_lt_returns framed state cursor limit "cursor" "limit"
        (by simp [framed, caller, environment, Helper.names, applySubst, Subst.lookup])
        (by simp [framed, caller, environment, Helper.names, applySubst, Subst.lookup])
    · by_cases earlier : cursor < limit
      · simp only [earlier, decide_true]
        unfold scanNextBody
        apply let_returns Base.runtime framed advanced state state state (Base.v "next")
          (Base.a "+" [Base.v "cursor", Base.number 1]) scanNextData (Base.number (cursor + 1)) _
        · exact Base.add_one_returns framed state cursor "cursor" (by
            simp [framed, caller, environment, Helper.names, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            advanced, framed, caller, environment, Helper.names, Subst.lookup]
        · have templated : PureData.Template Base.runtime scanNextData := by
            unfold scanNextData
            machine_template
          simpa [scanNextData, expansionValue, expansionTerm, GeneralPremise.Execution.expand, earlier,
            taskTerm, continuationTerm, goalTerm, encodeOption, encodeList, advanced, framed, caller,
            environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            Base.boundValue, Base.typeValue, Base.patternValue, Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime advanced state _ templated
      · simp only [earlier, decide_false]
        have templated : PureData.Template Base.runtime scanEmptyData := by
          unfold scanEmptyData
          machine_template
        simpa [scanEmptyData, expansionValue, expansionTerm, GeneralPremise.Execution.expand, earlier,
          encodeOption, encodeList, applySubst, applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return Base.runtime framed state _ templated

#print axioms expand_scan_children_returns

/-- Every administrative continuation is executed by its retained native
source clause. The root-body and child-target continuations remain separate
machine transitions and are excluded by this explicitly stated domain. -/
theorem delivered_administrative_returns (state : State) (env : Environment) (goal outer : Goal)
    (result : Result env goal) (tail : Continuation env goal outer)
    (supported : administrativeContinuation tail = true) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-deliver" [resultValue result, continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.delivered env outer result tail)) := by
  cases tail with
  | done goal => exact delivered_done_returns state env goal result
  | nextPremise context premise premises initial tail =>
      exact delivered_next_returns state env outer context premise premises initial tail result
  | prepend context premise premises initial middle event head tail =>
      exact delivered_prepend_returns state env outer context premise premises initial middle event head tail result
  | quantifier context collection parameter body initial kind elements read tail =>
      exact delivered_quantifier_returns state env outer context collection parameter body initial kind elements read tail result
  | element context parameter body index element elements initial localTyped tail =>
      exact delivered_element_returns state env outer context parameter body index element elements initial localTyped tail result
  | prependElement context parameter body index element elements initial middle event localTyped head tail =>
      exact delivered_prepend_element_returns state env outer context parameter body index element elements initial middle
        event localTyped head tail result
  | rootBody => simp [administrativeContinuation] at supported
  | searchedRoot bound type source index limit earlier tail =>
      exact delivered_searched_root_returns state env outer bound type source index limit earlier tail result
  | stepped => simp [administrativeContinuation] at supported

theorem delivered_administrative_completed_iff (state after : State) (env : Environment) (goal outer : Goal)
    (result : Result env goal) (tail : Continuation env goal outer)
    (supported : administrativeContinuation tail = true) (answers input output : List Atom) :
    (∃ fuel, run Base.runtime fuel {state, control := (.evaluate []
        (Base.a "gslt:premise:machine-deliver" [resultValue result, continuationValue tail]))} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (GeneralPremise.Execution.delivered env outer result tail)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff Base.runtime [] state state _ _
    (delivered_administrative_returns state env goal outer result tail supported) after answers input output

theorem delivered_administrative_derivation_iff (state after : State) (env : Environment) (goal outer : Goal)
    (result : Result env goal) (tail : Continuation env goal outer)
    (supported : administrativeContinuation tail = true) (answers input output : List Atom) :
    DeclarativeSpec.Runs Base.runtime {state, control := (.evaluate []
        (Base.a "gslt:premise:machine-deliver" [resultValue result, continuationValue tail]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (GeneralPremise.Execution.delivered env outer result tail)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff Base.runtime [] state state _ _
    (delivered_administrative_returns state env goal outer result tail supported) after answers input output

#print axioms delivered_administrative_returns
#print axioms delivered_administrative_completed_iff
#print axioms delivered_administrative_derivation_iff

/-- Each supported evaluation branch follows its original dependent goal,
including its exact finite free-context footprint when a local value enters. -/
theorem evaluate_administrative_returns (state : State) (env : Environment) (outer goal : Goal)
    (tail : Continuation env goal outer) (supported : administrativeGoal goal = true) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language,
        Base.freeValue (evaluationFreeContext env goal), goalValue goal, continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer goal tail)) := by
  cases goal with
  | premise context premise initial =>
      cases premise with
      | forAll collection parameter body =>
          exact evaluate_forall_returns state env outer context collection parameter body initial tail
      | relationQuery => simp [administrativeGoal] at supported
      | freshness => simp [administrativeGoal] at supported
      | congruence => simp [administrativeGoal] at supported
      | scopedStep => simp [administrativeGoal] at supported
  | premises context premises initial =>
      exact evaluate_premises_returns state env outer context premises initial tail
  | quantified context parameter body index elements initial =>
      cases elements with
      | nil => exact evaluate_quantified_nil_returns state env outer context parameter body index initial tail
      | cons element elements =>
          exact evaluate_quantified_cons_returns state env outer context parameter body index element elements initial tail
  | root => simp [administrativeGoal] at supported
  | steps bound type source limit => exact evaluate_steps_returns state env outer bound type source limit tail

def taskFreeContext (env : Environment) {outer : Goal} : Task env outer → List (String × TypeExpr)
  | .evaluate goal _ => evaluationFreeContext env goal
  | _ => []

/-- The dispatcher retains the original tasks and continuations. Its source
domain is stated explicitly and grows only when a new branch is realized. -/
theorem expand_administrative_returns (state : State) (env : Environment) (outer : Goal)
    (task : Task env outer) (supported : administrativeTask task = true) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-expand" [Base.declarationsValue env.language,
        Base.freeValue (taskFreeContext env task), Base.encoded (taskTerm task)]) state
      (expansionValue (GeneralPremise.Execution.expand env outer task)) := by
  cases task with
  | evaluate goal tail =>
      let caller := environment .expand [Base.declarationsValue env.language,
        Base.freeValue (evaluationFreeContext env goal), Base.encoded (taskTerm (.evaluate goal tail))]
      let selected := [("continuation", continuationValue tail), ("goal", goalValue goal)] ++ caller
      apply helper_call .expand [] state _ _ _ rfl (Base.captured_closed _)
      rw [expand_shape]
      apply Base.branch_returns caller selected state _ (Base.encoded (taskTerm (.evaluate goal tail)))
        expandCases (Base.a "gslt:premise:machine-evaluate"
          [Base.v "declarations", Base.v "free", Base.v "goal", Base.v "continuation"]) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "task"
      · simp [expandCases, taskTerm, selected, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, goalValue, Subst.lookup]
      · change PureReturns Base.runtime selected state
          (Base.a "gslt:premise:machine-evaluate" [Base.v "declarations", Base.v "free", Base.v "goal", Base.v "continuation"])
          state (expansionValue (GeneralPremise.Execution.evaluate env outer goal tail))
        exact helper_capture .evaluate selected state _ _ _ rfl
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          (evaluate_administrative_returns state env outer goal tail supported)
  | deliver result tail =>
      let caller := environment .expand [Base.declarationsValue env.language, Base.freeValue [],
        Base.encoded (taskTerm (.deliver result tail))]
      let selected := [("continuation", continuationValue tail), ("result", resultValue result)] ++ caller
      apply helper_call .expand [] state _ _ _ rfl (Base.captured_closed _)
      rw [expand_shape]
      apply Base.branch_returns caller selected state _ (Base.encoded (taskTerm (.deliver result tail)))
        expandCases (Base.a "gslt:premise:machine-deliver" [Base.v "result", Base.v "continuation"]) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "task"
      · simp [expandCases, taskTerm, selected, caller, environment, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, resultValue, Subst.lookup]
      · change PureReturns Base.runtime selected state
          (Base.a "gslt:premise:machine-deliver" [Base.v "result", Base.v "continuation"])
          state (expansionValue (GeneralPremise.Execution.delivered env outer result tail))
        exact helper_capture .deliver selected state _ _ _ rfl
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          (delivered_administrative_returns state env _ outer result tail supported)
  | scanChildren bound type source limit cursor tail =>
      exact expand_scan_children_returns state env outer bound type source limit cursor tail
  | query => simp [administrativeTask] at supported
  | rootMatch => simp [administrativeTask] at supported
  | targetMatch => simp [administrativeTask] at supported

theorem expand_administrative_completed_iff (state after : State) (env : Environment) (outer : Goal)
    (task : Task env outer) (supported : administrativeTask task = true) (answers input output : List Atom) :
    (∃ fuel, run Base.runtime fuel {state, control := (.evaluate []
        (Base.a "gslt:premise:machine-expand" [Base.declarationsValue env.language,
          Base.freeValue (taskFreeContext env task), Base.encoded (taskTerm task)]))} =
      .complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (GeneralPremise.Execution.expand env outer task)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff Base.runtime [] state state _ _
    (expand_administrative_returns state env outer task supported) after answers input output

theorem expand_administrative_derivation_iff (state after : State) (env : Environment) (outer : Goal)
    (task : Task env outer) (supported : administrativeTask task = true) (answers input output : List Atom) :
    DeclarativeSpec.Runs Base.runtime {state, control := (.evaluate []
        (Base.a "gslt:premise:machine-expand" [Base.declarationsValue env.language,
          Base.freeValue (taskFreeContext env task), Base.encoded (taskTerm task)]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [expansionValue (GeneralPremise.Execution.expand env outer task)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff Base.runtime [] state state _ _
    (expand_administrative_returns state env outer task supported) after answers input output

#print axioms evaluate_administrative_returns
#print axioms expand_administrative_returns
#print axioms expand_administrative_completed_iff
#print axioms expand_administrative_derivation_iff

theorem evaluate_premises_free_returns (state : State) (env : Environment) (outer : Goal) (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (premises : List Premise) (initial : Assignment)
    (tail : Continuation env (.premises context premises initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue free,
        goalValue (.premises context premises initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer (.premises context premises initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue free,
    goalValue (.premises context premises initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("premises", premisesValue premises),
    ("context", contextValue context)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.premises context premises initial))
    evaluateCases (Base.caseData (Base.v "premises") evaluatePremisesCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, premisesValue,
      contextValue, Subst.lookup]
  · cases premises with
    | nil =>
        apply Base.branch_returns framed framed state _ (.symbol "LNil") evaluatePremisesCases evaluatePremisesNilData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, premisesValue,
            encodeList, CettaWireAtom.encode] using variable_returns Base.runtime framed state "premises"
        · simp [evaluatePremisesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · have templated : PureData.Template Base.runtime evaluatePremisesNilData := by
            unfold evaluatePremisesNilData
            machine_template
          simpa [evaluatePremisesNilData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
            taskTerm, resultTerm, goalTerm, eventsTerm, encodeOption, encodeList, framed, caller, environment,
            Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, assignmentValue,
            goalValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime framed state _ templated
    | cons premise premises =>
        let selected := [("rest", premisesValue premises), ("premise", premiseValue premise)] ++ framed
        apply Base.branch_returns framed selected state _
          (Base.a "LCons" [premiseValue premise, premisesValue premises]) evaluatePremisesCases evaluatePremisesConsData _
        · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, premisesValue,
            premiseValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            variable_returns Base.runtime framed state "premises"
        · simp [evaluatePremisesCases, selected, framed, caller, environment, Helper.names,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · have templated : PureData.Template Base.runtime evaluatePremisesConsData := by
            unfold evaluatePremisesConsData
            machine_template
          simpa [evaluatePremisesConsData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
            taskTerm, continuationTerm, goalTerm, encodeOption, encodeList, selected, framed, caller,
            environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            assignmentValue, premisesValue, premiseValue, contextValue,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return Base.runtime selected state _ templated

#print axioms evaluate_premises_free_returns


theorem evaluate_quantified_nil_free_returns (state : State) (env : Environment) (outer : Goal) (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (initial : Assignment)
    (tail : Continuation env (.quantified context parameter body index [] initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue free,
        goalValue (.quantified context parameter body index [] initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.quantified context parameter body index [] initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue free,
    goalValue (.quantified context parameter body index [] initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("elements", Base.patternsValue []), ("index", Base.number index),
    ("body", premiseValue body), ("parameter", Base.stringValue parameter), ("context", contextValue context)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.quantified context parameter body index [] initial))
    evaluateCases (Base.caseData (Base.v "elements") evaluateQuantifiedCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, Base.patternsValue,
      premiseValue, contextValue, Base.number, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed framed state _ (.symbol "LNil") evaluateQuantifiedCases evaluateQuantifiedNilData _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, Base.patternsValue,
        Base.patternsTerm, InferenceCettaWire.encodePatterns, encodeList, CettaWireAtom.encode] using
        variable_returns Base.runtime framed state "elements"
    · simp [evaluateQuantifiedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · have templated : PureData.Template Base.runtime evaluateQuantifiedNilData := by
        unfold evaluateQuantifiedNilData
        machine_template
      simpa [evaluateQuantifiedNilData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
        taskTerm, resultTerm, goalTerm, encodeOption, encodeList, quantifiedEventsTerm, framed, caller,
        environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
        assignmentValue, goalValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return Base.runtime framed state _ templated

#print axioms evaluate_quantified_nil_free_returns


theorem evaluate_steps_free_returns (state : State) (env : Environment) (outer : Goal) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Continuation env (.steps bound type source limit) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue free,
        goalValue (.steps bound type source limit), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer (.steps bound type source limit) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue free,
    goalValue (.steps bound type source limit), continuationValue tail]
  let framed := [("limit", Base.number limit), ("source", Base.patternValue source),
    ("type", Base.typeValue type), ("bound", Base.boundValue bound)] ++ caller
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _ (goalValue (.steps bound type source limit))
    evaluateCases evaluateStepsData _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Base.boundValue, Base.typeValue,
      Base.patternValue, Base.number, Subst.lookup]
  · have templated : PureData.Template Base.runtime evaluateStepsData := by
      unfold evaluateStepsData
      machine_template
    simpa [evaluateStepsData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
      taskTerm, goalTerm, encodeOption, encodeList, framed, caller, environment, Helper.names,
      applySubst, applySubst.applySubstList, Subst.lookup, Base.boundValue, Base.typeValue, Base.patternValue,
      Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return Base.runtime framed state _ templated

#print axioms evaluate_steps_free_returns


theorem evaluate_forall_free_returns (state : State) (env : Environment) (outer : Goal) (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (collection parameter : String) (body : Premise)
    (initial : Assignment)
    (tail : Continuation env (.premise context (.forAll collection parameter body) initial) outer) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language, Base.freeValue free,
        goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.premise context (.forAll collection parameter body) initial) tail)) := by
  let caller := environment .evaluate [Base.declarationsValue env.language, Base.freeValue free,
    goalValue (.premise context (.forAll collection parameter body) initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("body", premiseValue body),
    ("parameter", Base.stringValue parameter), ("collection", Base.stringValue collection), ("context", contextValue context)] ++ caller
  let contextual := contextCaptured context framed
  let ambient := ("ambient", Base.number context.bound.length) :: contextual
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _
    (goalValue (.premise context (.forAll collection parameter body) initial))
    evaluateCases (Base.caseData (Base.v "context") evaluateForAllContextCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, InferenceCettaWire.AuthoredRule.premiseTerm,
      framed, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      assignmentValue, premiseValue, contextValue, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed contextual state _ (contextValue context)
      evaluateForAllContextCases evaluateForAllBody _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns Base.runtime framed state "context"
    · simp [evaluateForAllContextCases, contextual, contextCaptured, framed, caller, environment, Helper.names,
        contextValue, contextTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Base.number, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, Subst.lookup]
    · rw [forall_body_shape]
      apply let_returns Base.runtime contextual ambient state state state (Base.v "ambient")
        (Base.a "gslt:automata:length" [Base.v "bound"])
        (Base.caseData (Base.a "gslt:premise:scope-collection" [Base.v "ambient", Base.v "initial", Base.v "collection"])
          evaluateForAllCollectionCases) (Base.number context.bound.length) _
      · exact assignment_length_returns contextual state context.bound (by
          simp [contextual, contextCaptured, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, contextual, contextCaptured, framed, caller, environment, Helper.names, Subst.lookup]
      · have collectionReturned := Base.previous_returns (by decide +kernel)
          (QuantifiedLocal.finite_collection_captured_returns ambient state context.bound.length initial collection
            (Base.v "ambient") (Base.v "initial") (Base.v "collection") (by
              simp [ambient, contextual, contextCaptured, framed, caller, environment, Helper.names,
                applySubst, Subst.lookup]))
        cases found : GeneralPremise.finiteCollection? context.bound.length initial collection with
        | none =>
            apply Base.branch_returns ambient ambient state _ (.symbol "None")
              evaluateForAllCollectionCases evaluateForAllNoneData _
            · simpa only [found, QuantifiedLocal.finiteCollectionOptionTerm, encodeOption, CettaWireAtom.encode] using collectionReturned
            · simp [evaluateForAllCollectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · rw [evaluate_forall_none_eq env outer context collection parameter body initial tail found]
              have templated : PureData.Template Base.runtime evaluateForAllNoneData := by
                unfold evaluateForAllNoneData
                machine_template
              simpa [evaluateForAllNoneData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
                GeneralPremise.Execution.evaluatePremise, found, encodeOption, encodeList, obligationTerm,
                ambient, contextual, contextCaptured, framed, caller, environment, Helper.names,
                applySubst, applySubst.applySubstList, Subst.lookup, Base.stringValue, Base.number,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return Base.runtime ambient state _ templated
        | some value =>
            rcases value with ⟨kind, elements⟩
            let selected := [("elements", Base.patternsValue elements), ("kind", collectionValue kind)] ++ ambient
            apply Base.branch_returns ambient selected state _
              (Base.a "Some" [Base.a "FiniteCollection" [collectionValue kind, Base.patternsValue elements]])
              evaluateForAllCollectionCases evaluateForAllSomeData _
            · simpa only [found, QuantifiedLocal.finiteCollectionOptionTerm, encodeOption, CettaWireAtom.encode,
                CettaWireAtom.encodeMany] using collectionReturned
            · simp [evaluateForAllCollectionCases, selected, ambient, contextual, contextCaptured,
                framed, caller, environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · rw [evaluate_forall_some_eq env outer context collection parameter body initial kind elements tail found]
              have templated : PureData.Template Base.runtime evaluateForAllSomeData := by
                unfold evaluateForAllSomeData
                machine_template
              simpa [evaluateForAllSomeData, expansionValue, expansionTerm, GeneralPremise.Execution.evaluate,
                GeneralPremise.Execution.evaluatePremise, found, taskTerm, continuationTerm, goalTerm,
                encodeOption, encodeList, selected, ambient, contextual, contextCaptured, framed, caller,
                environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                contextValue, assignmentValue, premiseValue, Base.patternsValue, collectionValue, Base.stringValue,
                Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return Base.runtime selected state _ templated

#print axioms evaluate_forall_free_returns


theorem evaluate_quantified_cons_free_returns (state : State) (env : Environment) (outer : Goal) (free : List (String × TypeExpr))
    (context : GeneralPremise.Context) (parameter : String) (body : Premise)
    (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
    (tail : Continuation env (.quantified context parameter body index (element :: elements) initial) outer)
    (same : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial),
      (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) name = env.free name) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:machine-evaluate" [Base.declarationsValue env.language,
        Base.freeValue free,
        goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]) state
      (expansionValue (GeneralPremise.Execution.evaluate env outer
        (.quantified context parameter body index (element :: elements) initial) tail)) := by
  let assignment := GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element) initial
  let caller := environment .evaluate [Base.declarationsValue env.language,
    Base.freeValue free,
    goalValue (.quantified context parameter body index (element :: elements) initial), continuationValue tail]
  let framed := [("initial", assignmentValue initial), ("elements", Base.patternsValue (element :: elements)),
    ("index", Base.number index), ("body", premiseValue body), ("parameter", Base.stringValue parameter),
    ("context", contextValue context)] ++ caller
  let selected := [("rest", Base.patternsValue elements), ("element", Base.patternValue element)] ++ framed
  let contextual := [("quantifiers", Base.number context.quantifierDepth), ("premise", Base.number context.premiseIndex),
    ("bound", Base.boundValue context.bound), ("spec", Base.specValue context.spec), ("rule", Base.ruleValue context.rule),
    ("ruleIndex", Base.number context.ruleIndex)] ++ selected
  let ambient := ("ambient", Base.number context.bound.length) :: contextual
  let localized := ("local", contextualValueValue (GeneralPremise.localValue context.bound element)) :: ambient
  let assigned := ("assignment", assignmentValue assignment) :: localized
  let quantified := ("quantified", contextValue context.quantified) :: assigned
  apply helper_call .evaluate [] state _ _ _ rfl (Base.captured_closed _)
  rw [evaluate_shape]
  apply Base.branch_returns caller framed state _
    (goalValue (.quantified context parameter body index (element :: elements) initial))
    evaluateCases (Base.caseData (Base.v "elements") evaluateQuantifiedCases) _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "goal"
  · simp [evaluateCases, goalValue, goalTerm, framed, caller, environment, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, assignmentValue, Base.patternsValue,
      premiseValue, contextValue, Base.number, Base.stringValue, Subst.lookup]
  · apply Base.branch_returns framed selected state _
      (Base.a "LCons" [Base.patternValue element, Base.patternsValue elements]) evaluateQuantifiedCases
      (Base.caseData (Base.v "context") evaluateQuantifiedContextCases) _
    · simpa [framed, caller, environment, Helper.names, applySubst, Subst.lookup, Base.patternsValue,
        Base.patternsTerm, InferenceCettaWire.encodePatterns, encodeList, CettaWireAtom.encode,
        CettaWireAtom.encodeMany] using variable_returns Base.runtime framed state "elements"
    · simp [evaluateQuantifiedCases, selected, framed, caller, environment, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup]
    · apply Base.branch_returns selected contextual state _ (contextValue context)
        evaluateQuantifiedContextCases evaluateQuantifiedConsBody _
      · simpa [selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime selected state "context"
      · simp [evaluateQuantifiedContextCases, contextual, selected, framed, caller, environment, Helper.names,
          contextValue, contextTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Base.number, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, Subst.lookup]
      · rw [quantified_cons_shape]
        apply PureData.let_bindings_return (pairs := [
          (Base.v "ambient", Base.a "gslt:automata:length" [Base.v "bound"]),
          (Base.v "local", Base.a "gslt:premise:scope-local-value" [Base.v "ambient", Base.v "element"]),
          (Base.v "assignment", Base.a "gslt:premise:scope-bind" [Base.v "parameter", Base.v "local", Base.v "initial"]),
          (Base.v "quantified", Base.a "gslt:premise:context-quantified" [Base.v "context"])])
          (final := quantified) (middle := state) _ state evaluateQuantifiedCheckData _ _
        · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state) (value := Base.number context.bound.length)
          · exact assignment_length_returns contextual state context.bound (by
              simp [contextual, selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := localized) (middle := state)
              (value := contextualValueValue (GeneralPremise.localValue context.bound element))
            · exact Base.previous_returns (by decide +kernel)
                (QuantifiedLocal.local_value_captured_returns ambient state context.bound element
                  (Base.v "ambient") (Base.v "element") (by
                    simp [ambient, contextual, selected, framed, caller, environment, Helper.names,
                      applySubst, Subst.lookup]))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                localized, ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := assigned) (middle := state)
                (value := assignmentValue assignment)
              · exact Base.previous_returns (by decide +kernel)
                  (QuantifiedLocal.bind_parameter_captured_returns localized state parameter
                    (GeneralPremise.localValue context.bound element) initial
                    (Base.v "parameter") (Base.v "local") (Base.v "initial") (by
                      simp [localized, ambient, contextual, selected, framed, caller, environment, Helper.names,
                        applySubst, Subst.lookup]))
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  assigned, localized, ambient, contextual, selected, framed, caller, environment, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := quantified) (middle := state)
                  (value := contextValue context.quantified)
                · exact context_quantified_captured_returns assigned state context (Base.v "context") (by
                    simp [assigned, localized, ambient, contextual, selected, framed, caller,
                      environment, Helper.names, applySubst, Subst.lookup])
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    quantified, assigned, localized, ambient, contextual, selected, framed, caller,
                    environment, Helper.names, Subst.lookup]
                · exact .nil quantified state
        · unfold evaluateQuantifiedCheckData
          apply Base.bool_if_returns quantified state _
            (GeneralPremise.checkTypedAssignment env context.quantified assignment)
            evaluateQuantifiedAcceptedData evaluateQuantifiedRejectedData _
          · exact check_typed_assignment_free_captured_returns quantified state env context.quantified assignment free same
              (Base.v "declarations") (Base.v "free") (Base.v "bound") (Base.v "rule") (Base.v "spec") (Base.v "assignment") (by
                simp [GeneralPremise.Context.quantified, quantified, assigned, localized, ambient, contextual,
                  selected, framed, caller, environment, Helper.names, applySubst, Subst.lookup])
          · cases checked : GeneralPremise.checkTypedAssignment env context.quantified assignment with
            | false =>
                have templated : PureData.Template Base.runtime evaluateQuantifiedRejectedData := by
                  unfold evaluateQuantifiedRejectedData
                  machine_template
                simpa [checked, evaluateQuantifiedRejectedData, expansionValue, expansionTerm,
                  GeneralPremise.Execution.evaluate, assignment, encodeOption, encodeList, obligationTerm,
                  quantified, assigned, localized, ambient, contextual, selected, framed, caller,
                  environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                  Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return Base.runtime quantified state _ templated
            | true =>
                have templated : PureData.Template Base.runtime evaluateQuantifiedAcceptedData := by
                  unfold evaluateQuantifiedAcceptedData
                  machine_template
                simpa [checked, evaluateQuantifiedAcceptedData, expansionValue, expansionTerm,
                  GeneralPremise.Execution.evaluate, taskTerm, continuationTerm, goalTerm, assignment,
                  encodeOption, encodeList, quantified, assigned, localized, ambient, contextual, selected,
                  framed, caller, environment, Helper.names, applySubst, applySubst.applySubstList,
                  Subst.lookup, assignmentValue, contextValue, premiseValue, Base.patternsValue, Base.patternValue,
                  Base.stringValue, Base.number, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return Base.runtime quantified state _ templated


#print axioms evaluate_quantified_cons_free_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open PremiseOperationsExecution.GeneralExecution
  (contextTerm signatureTerm queryRequestTerm queryObligationTerm)

private abbrev assignmentTerm := RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm

/-- The name table and bare premise environment carried by interpreted matching. -/
def interpretedEnvironmentTerm (names : List String) (core : Term) : Term :=
  .application "InterpretedPremiseEnvironment" [encodeList Term.string names, core]

/-- The shared source program viewed by the interpreted matching proofs. -/
def interpretedLibrary : BridgeKit.Library :=
  ⟨{ equations := [], declarations := [] }, RuleExecutionProgram.interpretedPremiseProgram, ["gslt:"]⟩

set_option maxRecDepth 100000 in
theorem interpreted_checked : interpretedLibrary.check = true := by decide +kernel

theorem interpreted_runtime : interpretedLibrary.runtime = RuleExecutionProgram.interpretedPremiseProgram := rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open SpaceSemantics (Program)
open Eval BridgeKit

private local instance scopedPrimitiveEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧
    left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

private def scopedPrimitiveExcluded : List String := ["gslt:premise:query-expand-in", "gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root", "gslt:premise:machine-expand-in", "gslt:premise:machine-tick", "gslt:premise:machine-run"]

def scopedPrimitiveHeads (head : String) : Bool :=
  !scopedPrimitiveExcluded.contains head && !head.startsWith "gslt:premise:matching-" &&
    !head.startsWith "native-probe:" &&
    (!head.startsWith "gslt:" || head.startsWith "gslt:rule:" ||
      head.startsWith "gslt:premise:" || head.startsWith "gslt:automata:")

private def scopedPrimitiveCheckRow (row : SpaceSemantics.Equation) : Bool := !scopedPrimitiveHeads row.head || codeWithin scopedPrimitiveHeads row.body

private theorem scopedPrimitive_all_split {α : Type} (xs : List α) (p : α → Bool) (n : Nat)
    (first : (xs.take n).all p = true) (rest : (xs.drop n).all p = true) : xs.all p = true := by
  have joined : (xs.take n ++ xs.drop n).all p = true := by rw [List.all_append, first, rest]; rfl
  simpa only [List.take_append_drop] using joined

private theorem scopedPrimitive_filter_split {α : Type} (p : α → Bool) (xs ys : List α) (n m : Nat)
    (first : (xs.take n).filter p = (ys.take m).filter p)
    (rest : (xs.drop n).filter p = (ys.drop m).filter p) : xs.filter p = ys.filter p := by
  calc
    xs.filter p = (xs.take n ++ xs.drop n).filter p := by rw [List.take_append_drop]
    _ = (xs.take n).filter p ++ (xs.drop n).filter p := by rw [List.filter_append]
    _ = (ys.take m).filter p ++ (ys.drop m).filter p := by rw [first, rest]
    _ = (ys.take m ++ ys.drop m).filter p := by rw [List.filter_append]
    _ = ys.filter p := by rw [List.take_append_drop]

private theorem scopedPrimitive_closed_block_0 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 0).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_20 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 20).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_40 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 40).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_60 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 60).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_80 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 80).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_100 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 100).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_120 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 120).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_140 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 140).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_160 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 160).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_180 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 180).take 20).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_block_200 : ((RuleExecutionProgram.scopedMachineProgram.equations.drop 200).take 18).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_suffix_218 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 218).all scopedPrimitiveCheckRow = true := by decide +kernel

private theorem scopedPrimitive_closed_suffix_200 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 200).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 200) scopedPrimitiveCheckRow 18
  · simpa using scopedPrimitive_closed_block_200
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_218

private theorem scopedPrimitive_closed_suffix_180 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 180).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 180) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_180
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_200

private theorem scopedPrimitive_closed_suffix_160 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 160).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 160) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_160
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_180

private theorem scopedPrimitive_closed_suffix_140 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 140).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 140) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_140
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_160

private theorem scopedPrimitive_closed_suffix_120 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 120).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 120) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_120
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_140

private theorem scopedPrimitive_closed_suffix_100 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 100).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 100) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_100
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_120

private theorem scopedPrimitive_closed_suffix_80 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 80).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 80) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_80
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_100

private theorem scopedPrimitive_closed_suffix_60 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 60).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 60) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_60
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_80

private theorem scopedPrimitive_closed_suffix_40 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 40).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 40) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_40
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_60

private theorem scopedPrimitive_closed_suffix_20 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 20).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 20) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_20
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_40

private theorem scopedPrimitive_closed_suffix_0 : (RuleExecutionProgram.scopedMachineProgram.equations.drop 0).all scopedPrimitiveCheckRow = true := by
  apply scopedPrimitive_all_split (RuleExecutionProgram.scopedMachineProgram.equations.drop 0) scopedPrimitiveCheckRow 20
  · simpa using scopedPrimitive_closed_block_0
  · simpa only [List.drop_drop] using scopedPrimitive_closed_suffix_20

theorem scopedPrimitive_closed : ProgramClosed scopedPrimitiveHeads RuleExecutionProgram.scopedMachineProgram := by
  refine ⟨by decide +kernel, ?_⟩
  intro row member supported
  have checked : RuleExecutionProgram.scopedMachineProgram.equations.all scopedPrimitiveCheckRow = true := by simpa only [List.drop_zero] using scopedPrimitive_closed_suffix_0
  have good := List.all_eq_true.mp checked row member
  change (!scopedPrimitiveHeads row.head || codeWithin scopedPrimitiveHeads row.body) = true at good
  simpa only [supported, Bool.not_true, Bool.false_or] using good

private theorem scopedPrimitive_equations_block_0 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 0).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 0).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_1 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 20).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 20).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_2 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 40).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 40).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_3 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 60).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 60).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_4 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 80).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 80).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_5 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 100).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 100).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_6 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 120).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 120).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_7 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 140).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 140).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_8 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 160).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 160).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_9 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 180).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 180).take 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_10 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 200).take 18).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 200).take 17).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_block_11 :
    ((RuleExecutionProgram.scopedMachineProgram.equations.drop 218).take 0).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 217).take 343).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_suffix_12 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 218).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 560).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  decide +kernel

private theorem scopedPrimitive_equations_suffix_11 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 218).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 217).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 218)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 217) 0 343 scopedPrimitive_equations_block_11
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_12

private theorem scopedPrimitive_equations_suffix_10 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 200).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 200).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 200)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 200) 18 17 scopedPrimitive_equations_block_10
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_11

private theorem scopedPrimitive_equations_suffix_9 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 180).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 180).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 180)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 180) 20 20 scopedPrimitive_equations_block_9
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_10

private theorem scopedPrimitive_equations_suffix_8 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 160).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 160).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 160)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 160) 20 20 scopedPrimitive_equations_block_8
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_9

private theorem scopedPrimitive_equations_suffix_7 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 140).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 140).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 140)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 140) 20 20 scopedPrimitive_equations_block_7
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_8

private theorem scopedPrimitive_equations_suffix_6 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 120).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 120).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 120)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 120) 20 20 scopedPrimitive_equations_block_6
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_7

private theorem scopedPrimitive_equations_suffix_5 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 100).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 100).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 100)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 100) 20 20 scopedPrimitive_equations_block_5
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_6

private theorem scopedPrimitive_equations_suffix_4 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 80).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 80).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 80)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 80) 20 20 scopedPrimitive_equations_block_4
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_5

private theorem scopedPrimitive_equations_suffix_3 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 60).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 60).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 60)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 60) 20 20 scopedPrimitive_equations_block_3
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_4

private theorem scopedPrimitive_equations_suffix_2 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 40).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 40).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 40)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 40) 20 20 scopedPrimitive_equations_block_2
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_3

private theorem scopedPrimitive_equations_suffix_1 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 20).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 20)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 20) 20 20 scopedPrimitive_equations_block_1
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_2

private theorem scopedPrimitive_equations_suffix_0 :
    (RuleExecutionProgram.scopedMachineProgram.equations.drop 0).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) =
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 0).filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  apply scopedPrimitive_filter_split (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) (RuleExecutionProgram.scopedMachineProgram.equations.drop 0)
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 0) 20 20 scopedPrimitive_equations_block_0
  simpa only [List.drop_drop] using scopedPrimitive_equations_suffix_1

theorem scopedPrimitive_equations : RuleExecutionProgram.scopedMachineProgram.equations.filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) = RuleExecutionProgram.interpretedPremiseProgram.equations.filter (fun row : SpaceSemantics.Equation => scopedPrimitiveHeads row.head) := by
  simpa only [List.drop_zero] using scopedPrimitive_equations_suffix_0

private theorem scopedPrimitive_declarations_block_0 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 0).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 0).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_1 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 20).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 20).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_2 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 40).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 40).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_3 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 60).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 60).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_4 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 80).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 80).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_5 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 100).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 100).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_6 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 120).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 120).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_7 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 140).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 140).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_8 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 160).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 160).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_9 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 180).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 180).take 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_10 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 200).take 18).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 200).take 17).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_block_11 :
    ((RuleExecutionProgram.scopedMachineProgram.declarations.drop 218).take 0).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    ((RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 217).take 343).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_suffix_12 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 218).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 560).filter (retainedCallDeclaration scopedPrimitiveHeads) := by decide +kernel

private theorem scopedPrimitive_declarations_suffix_11 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 218).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 217).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 218)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 217) 0 343 scopedPrimitive_declarations_block_11
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_12

private theorem scopedPrimitive_declarations_suffix_10 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 200).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 200).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 200)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 200) 18 17 scopedPrimitive_declarations_block_10
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_11

private theorem scopedPrimitive_declarations_suffix_9 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 180).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 180).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 180)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 180) 20 20 scopedPrimitive_declarations_block_9
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_10

private theorem scopedPrimitive_declarations_suffix_8 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 160).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 160).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 160)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 160) 20 20 scopedPrimitive_declarations_block_8
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_9

private theorem scopedPrimitive_declarations_suffix_7 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 140).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 140).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 140)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 140) 20 20 scopedPrimitive_declarations_block_7
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_8

private theorem scopedPrimitive_declarations_suffix_6 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 120).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 120).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 120)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 120) 20 20 scopedPrimitive_declarations_block_6
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_7

private theorem scopedPrimitive_declarations_suffix_5 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 100).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 100).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 100)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 100) 20 20 scopedPrimitive_declarations_block_5
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_6

private theorem scopedPrimitive_declarations_suffix_4 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 80).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 80).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 80)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 80) 20 20 scopedPrimitive_declarations_block_4
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_5

private theorem scopedPrimitive_declarations_suffix_3 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 60).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 60).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 60)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 60) 20 20 scopedPrimitive_declarations_block_3
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_4

private theorem scopedPrimitive_declarations_suffix_2 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 40).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 40).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 40)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 40) 20 20 scopedPrimitive_declarations_block_2
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_3

private theorem scopedPrimitive_declarations_suffix_1 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 20).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 20).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 20)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 20) 20 20 scopedPrimitive_declarations_block_1
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_2

private theorem scopedPrimitive_declarations_suffix_0 :
    (RuleExecutionProgram.scopedMachineProgram.declarations.drop 0).filter (retainedCallDeclaration scopedPrimitiveHeads) =
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 0).filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  apply scopedPrimitive_filter_split (retainedCallDeclaration scopedPrimitiveHeads) (RuleExecutionProgram.scopedMachineProgram.declarations.drop 0)
    (RuleExecutionProgram.interpretedPremiseProgram.declarations.drop 0) 20 20 scopedPrimitive_declarations_block_0
  simpa only [List.drop_drop] using scopedPrimitive_declarations_suffix_1

theorem scopedPrimitive_declarations : RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration scopedPrimitiveHeads) = RuleExecutionProgram.interpretedPremiseProgram.declarations.filter (retainedCallDeclaration scopedPrimitiveHeads) := by
  simpa only [List.drop_zero] using scopedPrimitive_declarations_suffix_0

theorem scopedPrimitive_agreement : ProgramAgreementOn scopedPrimitiveHeads RuleExecutionProgram.scopedMachineProgram RuleExecutionProgram.interpretedPremiseProgram :=
  programAgreementOn_of_retained_rows scopedPrimitiveHeads RuleExecutionProgram.scopedMachineProgram RuleExecutionProgram.interpretedPremiseProgram scopedPrimitive_equations scopedPrimitive_declarations


set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure MatchingCodec (matcher : MatchingExecution) where
  choiceTerm : matcher.Choice → Term
  stateTerm : matcher.State → Term

def ordinaryCodec : MatchingCodec MatchingExecution.ordinary where
  choiceTerm := RuleInstantiationExecution.GeneralExecution.bagChoiceTerm
  stateTerm := RuleInstantiationExecution.GeneralExecution.matcherStateTerm

/-- Reading an answer preserves its assignment and ordered occurrence trace. -/
def matcherAnswerTerm {matcher : MatchingExecution} (codec : MatchingCodec matcher)
    (answer : matcher.Answer) : Term :=
  .application "ScopedMatcherAnswer" [assignmentTerm (matcher.assignment answer),
    encodeList codec.choiceTerm (matcher.trace answer)]

/-- Native start, one matcher tick, readout and input comparison for a selected matcher. -/
structure MatchingOperations (program : SpaceSemantics.Program)
    (matcher : MatchingExecution) (codec : MatchingCodec matcher)
    (profile : Term) (requestReady : GeneralScopedMatchMachine.Request → Prop)
    (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop) : Prop where
  start : ∀ host query, requestReady query →
    Eval.PureReturns program [] host (WireKit.apply "gslt:premise:matching-start"
      [WireKit.encoded profile, WireKit.encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query)])
      host (WireKit.encoded (codec.stateTerm (matcher.start query)))
  tick : ∀ host query machine, stateReady machine →
    Eval.PureReturns program [] host (WireKit.apply "gslt:premise:matching-tick"
      [WireKit.encoded profile, WireKit.encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query), WireKit.encoded (codec.stateTerm machine)])
      host (WireKit.encoded (codec.stateTerm (matcher.tick query machine)))
  complete : ∀ host machine,
    Eval.PureReturns program [] host (WireKit.apply "gslt:premise:matching-complete" [WireKit.encoded profile, WireKit.encoded (codec.stateTerm machine)])
      host (Effects.boolean (matcher.complete machine))
  answer : ∀ host machine cursor,
    Eval.PureReturns program [] host (WireKit.apply "gslt:premise:matching-answer-at"
      [WireKit.encoded profile, WireKit.encoded (codec.stateTerm machine), WireKit.number cursor])
      host (WireKit.encoded (encodeOption (matcherAnswerTerm codec) (matcher.answers machine)[cursor]?))
  input : ∀ host query actual, requestReady query → valueReady actual →
    Eval.PureReturns program [] host (WireKit.apply "gslt:premise:matching-input"
      [WireKit.encoded profile, WireKit.encoded (InferenceCettaWire.encodePattern actual), WireKit.encoded (InferenceCettaWire.encodePattern query.target)])
      host (Effects.boolean (matcher.acceptsInput query actual))

theorem ordinary_matcherAnswer (answer : GeneralScopedMatchMachine.Answer) :
    matcherAnswerTerm ordinaryCodec answer =
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answer := rfl

def originsTerm {Choice : Type} (choiceTerm : Choice → Term)
    (origins : List (Nat × List Choice)) : Term :=
  encodeList (fun origin => .application "ArgumentOrigin"
    [.natural origin.1, encodeList choiceTerm origin.2]) origins

mutual
def eventTerm {Choice : Type} (choiceTerm : Choice → Term) : GeneralPremise.Event Choice → Term
  | .query index quantifiers row origins => .application "PremiseQueryEvent"
      [.natural index, .natural quantifiers, .natural row, originsTerm choiceTerm origins]
  | .freshness index quantifiers atom subject => .application "PremiseFreshnessEvent"
      [.natural index, .natural quantifiers, .string atom, InferenceCettaWire.encodePattern subject]
  | .quantified index quantifiers kind elements => .application "PremiseQuantifiedEvent"
      [.natural index, .natural quantifiers, InferenceCettaWire.encodeCollectionType kind,
        quantifiedEventsTerm choiceTerm elements]
  | .child index quantifiers declaration bound source target trace targetTrace captured completed history =>
      .application "PremiseChildEvent" [.natural index, .natural quantifiers, .natural declaration,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm bound,
        InferenceCettaWire.encodePattern source, InferenceCettaWire.encodePattern target,
        encodeList choiceTerm trace, encodeList choiceTerm targetTrace,
        assignmentTerm captured, assignmentTerm completed, eventsTerm choiceTerm history]
termination_by event => sizeOf event

def eventsTerm {Choice : Type} (choiceTerm : Choice → Term) : List (GeneralPremise.Event Choice) → Term
  | [] => .symbol "LNil"
  | event :: events => .application "LCons" [eventTerm choiceTerm event, eventsTerm choiceTerm events]
termination_by events => sizeOf events

def quantifiedEventsTerm {Choice : Type} (choiceTerm : Choice → Term) :
    List (Nat × Pattern × List (GeneralPremise.Event Choice)) → Term
  | [] => .symbol "LNil"
  | (index, element, history) :: rest => .application "LCons"
      [.application "QuantifiedElement" [.natural index, InferenceCettaWire.encodePattern element,
        eventsTerm choiceTerm history], quantifiedEventsTerm choiceTerm rest]
termination_by elements => sizeOf elements
end

def stepCallTerm {environment : Environment} {matcher : MatchingExecution}
    (call : GeneralPremise.Execution.StepCall environment matcher) : Term :=
  .application "PremiseStepCall" [contextTerm call.context,
    InferenceCettaWire.AuthoredRule.premiseTerm call.premise,
    assignmentTerm call.initial, PremiseOperationsExecution.GeneralExecution.Base.typesTerm call.binders,
    InferenceCettaWire.AuthoredRule.typeTerm call.type,
    InferenceCettaWire.encodePattern call.source, InferenceCettaWire.encodePattern call.targetSchema]

def queryTaskTerm {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : MatchingCodec matcher) : Query.Task environment request matcher → Term
  | .start => .symbol "PremiseQueryStart"
  | .rows frame => .application "PremiseQueryRows" [signatureTerm frame.signature, .natural frame.cursor]
  | .dynamicInputs frame => .application "PremiseQueryDynamicInputs"
      [signatureTerm frame.signature, .natural frame.index,
        InferenceCettaWire.encodePatterns frame.schemas,
        encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes,
        InferenceCettaWire.encodePatterns frame.resolvedRev]
  | .dynamicRows frame => .application "PremiseQueryDynamicRows"
      [signatureTerm frame.signature, InferenceCettaWire.encodePatterns frame.resolved,
        encodeList InferenceCettaWire.encodePatterns frame.rows, .natural frame.cursor]
  | .arguments frame => .application "PremiseQueryArguments"
      [.natural frame.rowIndex, .natural frame.index, assignmentTerm frame.assignment,
        InferenceCettaWire.encodePatterns frame.schemas, InferenceCettaWire.encodePatterns frame.values,
        encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes,
        originsTerm codec.choiceTerm frame.origins]
  | .matcher frame => .application "PremiseQueryMatcher"
      [.natural frame.rowIndex, .natural frame.argumentIndex, InferenceCettaWire.encodePatterns frame.schemas,
        InferenceCettaWire.encodePatterns frame.values,
        encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes,
        originsTerm codec.choiceTerm frame.origins,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm frame.query,
        codec.stateTerm frame.state, .natural frame.cursor]

def queryAnswerTerm {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : MatchingCodec matcher) (answer : Query.Answer environment request matcher) : Term :=
  .application "PremiseQueryAnswer" [.natural answer.rowIndex,
    assignmentTerm answer.assignment, originsTerm codec.choiceTerm answer.origins]

def queryStateTerm {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : MatchingCodec matcher) (state : Query.State environment request matcher) : Term :=
  PremiseSchedulerExecution.schedulerStateTerm (queryTaskTerm codec) (queryAnswerTerm codec)
    queryObligationTerm state

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise

mutual
theorem ordinary_event : ∀ event : GeneralPremise.Event,
    eventTerm ordinaryCodec.choiceTerm event = PremiseOperationsExecution.GeneralExecution.eventTerm event
  | .query _ _ _ _ => by
      simp only [eventTerm, PremiseOperationsExecution.GeneralExecution.eventTerm]
      rfl
  | .freshness _ _ _ _ => by
      simp only [eventTerm, PremiseOperationsExecution.GeneralExecution.eventTerm]
  | .quantified index quantifiers kind elements => by
      simp only [eventTerm, PremiseOperationsExecution.GeneralExecution.eventTerm,
        ordinary_quantified elements]
  | .child index quantifiers declaration bound source target trace targetTrace captured completed history => by
      simp only [eventTerm, PremiseOperationsExecution.GeneralExecution.eventTerm,
        ordinary_events history]
      rfl
termination_by event => sizeOf event

theorem ordinary_events : ∀ events : List GeneralPremise.Event,
    eventsTerm ordinaryCodec.choiceTerm events = PremiseOperationsExecution.GeneralExecution.eventsTerm events
  | [] => by simp only [eventsTerm, PremiseOperationsExecution.GeneralExecution.eventsTerm]
  | event :: events => by
      simp only [eventsTerm, PremiseOperationsExecution.GeneralExecution.eventsTerm,
        ordinary_event event, ordinary_events events]
termination_by events => sizeOf events

theorem ordinary_quantified : ∀ elements : List (Nat × Pattern × List GeneralPremise.Event),
    quantifiedEventsTerm ordinaryCodec.choiceTerm elements =
      PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm elements
  | [] => by simp only [quantifiedEventsTerm, PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm]
  | (index, element, history) :: rest => by
      simp only [quantifiedEventsTerm, PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm,
        ordinary_events history, ordinary_quantified rest]
termination_by elements => sizeOf elements
end

theorem ordinary_query_task {environment : Environment} {request : Query.Request}
    (task : Query.Task environment request) :
    queryTaskTerm ordinaryCodec task = PremiseOperationsExecution.GeneralExecution.queryTaskTerm task := by
  cases task <;> rfl

theorem ordinary_query_answer {environment : Environment} {request : Query.Request}
    (answer : Query.Answer environment request) :
    queryAnswerTerm ordinaryCodec answer =
      PremiseOperationsExecution.GeneralExecution.QueryExecution.queryAnswerTerm answer := rfl

theorem ordinary_query_state {environment : Environment} {request : Query.Request}
    (state : Query.State environment request) :
    queryStateTerm ordinaryCodec state = PremiseOperationsExecution.GeneralExecution.queryStateTerm state := by
  have tasks : (queryTaskTerm ordinaryCodec : Query.Task environment request → Term) =
      PremiseOperationsExecution.GeneralExecution.queryTaskTerm := funext ordinary_query_task
  have answers : (queryAnswerTerm ordinaryCodec : Query.Answer environment request → Term) =
      PremiseOperationsExecution.GeneralExecution.QueryExecution.queryAnswerTerm := funext ordinary_query_answer
  unfold queryStateTerm PremiseOperationsExecution.GeneralExecution.queryStateTerm
  rw [tasks, answers]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations.start
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations.tick
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations.complete
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations.answer
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.MatchingOperations.input

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.interpreted_checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.interpreted_runtime

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.interpretedEnvironmentTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.scopedPrimitive_closed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.scopedPrimitive_equations
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.scopedPrimitive_declarations
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.scopedPrimitive_agreement
