import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseEnvironmentExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness

/-! Native source realization of the finite-provider general-premise query
frames. Registered native services have their separate execution contract. -/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Effects (State)
open SpaceSemantics (Program)
open Eval
open scoped ProgramQuotation

private def matcherEraseSource : Program := RuleExecutionProgram.matcherEraseProgram

private def instantiationSource : Program := RuleExecutionProgram.scopedInstantiationProgram

private def matcherSource : Program := RuleExecutionProgram.scopedMatcherProgram

private def querySource : Program := RuleExecutionProgram.premiseQueryProgram

private def extension : Program :=
  ((matcherEraseSource.append instantiationSource).append matcherSource).append querySource

def queryRuntimeProgram : Program := premiseRuntimeProgram.append extension

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem prior_agreement :
    ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram queryRuntimeProgram := by
  apply appended_program_agreement
  · intro equation member
    have checked : extension.equations.all (fun equation => !premiseExecutionHeads equation.head) = true := by
      decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : premiseExecutionHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : extension.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !premiseExecutionHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : premiseExecutionHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem prior_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin premiseExecutionHeads code = true)
    (returned : PureReturns premiseRuntimeProgram caller state code state answer) :
    PureReturns queryRuntimeProgram caller state code state answer :=
  premise_returns_in_extension queryRuntimeProgram prior_agreement supported returned

def queryExpansionTerm {environment : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task environment request) (Query.Answer environment request) Query.Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm queryTaskTerm queryAnswerTerm queryObligationTerm expansion

theorem query_state_wire_eq_scheduler {environment : Environment} {request : Query.Request}
    (state : Query.State environment request) :
    queryStateTerm state =
      PremiseSchedulerExecution.schedulerStateTerm queryTaskTerm queryAnswerTerm queryObligationTerm state := rfl

theorem query_source_no_initializers : querySource.initializers = [] := by decide +kernel

theorem query_source_equation_heads_unique : (querySource.equations.map (·.head)).Nodup := by decide +kernel


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

private def baseHeads (head : String) : Bool :=
  premiseExecutionHeads head && !(["gslt:premise:check-assignment", "gslt:premise:check-row", "gslt:premise:check-values", "gslt:premise:constructor-declarations", "gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:ground-at", "gslt:premise:ground-list-at", "gslt:premise:machine-deliver", "gslt:premise:machine-evaluate", "gslt:premise:machine-expand", "gslt:premise:presentation-named", "gslt:premise:reflective-presentations", "gslt:premise:reflective-rules", "gslt:premise:signature", "gslt:premise:signature-candidates", "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:substitution-presentation", "gslt:premise:type-context-lookup"].contains head)

private def baseExtension : Program where
  equations := queryRuntimeProgram.equations.drop RuleExecutionProgram.program.equations.length
  declarations := queryRuntimeProgram.declarations.drop RuleExecutionProgram.program.declarations.length
  initializers := queryRuntimeProgram.initializers.drop RuleExecutionProgram.program.initializers.length
  facts := queryRuntimeProgram.facts.drop RuleExecutionProgram.program.facts.length
  layout := queryRuntimeProgram.layout.drop RuleExecutionProgram.program.layout.length

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_append : queryRuntimeProgram = RuleExecutionProgram.program.append baseExtension := by
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_closed : ProgramClosed baseHeads RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !baseHeads equation.head || codeWithin baseHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_agreement : ProgramAgreementOn baseHeads RuleExecutionProgram.program queryRuntimeProgram := by
  rw [base_append]
  apply appended_program_agreement
  · intro equation member
    have checked : baseExtension.equations.all (fun equation => !baseHeads equation.head) = true := by
      decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : baseHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : baseExtension.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !baseHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : baseHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem base_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin baseHeads code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns queryRuntimeProgram caller state code state answer :=
  path_of_closed_agreement base_closed base_agreement ⟨supported, rfl⟩ returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

abbrev runtime : Program := queryRuntimeProgram
abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
abbrev v (name : String) : Atom := .var name
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev number (value : Nat) : Atom := encoded (.natural value)
abbrev stringValue (value : String) : Atom := encoded (.string value)
abbrev boundValue (bound : List TypeExpr) : Atom := encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
abbrev ruleValue (rule : RewriteRule) : Atom := encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
abbrev assignmentValue (assignment : Assignment) : Atom := encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)
abbrev contextValue (context : Context) : Atom := encoded (contextTerm context)
abbrev queryValue (request : Query.Request) : Atom := encoded (queryRequestTerm request)
abbrev taskValue {env : Environment} {request : Query.Request} (task : Query.Task env request) : Atom := encoded (queryTaskTerm task)
abbrev expansionValue {env : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task env request) (Query.Answer env request) Query.Obligation) : Atom :=
  encoded (encodeOption queryExpansionTerm (some expansion))

def caseData (expression : Atom) (rows : SpaceSemantics.Cases) : Atom :=
  a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]

inductive Helper where
  | site | matchingRequest | expand
  | matchingEnvironment | matchingStart | matchingTick | matchingComplete | matchingAnswer | matchingInput

def Helper.head : Helper → String
  | .site => "gslt:premise:query-site"
  | .matchingRequest => "gslt:premise:query-matching-request"
  | .expand => "gslt:premise:query-expand-in"
  | .matchingEnvironment => "gslt:premise:matching-environment"
  | .matchingStart => "gslt:premise:matching-start"
  | .matchingTick => "gslt:premise:matching-tick"
  | .matchingComplete => "gslt:premise:matching-complete"
  | .matchingAnswer => "gslt:premise:matching-answer-at"
  | .matchingInput => "gslt:premise:matching-input"

def Helper.names : Helper → List String
  | .site => ["context", "argument"]
  | .matchingRequest => ["context", "index", "assignment", "schema", "value"]
  | .expand => ["environment", "request", "task"]
  | .matchingEnvironment => ["environment"]
  | .matchingStart => ["environment", "request"]
  | .matchingTick => ["environment", "request", "state"]
  | .matchingComplete => ["environment", "state"]
  | .matchingAnswer => ["environment", "state", "cursor"]
  | .matchingInput => ["environment", "actual", "expected"]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
local elab "query_source_equation% " head:str : term => do
  let source ← unsafe Lean.Meta.evalExpr Program (Lean.mkConst ``Program)
    (Lean.mkConst ``RuleExecutionProgram.scopedProgram)
  let some equation := source.equations.find? (fun equation => equation.head == head.getString)
    | Lean.throwErrorAt head "authored query clause is absent"
  return Lean.mkApp3 (Lean.mkConst ``SpaceSemantics.Equation.mk)
    (Lean.toExpr equation.head)
    ((equation.arguments.map BridgeKit.atomToExpr).foldr
      (fun value rest => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) (Lean.mkConst ``Atom) value rest)
      (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``Atom)))
    (BridgeKit.atomToExpr equation.body)

/-- Literal clause data read from the loaded authored source. Runtime membership
and uniqueness are certified below, independently of the elaborator. -/
def queryEquation : Helper → SpaceSemantics.Equation
  | .site => query_source_equation% "gslt:premise:query-site"
  | .matchingRequest => query_source_equation% "gslt:premise:query-matching-request"
  | .expand => query_source_equation% "gslt:premise:query-expand-in"
  | .matchingEnvironment => query_source_equation% "gslt:premise:matching-environment"
  | .matchingStart => query_source_equation% "gslt:premise:matching-start"
  | .matchingTick => query_source_equation% "gslt:premise:matching-tick"
  | .matchingComplete => query_source_equation% "gslt:premise:matching-complete"
  | .matchingAnswer => query_source_equation% "gslt:premise:matching-answer-at"
  | .matchingInput => query_source_equation% "gslt:premise:matching-input"

private local instance queryEquationEq : DecidableEq SpaceSemantics.Equation := by
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

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem query_equations (helper : Helper) :
    runtime.equations.filter (fun equation => equation.head == helper.head) = [queryEquation helper] := by
  cases helper <;> decide +kernel

def callee (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (callee helper values) (queryEquation helper).body] :=
  PureData.named_equation_clause runtime helper.head (queryEquation helper) helper.names values
    (query_equations helper) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private def helperInventory : List Helper :=
  [.site, .matchingRequest, .expand, .matchingEnvironment, .matchingStart,
    .matchingTick, .matchingComplete, .matchingAnswer, .matchingInput]

private theorem helper_present (helper : Helper) : helper ∈ helperInventory := by
  cases helper <;> simp [helperInventory]

private def queryTypes (helper : Helper) : List Atom :=
  List.replicate helper.names.length (.symbol "Atom") ++ [.symbol "%Undefined%"]

private def queryDeclaration (helper : Helper) : Atom :=
  .expression [.symbol ":", .symbol helper.head, .expression (.symbol "->" :: queryTypes helper)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem query_declarations_checked :
    helperInventory.all (fun helper => decide (queryDeclaration helper ∈ runtime.declarations)) = true := by
  decide +kernel

private theorem query_declared (helper : Helper) : queryDeclaration helper ∈ runtime.declarations :=
  of_decide_eq_true (List.all_eq_true.mp query_declarations_checked helper (helper_present helper))

theorem query_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  apply (argumentIsRaw_iff_declaredAtom runtime helper.head index (by cases helper <;> decide)).mpr
  refine ⟨queryTypes helper, query_declared helper, ?_⟩
  unfold queryTypes
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using bounded)]
  exact List.getElem?_replicate_of_lt bounded

private theorem query_registered (helper : Helper) :
    runtime.equations.any (·.head == helper.head) = true := by
  have member : queryEquation helper ∈ runtime.equations.filter (fun row => row.head == helper.head) := by
    rw [query_equations helper]
    exact List.mem_cons_self
  have selected := List.mem_filter.mp member
  exact List.any_eq_true.mpr ⟨_, selected.1, selected.2⟩

private theorem query_dispatch (helper : Helper) :
    (ioHead helper.head || StdLib.known helper.head || runtime.equations.any (·.head == helper.head)) = true := by
  simp only [query_registered, Bool.or_true]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (callee helper values) state (queryEquation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (callee helper values) state state
    helper.head arguments (queryEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (query_registered helper)
  · intro index bounded
    apply query_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact query_clause helper values length
  · exact returned

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (query_dispatch helper) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact query_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state (caseData expression rows) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

def dataHeads : List String :=
  ["Some", "LCons", "RulePremise", "ScopedMatcherRequest", "PremiseExpansion", "PremiseSignatureUnavailable",
    "PremiseInputUnavailable", "PremiseArgumentShape", "PremiseQueryRows", "PremiseQueryArguments",
    "PremiseQueryAnswer", "PremiseQueryMatcher", "ArgumentOrigin"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem data_template (head : String) (arguments : List Atom)
    (supported : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  have checked : dataHeads.all (fun name => decide
      ((ioHead name || StdLib.known name || runtime.equations.any (·.head == name)) = false ∧
        name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"])) = true := by
    rfl
  have row := List.all_eq_true.mp checked head supported
  rw [decide_eq_true_eq] at row
  exact .constructor head arguments row.1 row.2 children

def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [.symbol "case", _, .expression rows] => (readCases rows).getD []
  | _ => []

def siteCases : SpaceSemantics.Cases := sourceCases (queryEquation .site).body

def matchingRequestCases : SpaceSemantics.Cases := sourceCases (queryEquation .matchingRequest).body

def environmentCases : SpaceSemantics.Cases := sourceCases (queryEquation .expand).body

def requestCases : SpaceSemantics.Cases := sourceCases ((environmentCases.head!).2)

def taskCases : SpaceSemantics.Cases := sourceCases ((requestCases.head!).2)

def taskBody (index : Nat) : Atom := ((taskCases[index]?).getD (.symbol "unreachable", .symbol "None")).2

theorem site_shape : (queryEquation .site).body = caseData (v "context") siteCases := by decide +kernel

theorem matching_request_shape : (queryEquation .matchingRequest).body = caseData (v "context") matchingRequestCases := by decide +kernel

theorem expand_shape : (queryEquation .expand).body = caseData (a "gslt:premise:matching-environment" [v "environment"]) environmentCases := by decide +kernel

theorem environment_case_shape : (environmentCases.head!).2 = caseData (v "request") requestCases := by decide +kernel

theorem request_case_shape : (requestCases.head!).2 = caseData (v "task") taskCases := by decide +kernel

def contextCaller (context : Context) (caller : Subst) : Subst :=
  [("quantifiers", number context.quantifierDepth), ("premise", number context.premiseIndex),
    ("bound", boundValue context.bound), ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm context.spec)),
    ("rule", ruleValue context.rule), ("ruleIndex", number context.ruleIndex)] ++ caller

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem length_returns {α : Type} (encoder : α → Term) (caller : Subst) (state : State)
    (values : List α) (input : String)
    (captured : applySubst caller (v input) = encoded (encodeList encoder values)) :
    PureReturns runtime caller state (a "gslt:automata:length" [v input]) state (number values.length) := by
  have returned := MatchAutomataSourceExecution.length_captured_returns caller state
    (values.map encoder) (v input) (by
      simpa only [MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)
  have transferred := base_returns (by simp [codeWithin, expressionHeadWithin]; decide +kernel)
    (RuleExecutionProgram.automata_captured_returns
      (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead]) returned)
  simpa only [List.length_map] using transferred


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def querySiteCasesSyntax : SpaceSemantics.Cases :=
  [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], a "RulePremise" [v "premise", v "quantifiers", v "argument"]),
    (v "bad", .symbol "None")]

def queryMatchingCasesSyntax : SpaceSemantics.Cases :=
  [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]], .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0, v "assignment", v "schema", v "value"]]),
    (v "bad", .symbol "None")]

theorem site_cases_syntax : siteCases = querySiteCasesSyntax := by decide +kernel

theorem matching_cases_syntax : matchingRequestCases = queryMatchingCasesSyntax := by decide +kernel

theorem environment_cases_syntax : environmentCases =
  [(a "PremiseEnvironment" [v "declarations", v "rewrites", v "specifications", a "PremiseProvider" [v "signatures", v "rows"], v "reflection", v "free"], caseData (v "request") requestCases),
    (v "badEnvironment", .symbol "None")] := by decide +kernel

theorem request_cases_syntax : requestCases =
  [(a "PremiseQueryRequest" [a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], v "relation", v "arguments", v "initial"], caseData (v "task") taskCases),
    (v "badRequest", .symbol "None")] := by decide +kernel

theorem task_cases_syntax : taskCases =
  [(.symbol "PremiseQueryStart", taskBody 0),
    (a "PremiseQueryRows" [v "signature", v "cursor"], taskBody 1),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", .symbol "LNil", .symbol "LNil", .symbol "LNil", v "origins"], taskBody 2),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", a "LCons" [v "schema", v "schemas"], a "LCons" [v "value", v "values"], a "LCons" [.symbol "RelationInput", v "modes"], v "origins"], taskBody 3),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", a "LCons" [v "schema", v "schemas"], a "LCons" [v "value", v "values"], a "LCons" [.symbol "RelationOutput", v "modes"], v "origins"], taskBody 4),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", v "schemas", v "values", v "modes", v "origins"], taskBody 5),
    (a "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "state", v "cursor"], taskBody 6),
    (v "badTask", taskBody 7)] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

local macro "query_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem query_site_returns (state : State) (context : Context) (index : Nat) :
    PureReturns runtime [] state
      (a "gslt:premise:query-site" [contextValue context, number index]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) := by
  let caller := callee .site [contextValue context, number index]
  let selected := contextCaller context caller
  apply query_call .site [] state _ _ _ rfl (captured_closed _)
  rw [site_shape]
  apply branch_returns caller selected state _ (contextValue context) siteCases
    (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "context"
  · simp [site_cases_syntax, querySiteCasesSyntax, contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have templated : PureData.Template runtime (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) := by
      query_template
    simpa [GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
      selected, contextCaller, caller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return runtime selected state _ templated

theorem query_site_captured_returns (caller : Subst) (state : State) (context : Context) (index : Nat)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [contextValue context, number index]) :
    PureReturns runtime caller state (a "gslt:premise:query-site" [one, two]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) :=
  query_capture .site caller state _ _ _ rfl captured (query_site_returns state context index)

private def matchingRequestData : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0,
    v "assignment", v "schema", v "value"]

private def matchingRequestBody : Atom :=
  a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], matchingRequestData]

private theorem matching_request_case_body : (matchingRequestCases.head!).2 = matchingRequestBody := by decide +kernel

theorem query_matching_request_returns (state : State) (request : Query.Request) (index : Nat)
    (assignment : Assignment) (schema value : Pattern) :
    PureReturns runtime [] state
      (a "gslt:premise:query-matching-request" [contextValue request.context, number index,
        assignmentValue assignment, patternValue schema, patternValue value]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) := by
  let caller := callee .matchingRequest [contextValue request.context, number index,
    assignmentValue assignment, patternValue schema, patternValue value]
  let selected := contextCaller request.context caller
  let ambient := ("ambient", number request.context.bound.length) :: selected
  let final := ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index))) :: ambient
  apply query_call .matchingRequest [] state _ _ _ rfl (captured_closed _)
  rw [matching_request_shape]
  apply branch_returns caller selected state _ (contextValue request.context) matchingRequestCases matchingRequestBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "context"
  · simp [matching_cases_syntax, queryMatchingCasesSyntax, matchingRequestBody, matchingRequestData,
      contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold matchingRequestBody
    apply PureData.let_bindings_return (pairs := [
      (v "ambient", a "gslt:automata:length" [v "bound"]),
      (v "site", a "gslt:premise:query-site" [v "context", v "index"])])
      (final := final) (middle := state) _ state matchingRequestData _ _
    · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state)
        (value := number request.context.bound.length)
      · exact length_returns InferenceCettaWire.AuthoredRule.typeTerm selected state request.context.bound "bound"
          (by simp [selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
          (value := encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index)))
        · exact query_site_captured_returns ambient state request.context index (v "context") (v "index")
            (by simp [ambient, selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            final, ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
        · exact .nil final state
    · have templated : PureData.Template runtime matchingRequestData := by unfold matchingRequestData; query_template
      simpa [matchingRequestData, Query.matchingRequest,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
        final, ambient, selected, contextCaller, caller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime final state _ templated

theorem query_matching_request_captured_returns (caller : Subst) (state : State)
    (request : Query.Request) (index : Nat) (assignment : Assignment) (schema value : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [contextValue request.context, number index, assignmentValue assignment, patternValue schema, patternValue value]) :
    PureReturns runtime caller state (a "gslt:premise:query-matching-request" [one, two, three, four, five]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) :=
  query_capture .matchingRequest caller state _ _ _ rfl captured
    (query_matching_request_returns state request index assignment schema value)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

local macro "query_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

abbrev environmentValue (environment : Environment) (free : List (String × TypeExpr)) : Atom :=
  encoded (environmentTerm environment free)

def environmentCaller (environment : Environment) (free : List (String × TypeExpr)) (caller : Subst) : Subst :=
  [("free", encoded (DeclarationTyping.freeContextTerm free)),
    ("reflection", encoded (reflectionTerm environment.reflection)),
    ("rows", encoded (encodeList providerRowTerm environment.provider.rows)),
    ("signatures", encoded (encodeList signatureTerm environment.provider.signatures)),
    ("specifications", encoded (encodeList specificationTerm environment.specifications)),
    ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)),
    ("declarations", encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm environment.language.terms))] ++ caller

def requestCaller (request : Query.Request) (caller : Subst) : Subst :=
  [("initial", assignmentValue request.initial), ("arguments", patternsValue request.arguments),
    ("relation", stringValue request.relation)] ++ contextCaller request.context caller

def frameCaller (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request) (free : List (String × TypeExpr)) : Subst :=
  requestCaller request (environmentCaller environment free
    (callee .expand [environmentValue environment free, queryValue request, taskValue task]))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

private def sourceHeadGroups : List (List String) :=
  [([Helper.site.head, Helper.matchingRequest.head, Helper.expand.head, "+", "=="] ++ dataHeads),
    [Helper.matchingEnvironment.head, Helper.matchingStart.head, Helper.matchingTick.head,
      Helper.matchingComplete.head, Helper.matchingAnswer.head, Helper.matchingInput.head],
    ["gslt:rule:row-at", "gslt:automata:length", "gslt:automata:append", "gslt:premise:signature",
      "gslt:premise:check-row", "gslt:premise:check-assignment"],
    ["gslt:rule:scope-instantiate-at"],
    ["gslt:rule:scope-matcher-start", "gslt:rule:scope-matcher-tick", "gslt:rule:scope-matcher-complete"]]

def ownedHeads (head : String) : Bool := sourceHeadGroups.flatten.contains head

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helper_supported (helper : Helper) : ownedHeads helper.head = true := by cases helper <;> decide

theorem helper_clause (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (values : List Atom) (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (callee helper values) (queryEquation helper).body] := by
  apply PureData.selected_clause_agreement agreement (helper_supported helper)
  exact query_clause helper values length

theorem helper_raw (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  rw [← agreement.demand helper.head index (helper_supported helper)]
  exact query_raw helper index bounded

theorem helper_call (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (callee helper values) state (queryEquation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (callee helper values) state state
    helper.head arguments (queryEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide) _ _ _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    exact query_registered helper
  · intro index bounded
    apply helper_raw program agreement helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause program agreement helper values length

theorem helper_capture (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    _ _ (by cases helper <;> decide) _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    exact query_dispatch helper
  · intro index bounded
    exact helper_raw program agreement helper index (by omega)
  · simpa only [captured_closed] using captured.symm

theorem data_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have supported : ownedHeads head = true := by simp [ownedHeads, sourceHeadGroups, member]
    rw [← agreement.dispatch head supported]
    have checked : dataHeads.all (fun name => decide
        ((ioHead name || StdLib.known name || runtime.equations.any (·.head == name)) = false ∧
          name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"])) = true := by
      rfl
    have row := List.all_eq_true.mp checked head member
    rw [decide_eq_true_eq] at row
    exact row.1
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem branch_returns (program : Program) (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns program caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program caller state (caseData expression rows) state answer :=
  case_returns program caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

theorem bool_if_returns (program : Program) (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem named_let_returns (program : Program) (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

theorem add_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (caller : Subst) (state : State) (left right : Nat) (one two : Atom)
    (first : PureReturns program caller state one state (number left))
    (second : PureReturns program caller state two state (number right)) :
    PureReturns program caller state (a "+" [one, two]) state (number (left + right)) := by
  have supported : ownedHeads "+" = true := by decide
  apply native_binary_call_returns program caller state state state state "+"
    one two (number left) (number right) (number (left + right))
    (by decide) (by decide) _ _ first second _ (by decide)
  · rw [← agreement.demand "+" 0 supported]; decide +kernel
  · rw [← agreement.demand "+" 1 supported]; decide +kernel
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
      StdLib.integer_addition state (left : Int) (right : Int)

structure LowerOperations (program : Program) : Prop where
  row : ∀ (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [number index, encoded (encodeList id values)] →
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?))
  length : ∀ (caller : Subst) (state : State) (values : List Term) (input : Atom),
    applySubst caller input = encoded (encodeList id values) →
    PureReturns program caller state (a "gslt:automata:length" [input]) state (number values.length)
  append : ∀ (caller : Subst) (state : State) (left right : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [encoded (encodeList id left), encoded (encodeList id right)] →
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (encoded (encodeList id (left ++ right)))
  signature : ∀ (caller : Subst) (state : State) (provider : ProviderSnapshot) (relation : String) (arity : Nat)
    (one two three : Atom),
    [one, two, three].map (applySubst caller) = [stringValue relation, number arity, encoded (providerTerm provider)] →
    PureReturns program caller state (a "gslt:premise:signature" [one, two, three]) state
      (encoded (encodeOption signatureTerm (signature? provider relation arity)))
  rowTyped : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signature : Signature) (row : ProviderRow) (one two three four five : Atom),
    [one, two, three, four, five].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free),
        boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)] →
    PureReturns program caller state (a "gslt:premise:check-row" [one, two, three, four, five]) state
      (Effects.boolean (checkRow language (FreeTypeContext.ofList free) bound signature row))
  assignment : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment)
    (one two three four five six : Atom),
    [one, two, three, four, five, six].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free),
        boundValue bound, ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment] →
    PureReturns program caller state (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language (FreeTypeContext.ofList free) bound rule spec assignment))
  start : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom),
    applySubst caller input = encoded (matcherRequestTerm request) →
    PureReturns program caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (encoded (matcherStateTerm (GeneralScopedMatchMachine.start request)))
  tick : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom),
    [one, two].map (applySubst caller) = [encoded (matcherRequestTerm request), encoded (matcherStateTerm machine)] →
    PureReturns program caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (encoded (matcherStateTerm (GeneralScopedMatchMachine.tick request machine)))
  complete : ∀ (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom),
    applySubst caller input = encoded (matcherStateTerm machine) →
    PureReturns program caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine))
  instantiate : ∀ (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment : Assignment)
    (pattern : Pattern) (one two three four five six seven eight nine : Atom),
    [one, two, three, four, five, six, seven, eight, nine].map (applySubst caller) =
      [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
        number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path),
        number depth, assignmentValue assignment, patternValue pattern] →
    PureReturns program caller state (a "gslt:rule:scope-instantiate-at" [one, two, three, four, five, six, seven, eight, nine]) state
      (encoded (encodeOption InferenceCettaWire.encodePattern (instantiateAt? rule spec ambient site path depth assignment pattern)))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem length_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (values : List α) (input : String)
    (captured : applySubst caller (v input) = encoded (encodeList encoder values)) :
    PureReturns program caller state (a "gslt:automata:length" [v input]) state (number values.length) := by
  simpa only [List.length_map] using lower.length caller state (values.map encoder) (v input)
    (by simpa only [encodeList_map, Function.id_comp] using captured)

theorem append_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (left right : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (encodeList encoder left), encoded (encodeList encoder right)]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state
      (encoded (encodeList encoder (left ++ right))) := by
  simpa only [← List.map_append, encodeList_map, Function.id_comp] using
    lower.append caller state (left.map encoder) (right.map encoder) one two
      (by simpa only [encodeList_map, Function.id_comp] using captured)

theorem row_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (index : Nat) (values : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [number index, encoded (encodeList encoder values)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption encoder values[index]?)) := by
  have returned := lower.row caller state index (values.map encoder) one two
    (by simpa only [encodeList_map, Function.id_comp] using captured)
  cases found : values[index]? <;> simpa [List.getElem?_map, found, encodeOption] using returned

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem query_site_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (state : State) (context : Context) (index : Nat) :
    PureReturns program [] state
      (a "gslt:premise:query-site" [contextValue context, number index]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) := by
  let caller := callee .site [contextValue context, number index]
  let selected := contextCaller context caller
  apply helper_call program agreement .site [] state _ _ _ rfl (captured_closed _)
  rw [site_shape]
  apply branch_returns program caller selected state _ (contextValue context) siteCases
    (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "context"
  · simp [site_cases_syntax, querySiteCasesSyntax, contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have templated : PureData.Template program (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) := by
      query_template (program) (agreement)
    simpa [GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
      selected, contextCaller, caller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program selected state _ templated

theorem query_site_captured_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (caller : Subst) (state : State) (context : Context) (index : Nat)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [contextValue context, number index]) :
    PureReturns program caller state (a "gslt:premise:query-site" [one, two]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) :=
  helper_capture program agreement .site caller state _ _ _ rfl captured (query_site_returns program agreement state context index)

private def matchingRequestData : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0,
    v "assignment", v "schema", v "value"]

private def matchingRequestBody : Atom :=
  a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], matchingRequestData]

private theorem matching_request_case_body : (matchingRequestCases.head!).2 = matchingRequestBody := by decide +kernel

theorem query_matching_request_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (state : State) (request : Query.Request) (index : Nat)
    (assignment : Assignment) (schema value : Pattern) :
    PureReturns program [] state
      (a "gslt:premise:query-matching-request" [contextValue request.context, number index,
        assignmentValue assignment, patternValue schema, patternValue value]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) := by
  let caller := callee .matchingRequest [contextValue request.context, number index,
    assignmentValue assignment, patternValue schema, patternValue value]
  let selected := contextCaller request.context caller
  let ambient := ("ambient", number request.context.bound.length) :: selected
  let final := ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index))) :: ambient
  apply helper_call program agreement .matchingRequest [] state _ _ _ rfl (captured_closed _)
  rw [matching_request_shape]
  apply branch_returns program caller selected state _ (contextValue request.context) matchingRequestCases matchingRequestBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "context"
  · simp [matching_cases_syntax, queryMatchingCasesSyntax, matchingRequestBody, matchingRequestData,
      contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold matchingRequestBody
    apply PureData.let_bindings_return (pairs := [
      (v "ambient", a "gslt:automata:length" [v "bound"]),
      (v "site", a "gslt:premise:query-site" [v "context", v "index"])])
      (final := final) (middle := state) _ state matchingRequestData _ _
    · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state)
        (value := number request.context.bound.length)
      · exact length_encoded_returns program lower InferenceCettaWire.AuthoredRule.typeTerm selected state request.context.bound "bound"
          (by simp [selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
          (value := encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index)))
        · exact query_site_captured_returns program agreement ambient state request.context index (v "context") (v "index")
            (by simp [ambient, selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            final, ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
        · exact .nil final state
    · have templated : PureData.Template program matchingRequestData := by unfold matchingRequestData; query_template (program) (agreement)
      simpa [matchingRequestData, Query.matchingRequest,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
        final, ambient, selected, contextCaller, caller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program final state _ templated

theorem query_matching_request_captured_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (caller : Subst) (state : State)
    (request : Query.Request) (index : Nat) (assignment : Assignment) (schema value : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [contextValue request.context, number index, assignmentValue assignment, patternValue schema, patternValue value]) :
    PureReturns program caller state (a "gslt:premise:query-matching-request" [one, two, three, four, five]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) :=
  helper_capture program agreement .matchingRequest caller state _ _ _ rfl captured
    (query_matching_request_returns program agreement lower state request index assignment schema value)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)

theorem symbol_constructor_mismatch (caller : Subst) (symbol head : String) (values : List Atom) :
    SpaceSemantics.matchValue caller (.symbol symbol) (a head values) = none := by
  simp [a, SpaceSemantics.matchValue, matchAtom]

theorem constructor_head_mismatch (caller : Subst) (left right : String) (patterns values : List Atom)
    (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.matchValue caller (a left patterns) (a right values) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  rw [SpaceSemantics.matchValue.matchValues]
  simp only [SpaceSemantics.matchValue, matchAtom, beq_iff_eq,
    if_neg different, Option.bind_eq_bind]
  rfl

theorem select_skip_constructor (caller : Subst) (left right : String) (patterns values : List Atom)
    (body : Atom) (rest : SpaceSemantics.Cases) (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.selectCase caller (a right values) ((a left patterns, body) :: rest) =
      SpaceSemantics.selectCase caller (a right values) rest := by
  rw [SpaceSemantics.selectCase, constructor_head_mismatch caller left right patterns values ordinary different]


theorem constructor_variables_match (caller : Subst) (head : String) (names : List String) (values : List Atom)
    (ordinary : head ≠ "cons") (distinct : names.Nodup) (length : values.length = names.length)
    (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.matchValue caller (a head (names.map v)) (a head values) =
      some ((names.zip values).reverse ++ caller) := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  simp only [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue, matchAtom,
    beq_self_eq_true, Option.bind_eq_bind]
  exact PureData.match_variable_values names values caller distinct length fresh


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.helper_capture
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.data_template
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval BridgeKit WireKit

private abbrev v (name : String) : Atom := .var name

def equation : SpaceSemantics.Equation := queryEquation .expand

def formals : List String := ["environment", "request", "task"]

def callerFor (values : List Atom) : Subst := (formals.zip values).reverse

theorem raw_arguments (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (index : Nat) (bounded : index < 3) :
    argumentIsRaw program "gslt:premise:query-expand-in" index = true :=
  Parameterized.helper_raw program agreement .expand index bounded

theorem call (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (caller : Subst) (host : Effects.State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = 3) (captured : arguments.map (applySubst caller) = values)
    (body : PureReturns program (callerFor values) host equation.body host answer) :
    PureReturns program caller host (WireKit.apply "gslt:premise:query-expand-in" arguments) host answer :=
  Parameterized.helper_call program agreement .expand caller host arguments values answer length captured body

theorem template_in_program (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    {code : Atom} (template : PureData.Template runtime code)
    (supported : codeWithin Parameterized.ownedHeads code = true) : PureData.Template program code := by
  induction template with
  | captured name => exact .captured name
  | grounded value => exact .grounded value
  | symbol name => exact .symbol name
  | constructor head arguments inert ordinary children ih =>
      simp only [codeWithin, expressionHeadWithin, Bool.and_eq_true, atomsWithin_eq_all, List.all_eq_true] at supported
      refine .constructor head arguments ?_ ordinary ?_
      · rw [← agreement.dispatch head supported.1.1]
        exact inert
      · intro child member
        exact ih child member (supported.2 child (List.mem_cons_of_mem _ member))

theorem data_in_program_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (caller : Subst) (host : Effects.State) (code answer : Atom)
    (checked : BridgeKit.templateCheck runtime code = true)
    (supported : codeWithin Parameterized.ownedHeads code = true)
    (same : applySubst caller code = answer) : PureReturns program caller host code host answer :=
  same ▸ PureData.template_return program caller host code
    (template_in_program program agreement (BridgeKit.template_of_check runtime code checked) supported)

syntax "query_capture " term:max term:max term:max (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| query_capture $program $agreement $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (refine PureData.raw_capture_returns $program [] _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ $fact
       · rw [← ($agreement).dispatch _ (by decide +kernel)]
         decide +kernel
       · intro index bounded
         rw [← ($agreement).demand _ index (by decide +kernel)]
         simp only [List.length_cons, List.length_nil, Nat.zero_add] at bounded
         revert index
         decide +kernel
       · decide
       · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, List.map_cons, List.map_nil,
           CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany,
           $extra,*]))

syntax "query_eval " term:max term:max (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| query_eval $program $agreement $[[$lemmas,*]]? $[unfolding [$unfold,*]]?) => do
    let lemmas := (lemmas.map (·.getElems)).getD #[]
    let unfold := (unfold.map (·.getElems)).getD #[]
    let unfoldLemmas ← unfold.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    let recurse ← `(tactic| query_eval $program $agreement [$lemmas,*] unfolding [$unfold,*])
    let again ← `(tacticSeq| $recurse:tactic)
    let nothing ← `(tactic| fail "query_eval: no supplied fact closes this call")
    let captures ← lemmas.foldlM (init := nothing) fun rest fact =>
      `(tactic| first | query_capture $program $agreement $fact unfolding [$unfold,*] | $(⟨rest.raw⟩):tacticSeq)
    let capturing ← `(tacticSeq| $captures:tactic)
    `(tactic| first
      | exact bound_returns _ _ _ (by rfl)
      | exact literal_returns _ _ _ _
      | exact Eval.symbol_returns _ _ _ _
      | focus
          (refine bound_answer_returns _ _ _ (by rfl) ?_
           simp [encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany, $unfoldLemmas,*]
           done)
      | focus
          (apply data_in_program_returns $program $agreement _ _ _ _ (by decide +kernel) (by decide +kernel)
           first
             | (rfl; done)
             | skip
           try simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
             Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
             Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, encoded, number,
             CettaWireAtom.encode, CettaWireAtom.encodeMany, $unfoldLemmas,*]
           done)
      | (apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
         $recurse
         try $again)
      | (apply pure_let_star_returns _ _ _ _ _ _ _ rfl
         try $again)
      | (apply pure_if_returns
         $recurse
         first
           | (simp only [decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_one_ne_zero,
               Nat.succ_ne_zero, decide_eq_true_eq, eq_self_iff_true, Mettapedia.GSLT.LanguageDef.CettaWire.Term.string.injEq,
               Mettapedia.GSLT.LanguageDef.CettaWire.Term.natural.injEq,
               $unfoldLemmas,*]
              try $again)
           | try $again)
      | (apply pure_case_returns _ _ _ _ _ _ _ _ rfl
         $recurse
         try (focus (metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number, $unfold,*]; done))
         try (intro selected body selection
              metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number, $unfold,*] at selection
              obtain ⟨bindings, branch⟩ := selection
              subst bindings
              subst branch
              try $again))
      | (apply natural_equal_returns) <;> $recurse
      | (apply string_equal_returns) <;> $recurse
      | (apply term_equal_returns) <;> $recurse
      | (apply natural_le_returns) <;> $recurse
      | (apply natural_lt_returns) <;> $recurse
      | (apply natural_add_returns) <;> $recurse
      | (apply natural_pred_returns) <;> $recurse
      | $capturing)

def taskValue {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher) (task : Query.Task environment request matcher) : Atom :=
  encoded (RetainedMatchingWire.queryTaskTerm codec task)

def expansionTerm {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (expansion : Scheduler.Expansion (Query.Task environment request matcher)
      (Query.Answer environment request matcher) Query.Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm (RetainedMatchingWire.queryTaskTerm codec)
    (RetainedMatchingWire.queryAnswerTerm codec)
    PremiseOperationsExecution.GeneralExecution.queryObligationTerm expansion

def expansionValue {environment : Environment} {request : Query.Request} {matcher : MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (expansion : Scheduler.Expansion (Query.Task environment request matcher)
      (Query.Answer environment request matcher) Query.Obligation) : Atom :=
  encoded (encodeOption (expansionTerm codec) (some expansion))

def environmentCases : SpaceSemantics.Cases := sourceCases equation.body

def requestCases : SpaceSemantics.Cases := sourceCases ((environmentCases.head!).2)

def taskCases : SpaceSemantics.Cases := sourceCases ((requestCases.head!).2)

def taskBody (index : Nat) : Atom := ((taskCases[index]?).getD (.symbol "unreachable", .symbol "None")).2

theorem expand_shape : equation.body =
    caseData (WireKit.apply "gslt:premise:matching-environment" [v "environment"]) environmentCases := by decide +kernel

theorem environment_case_shape : (environmentCases.head!).2 = caseData (v "request") requestCases := by decide +kernel

theorem request_case_shape : (requestCases.head!).2 = caseData (v "task") taskCases := by decide +kernel

theorem environment_cases_syntax : environmentCases =
  [(WireKit.apply "PremiseEnvironment" [v "declarations", v "rewrites", v "specifications", WireKit.apply "PremiseProvider" [v "signatures", v "rows"], v "reflection", v "free"], caseData (v "request") requestCases),
    (v "badEnvironment", .symbol "None")] := by decide +kernel

theorem request_cases_syntax : requestCases =
  [(WireKit.apply "PremiseQueryRequest" [WireKit.apply "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], v "relation", v "arguments", v "initial"], caseData (v "task") taskCases),
    (v "badRequest", .symbol "None")] := by decide +kernel

theorem task_cases_syntax : taskCases =
  [(.symbol "PremiseQueryStart", taskBody 0),
    (WireKit.apply "PremiseQueryRows" [v "signature", v "cursor"], taskBody 1),
    (WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", .symbol "LNil", .symbol "LNil", .symbol "LNil", v "origins"], taskBody 2),
    (WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", WireKit.apply "LCons" [v "schema", v "schemas"], WireKit.apply "LCons" [v "value", v "values"], WireKit.apply "LCons" [.symbol "RelationInput", v "modes"], v "origins"], taskBody 3),
    (WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", WireKit.apply "LCons" [v "schema", v "schemas"], WireKit.apply "LCons" [v "value", v "values"], WireKit.apply "LCons" [.symbol "RelationOutput", v "modes"], v "origins"], taskBody 4),
    (WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", v "schemas", v "values", v "modes", v "origins"], taskBody 5),
    (WireKit.apply "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "state", v "cursor"], taskBody 6),
    (v "badTask", taskBody 7)] := by decide +kernel

private def emptyData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def answerData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [
    WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "nextArgument", v "assignment", v "schemas", v "values", v "modes", v "extended"],
    WireKit.apply "LCons" [WireKit.apply "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins",
      v "query", v "state", v "nextCursor"], .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]

private def answerBody : Atom :=
  WireKit.apply "let*" [.expression [
    .expression [v "nextArgument", WireKit.apply "+" [v "argument", number 1]],
    .expression [v "nextCursor", WireKit.apply "+" [v "cursor", number 1]],
    .expression [v "extended", WireKit.apply "gslt:automata:append" [v "origins",
      WireKit.apply "LCons" [WireKit.apply "ArgumentOrigin" [v "argument", v "trace"], .symbol "LNil"]]]], answerData]

private def steppedData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [
    WireKit.apply "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "stepped", v "cursor"],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def stopBody : Atom :=
  WireKit.apply "if" [WireKit.apply "gslt:premise:matching-complete" [v "environment", v "state"], emptyData,
    WireKit.apply "let" [v "stepped", WireKit.apply "gslt:premise:matching-tick" [v "environment", v "query", v "state"], steppedData]]

private def answerCases : SpaceSemantics.Cases :=
  [(WireKit.apply "Some" [WireKit.apply "ScopedMatcherAnswer" [v "assignment", v "trace"]], answerBody),
    (.symbol "None", stopBody), (v "badAnswer", .symbol "None")]

private def matcherBody : Atom :=
  caseData (WireKit.apply "gslt:premise:matching-answer-at" [v "environment", v "state", v "cursor"]) answerCases

private theorem matcher_shape : taskBody 6 = matcherBody := by decide +kernel

def frameCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request) (task : Query.Task environment request matcher)
    (free : List (String × TypeExpr)) (profile : Term) : Subst :=
  requestCaller request (environmentCaller environment free
    (callerFor [encoded profile, encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request),
      taskValue codec task]))

def matcherCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request) (frame : Query.MatcherFrame environment request matcher)
    (free : List (String × TypeExpr)) (profile : Term) : Subst :=
  [("cursor", number frame.cursor), ("state", encoded (codec.stateTerm frame.state)),
    ("query", encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm frame.query)),
    ("origins", encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins)),
    ("modes", encoded (encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes)),
    ("values", encoded (InferenceCettaWire.encodePatterns frame.values)),
    ("schemas", encoded (InferenceCettaWire.encodePatterns frame.schemas)),
    ("argument", number frame.argumentIndex), ("rowIndex", number frame.rowIndex)] ++
    frameCaller codec environment request (.matcher frame) free profile

theorem expand_branch_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (task : Query.Task environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (selected : Subst) (body answer : Atom)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (matched : SpaceSemantics.selectCase (frameCaller codec environment request task free profile)
      (taskValue codec task) taskCases = some (selected, body))
    (continued : PureReturns program selected host body host answer) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec task])
      host answer := by
  let caller := callerFor [encoded profile,
    encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec task]
  let envCaller := environmentCaller environment free caller
  let reqCaller := requestCaller request envCaller
  apply call program agreement [] host _ _ _ rfl (captured_closed _)
  rw [expand_shape]
  apply Parameterized.branch_returns program caller envCaller host _
    (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))
    environmentCases (environmentCases.head!).2 _
  · query_capture program agreement view unfolding [caller, callerFor, formals]
  · simp [environment_cases_syntax, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm, envCaller, environmentCaller,
      caller, callerFor, formals, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [environment_case_shape]
    apply Parameterized.branch_returns program envCaller reqCaller host _
      (encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request))
      requestCases (requestCases.head!).2 _
    · simpa [envCaller, environmentCaller, caller, callerFor, formals, applySubst, Subst.lookup] using
        variable_returns program envCaller host "request"
    · simp [request_cases_syntax, PremiseOperationsExecution.GeneralExecution.queryRequestTerm,
        PremiseOperationsExecution.GeneralExecution.contextTerm, reqCaller, requestCaller, contextCaller,
        envCaller, environmentCaller, caller, callerFor, formals, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [request_case_shape]
      apply Parameterized.branch_returns program reqCaller selected host _ (taskValue codec task) taskCases body _
      · simpa [reqCaller, requestCaller, contextCaller, envCaller, environmentCaller, caller,
          callerFor, formals, applySubst, Subst.lookup] using variable_returns program reqCaller host "task"
      · exact matched
      · exact continued

theorem matcher_branch_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.MatcherFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (answer : Atom)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (continued : PureReturns program (matcherCaller codec environment request frame free profile) host matcherBody host answer) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.matcher frame)])
      host answer := by
  apply expand_branch_returns program agreement host environment request matcher codec (.matcher frame) free profile
    (matcherCaller codec environment request frame free profile) matcherBody answer view _ continued
  let values : List Atom := [number frame.rowIndex, number frame.argumentIndex,
    encoded (InferenceCettaWire.encodePatterns frame.schemas), encoded (InferenceCettaWire.encodePatterns frame.values),
    encoded (encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes),
    encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins),
    encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm frame.query),
    encoded (codec.stateTerm frame.state), number frame.cursor]
  have taskWire : taskValue codec (.matcher frame) = WireKit.apply "PremiseQueryMatcher" values := rfl
  rw [task_cases_syntax, taskWire]
  rw [SpaceSemantics.selectCase, Parameterized.symbol_constructor_mismatch]
  rw [Parameterized.select_skip_constructor _ "PremiseQueryRows" "PremiseQueryMatcher" _ _ _ _ (by decide) (by decide)]
  iterate 4 rw [Parameterized.select_skip_constructor _ "PremiseQueryArguments" "PremiseQueryMatcher" _ _ _ _ (by decide) (by decide)]
  rw [SpaceSemantics.selectCase]
  have matched := Parameterized.constructor_variables_match (frameCaller codec environment request (.matcher frame) free profile)
    "PremiseQueryMatcher" ["rowIndex", "argument", "schemas", "values", "modes", "origins", "query", "state", "cursor"]
    values (by decide) (by decide) (by rfl) (by
      intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals, Subst.lookup])
  have fields : SpaceSemantics.matchValue (frameCaller codec environment request (.matcher frame) free profile)
      (WireKit.apply "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "state", v "cursor"])
      (WireKit.apply "PremiseQueryMatcher" values) = some (matcherCaller codec environment request frame free profile) := by
    simpa [values, matcherCaller] using matched
  rw [fields, matcher_shape]

theorem matcher_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.MatcherFrame environment request matcher)
    (free : List (String × TypeExpr)) (profile : Term)
    (view : PureReturns program [] host
      (WireKit.apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (lookup : PureReturns program [] host
      (WireKit.apply "gslt:premise:matching-answer-at" [encoded profile, encoded (codec.stateTerm frame.state), number frame.cursor])
      host (encoded (encodeOption (RetainedMatchingWire.matcherAnswerTerm codec)
        (matcher.answers frame.state)[frame.cursor]?)))
    (finished : PureReturns program [] host
      (WireKit.apply "gslt:premise:matching-complete" [encoded profile, encoded (codec.stateTerm frame.state)])
      host (Effects.boolean (matcher.complete frame.state)))
    (stepped : PureReturns program [] host
      (WireKit.apply "gslt:premise:matching-tick" [encoded profile,
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm frame.query),
        encoded (codec.stateTerm frame.state)])
      host (encoded (codec.stateTerm (matcher.tick frame.query frame.state))))
    (append : ∀ left right : List (Nat × List matcher.Choice),
      PureReturns program [] host (WireKit.apply "gslt:automata:append"
        [encoded (RetainedMatchingWire.originsTerm codec.choiceTerm left),
          encoded (RetainedMatchingWire.originsTerm codec.choiceTerm right)])
        host (encoded (RetainedMatchingWire.originsTerm codec.choiceTerm (left ++ right)))) :
    PureReturns program [] host
      (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
        encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.matcher frame)])
      host (expansionValue codec (Query.expand environment request (.matcher frame))) := by
  simp only [Query.expand, Query.expandMatcher]
  split
  · rename_i answer found
    have row := lookup
    simp only [found] at row
    have appended := append frame.origins [(frame.argumentIndex, matcher.trace answer)]
    apply matcher_branch_returns program agreement host environment request matcher codec frame free profile _ view
    unfold matcherBody
    query_eval program agreement [view, row, appended] unfolding [answerCases, answerBody, stopBody, answerData, steppedData, emptyData,
      matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
      callerFor, formals, taskValue, expansionValue, expansionTerm,
      Query.expand, Query.expandMatcher, found, RetainedMatchingWire.queryTaskTerm,
      RetainedMatchingWire.queryAnswerTerm, RetainedMatchingWire.matcherAnswerTerm,
      RetainedMatchingWire.originsTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
      PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]
  · rename_i found
    have row := lookup
    simp only [found] at row
    cases completed : matcher.complete frame.state with
    | true =>
      apply matcher_branch_returns program agreement host environment request matcher codec frame free profile _ view
      unfold matcherBody
      query_eval program agreement [view, row, finished] unfolding [answerCases, answerBody, stopBody, answerData, steppedData, emptyData,
      matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
      callerFor, formals, taskValue, expansionValue, expansionTerm,
        Query.expand, Query.expandMatcher, found, completed, RetainedMatchingWire.queryTaskTerm,
        RetainedMatchingWire.queryAnswerTerm, RetainedMatchingWire.matcherAnswerTerm,
        RetainedMatchingWire.originsTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]
    | false =>
      apply matcher_branch_returns program agreement host environment request matcher codec frame free profile _ view
      unfold matcherBody
      query_eval program agreement [view, row, finished, stepped] unfolding [answerCases, answerBody, stopBody, answerData, steppedData, emptyData,
      matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
      callerFor, formals, taskValue, expansionValue, expansionTerm,
        Query.expand, Query.expandMatcher, found, completed, RetainedMatchingWire.queryTaskTerm,
        RetainedMatchingWire.queryAnswerTerm, RetainedMatchingWire.matcherAnswerTerm,
        RetainedMatchingWire.originsTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]

private def startUnavailableData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    WireKit.apply "LCons" [WireKit.apply "PremiseSignatureUnavailable" [v "relation", v "arity"], .symbol "LNil"]]]

private def startRowsData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [WireKit.apply "PremiseQueryRows" [v "signature", number 0], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]]

private def startSignatureCases : SpaceSemantics.Cases :=
  [(.symbol "None", startUnavailableData), (WireKit.apply "Some" [v "signature"], startRowsData), (v "badSignature", .symbol "None")]

private def startSignatureBody : Atom :=
  caseData (WireKit.apply "gslt:premise:signature" [v "relation", v "arity", WireKit.apply "PremiseProvider" [v "signatures", v "rows"]]) startSignatureCases

private def startBody : Atom :=
  WireKit.apply "let" [v "arity", WireKit.apply "gslt:automata:length" [v "arguments"], startSignatureBody]

private theorem start_shape : taskBody 0 = startBody := by decide +kernel

theorem start_branch_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) (answer : Atom)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (continued : PureReturns program (frameCaller codec environment request .start free profile)
      host startBody host answer) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue (environment := environment) (request := request) codec .start])
      host answer := by
  apply expand_branch_returns program agreement host environment request matcher codec .start free profile
    (frameCaller codec environment request .start free profile) startBody answer view _ continued
  simp [task_cases_syntax, start_shape, taskValue, RetainedMatchingWire.queryTaskTerm,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode]

theorem start_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue (environment := environment) (request := request) codec .start])
      host (expansionValue codec (Query.expand environment request .start)) := by
  have size := lower.length [] host (request.arguments.map InferenceCettaWire.encodePattern)
    (encoded (InferenceCettaWire.encodePatterns request.arguments)) (by
      simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
        InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map, Function.id_comp])
  simp only [List.length_map] at size
  have signatureRead := lower.signature [] host environment.provider request.relation request.arguments.length
    (encoded (.string request.relation)) (number request.arguments.length)
    (encoded (PremiseOperationsExecution.GeneralExecution.providerTerm environment.provider)) (captured_closed _)
  simp only [Query.expand]
  split
  · rename_i found
    have read := signatureRead
    simp only [found] at read
    apply start_branch_returns program agreement host environment request matcher codec free profile _ view
    unfold startBody startSignatureBody
    query_eval program agreement [size, read] unfolding [startSignatureCases, startUnavailableData, startRowsData,
      frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      expansionValue, expansionTerm, taskValue, RetainedMatchingWire.queryTaskTerm,
      RetainedMatchingWire.queryAnswerTerm, PremiseOperationsExecution.GeneralExecution.signatureTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
      PremiseOperationsExecution.GeneralExecution.queryObligationTerm,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, InferenceCettaWire.encodePatterns_eq_encodeList,
      encodeList, encodeOption, WireKit.apply, v]
  · rename_i signature found
    simp only [dif_neg unregistered]
    have read := signatureRead
    simp only [found] at read
    apply start_branch_returns program agreement host environment request matcher codec free profile _ view
    unfold startBody startSignatureBody
    query_eval program agreement [size, read] unfolding [startSignatureCases, startUnavailableData, startRowsData,
      frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      expansionValue, expansionTerm, taskValue, RetainedMatchingWire.queryTaskTerm,
      RetainedMatchingWire.queryAnswerTerm, PremiseOperationsExecution.GeneralExecution.signatureTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
      PremiseOperationsExecution.GeneralExecution.queryObligationTerm,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, InferenceCettaWire.encodePatterns_eq_encodeList,
      encodeList, encodeOption, WireKit.apply, v]

private def rowsEmptyData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def rowsTailData : Atom :=
  WireKit.apply "PremiseQueryRows" [v "signature", v "next"]

private def rowsAcceptedData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [
    WireKit.apply "LCons" [WireKit.apply "PremiseQueryArguments" [v "cursor", number 0, v "initial", v "arguments", v "values", v "modes", .symbol "LNil"],
      WireKit.apply "LCons" [rowsTailData, .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]

private def rowsRejectedData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [rowsTailData, .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def rowsCheckedBody : Atom := WireKit.apply "if" [v "checked", rowsAcceptedData, rowsRejectedData]

private def rowsConsBody : Atom :=
  WireKit.apply "let*" [.expression [.expression [v "next", WireKit.apply "+" [v "cursor", number 1]],
    .expression [v "checked", WireKit.apply "gslt:premise:check-row" [v "declarations", v "free", v "bound", v "signature",
      WireKit.apply "PremiseProviderRow" [v "rowRelation", v "values"]]]], rowsCheckedBody]

private def rowsSignatureCases : SpaceSemantics.Cases :=
  [(WireKit.apply "PremiseSignature" [v "signatureRelation", v "types", v "modes"], rowsConsBody),
    (v "badSignature", .symbol "None")]

private def rowsSignatureBody : Atom := caseData (v "signature") rowsSignatureCases

private def rowsCases : SpaceSemantics.Cases :=
  [(.symbol "None", rowsEmptyData),
    (WireKit.apply "Some" [WireKit.apply "PremiseProviderRow" [v "rowRelation", v "values"]], rowsSignatureBody),
    (v "badRow", .symbol "None")]

private def rowsBody : Atom := caseData (WireKit.apply "gslt:rule:row-at" [v "cursor", v "rows"]) rowsCases

private theorem rows_shape : taskBody 1 = rowsBody := by decide +kernel

def rowsCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request) (frame : Query.RowsFrame environment request)
    (free : List (String × TypeExpr)) (profile : Term) : Subst :=
  [("cursor", number frame.cursor), ("signature", encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm frame.signature))] ++
    frameCaller codec environment request (.rows frame) free profile

theorem rows_branch_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.RowsFrame environment request) (free : List (String × TypeExpr)) (profile : Term) (answer : Atom)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (continued : PureReturns program (rowsCaller codec environment request frame free profile) host rowsBody host answer) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.rows frame)])
      host answer := by
  apply expand_branch_returns program agreement host environment request matcher codec (.rows frame) free profile
    (rowsCaller codec environment request frame free profile) rowsBody answer view _ continued
  let values : List Atom := [encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm frame.signature), number frame.cursor]
  have taskWire : taskValue codec (.rows frame) = WireKit.apply "PremiseQueryRows" values := rfl
  rw [task_cases_syntax, taskWire]
  rw [SpaceSemantics.selectCase, Parameterized.symbol_constructor_mismatch, SpaceSemantics.selectCase]
  have matched := Parameterized.constructor_variables_match (frameCaller codec environment request (.rows frame) free profile)
    "PremiseQueryRows" ["signature", "cursor"] values (by decide) (by decide) (by rfl) (by
      intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals simp [frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals, Subst.lookup])
  have fields : SpaceSemantics.matchValue (frameCaller codec environment request (.rows frame) free profile)
      (WireKit.apply "PremiseQueryRows" [v "signature", v "cursor"]) (WireKit.apply "PremiseQueryRows" values) =
      some (rowsCaller codec environment request frame free profile) := by
    simpa [values, rowsCaller] using matched
  rw [fields, rows_shape]

theorem rows_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.RowsFrame environment request) (footprint : List String) (profile : Term)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (covers : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.rows frame)])
      host (expansionValue codec (Query.expand environment request (.rows frame))) := by
  let free := environment.free.entriesOn footprint
  have lookup := PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.row_encoded_returns
    program lower PremiseOperationsExecution.GeneralExecution.providerRowTerm [] host frame.cursor environment.provider.rows
    (number frame.cursor) (encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm environment.provider.rows))
    (captured_closed _)
  simp only [Query.expand]
  split
  · rename_i found
    have read := lookup
    simp only [found] at read
    apply rows_branch_returns program agreement host environment request matcher codec frame free profile _ view
    unfold rowsBody
    query_eval program agreement [read] unfolding [rowsCases, rowsEmptyData, rowsSignatureBody, rowsSignatureCases, rowsConsBody,
      rowsCheckedBody, rowsAcceptedData, rowsRejectedData, rowsTailData,
      rowsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      expansionValue, expansionTerm, taskValue, RetainedMatchingWire.queryTaskTerm, RetainedMatchingWire.queryAnswerTerm,
      PremiseOperationsExecution.GeneralExecution.signatureTerm, PremiseOperationsExecution.GeneralExecution.providerRowTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]
  · rename_i row found
    have read := lookup
    simp only [found] at read
    have checked := lower.rowTyped [] host environment.language free request.context.bound frame.signature row
      (encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms))
      (encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free))
      (encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.context.bound))
      (encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm frame.signature))
      (encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm row)) (captured_closed _)
    simp only [free, check_row_snapshot environment.language environment.free request.context.bound
      environment.provider frame.signature row (List.mem_of_getElem? found) footprint covers] at checked
    split
    · rename_i valid
      apply rows_branch_returns program agreement host environment request matcher codec frame free profile _ view
      unfold rowsBody
      query_eval program agreement [read, checked] unfolding [rowsCases, rowsEmptyData, rowsSignatureBody, rowsSignatureCases, rowsConsBody,
        rowsCheckedBody, rowsAcceptedData, rowsRejectedData, rowsTailData, valid, free,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        rowsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        expansionValue, expansionTerm, taskValue, RetainedMatchingWire.queryTaskTerm, RetainedMatchingWire.queryAnswerTerm,
        PremiseOperationsExecution.GeneralExecution.signatureTerm, PremiseOperationsExecution.GeneralExecution.providerRowTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]
    · rename_i invalid
      have failed : checkRow environment.language environment.free request.context.bound frame.signature row = false :=
        Bool.eq_false_iff.mpr invalid
      apply rows_branch_returns program agreement host environment request matcher codec frame free profile _ view
      unfold rowsBody
      query_eval program agreement [read, checked] unfolding [rowsCases, rowsEmptyData, rowsSignatureBody, rowsSignatureCases, rowsConsBody,
        rowsCheckedBody, rowsAcceptedData, rowsRejectedData, rowsTailData, failed, free,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        rowsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        expansionValue, expansionTerm, taskValue, RetainedMatchingWire.queryTaskTerm, RetainedMatchingWire.queryAnswerTerm,
        PremiseOperationsExecution.GeneralExecution.signatureTerm, PremiseOperationsExecution.GeneralExecution.providerRowTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, encodeList, encodeOption, WireKit.apply, v]

private def outputData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [
    WireKit.apply "PremiseQueryMatcher" [v "rowIndex", v "index", v "schemas", v "values", v "modes", v "origins", v "query", v "started", number 0],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def argumentContextData : Atom :=
  WireKit.apply "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"]

private def outputBody : Atom :=
  WireKit.apply "let*" [.expression [
    .expression [v "query", WireKit.apply "gslt:premise:query-matching-request"
      [argumentContextData, v "index", v "assignment", v "schema", v "value"]],
    .expression [v "started", WireKit.apply "gslt:premise:matching-start" [v "environment", v "query"]]], outputData]

private theorem output_shape : taskBody 4 = outputBody := by decide +kernel

def argumentsConsCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern)
    (modes : List RelationArgMode) : Subst :=
  [("origins", encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins)),
    ("modes", encoded (encodeList PremiseOperationsExecution.GeneralExecution.modeTerm modes)),
    ("values", encoded (InferenceCettaWire.encodePatterns values)),
    ("value", encoded (InferenceCettaWire.encodePattern value)),
    ("schemas", encoded (InferenceCettaWire.encodePatterns schemas)),
    ("schema", encoded (InferenceCettaWire.encodePattern schema)),
    ("assignment", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment)),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller codec environment request (.arguments frame) free profile

private def outputValue {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode) : Atom :=
  let query := Query.matchingRequest request frame.index frame.assignment schema value
  encoded (.application "Some" [.application "PremiseExpansion" [.application "LCons" [
    .application "PremiseQueryMatcher" [.natural frame.rowIndex, .natural frame.index,
      InferenceCettaWire.encodePatterns schemas, InferenceCettaWire.encodePatterns values,
      encodeList PremiseOperationsExecution.GeneralExecution.modeTerm modes,
      RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query,
      codec.stateTerm (matcher.start query), .natural 0], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]])

private theorem output_expansion (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .output :: modes) :
    expansionValue codec (Query.expand environment request (.arguments frame)) =
      outputValue codec environment request frame schema schemas value values modes := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = _ at schemasFound
  change values' = _ at valuesFound
  change modes' = _ at modesFound
  subst schemas'
  subst values'
  subst modes'
  rfl

theorem output_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .output :: modes)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (queryRead : PureReturns program [] host (WireKit.apply "gslt:premise:query-matching-request"
      [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm request.context), number frame.index,
        encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment),
        encoded (InferenceCettaWire.encodePattern schema), encoded (InferenceCettaWire.encodePattern value)])
      host (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request frame.index frame.assignment schema value))))
    (started : PureReturns program [] host (WireKit.apply "gslt:premise:matching-start"
      [encoded profile, encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request frame.index frame.assignment schema value))])
      host (encoded (codec.stateTerm (matcher.start (Query.matchingRequest request frame.index frame.assignment schema value))))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.arguments frame)])
      host (expansionValue codec (Query.expand environment request (.arguments frame))) := by
  rw [output_expansion environment request matcher codec frame schema schemas value values modes schemasFound valuesFound modesFound]
  apply expand_branch_returns program agreement host environment request matcher codec (.arguments frame) free profile
    (argumentsConsCaller codec environment request frame free profile schema schemas value values modes) outputBody _ view
  · simp [task_cases_syntax, output_shape, taskValue, RetainedMatchingWire.queryTaskTerm,
      schemasFound, valuesFound, modesFound,
      PremiseOperationsExecution.GeneralExecution.modeTerm, InferenceCettaWire.encodePatterns, encodeList,
      argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      WireKit.apply, v, Subst.lookup]
  · unfold outputBody
    query_eval program agreement [queryRead, started] unfolding [argumentContextData, outputData, outputValue,
      argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      PremiseOperationsExecution.GeneralExecution.contextTerm, WireKit.apply, v]


private def inputUnavailableData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    WireKit.apply "LCons" [WireKit.apply "PremiseInputUnavailable" [v "rowIndex", v "index"], .symbol "LNil"]]]

private def inputAcceptedData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [WireKit.apply "LCons" [
    WireKit.apply "PremiseQueryArguments" [v "rowIndex", v "next", v "assignment", v "schemas", v "values", v "modes", v "extended"],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def inputAdvanceBody : Atom :=
  WireKit.apply "let*" [.expression [
    .expression [v "next", WireKit.apply "+" [v "index", number 1]],
    .expression [v "extended", WireKit.apply "gslt:automata:append" [v "origins",
      WireKit.apply "LCons" [WireKit.apply "ArgumentOrigin" [v "index", .symbol "LNil"], .symbol "LNil"]]]], inputAcceptedData]

private def inputActualBody : Atom :=
  WireKit.apply "if" [WireKit.apply "gslt:premise:matching-input" [v "environment", v "actual", v "value"], inputAdvanceBody, emptyData]

private def inputInstantiateCases : SpaceSemantics.Cases :=
  [(.symbol "None", inputUnavailableData), (WireKit.apply "Some" [v "actual"], inputActualBody), (v "badInstantiation", .symbol "None")]

private def inputInstantiateBody : Atom :=
  caseData (WireKit.apply "gslt:rule:scope-instantiate-at" [.symbol "None", v "rule", v "spec", v "ambient", v "site",
    .symbol "LNil", number 0, v "assignment", v "schema"]) inputInstantiateCases

private def inputSiteData : Atom := WireKit.apply "RulePremise" [v "premise", v "quantifiers", v "index"]

private def inputBody : Atom :=
  WireKit.apply "let*" [.expression [
    .expression [v "ambient", WireKit.apply "gslt:automata:length" [v "bound"]],
    .expression [v "site", inputSiteData]], inputInstantiateBody]

private theorem input_shape : taskBody 3 = inputBody := by decide +kernel

private def inputAcceptedValue {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (schemas values : List Pattern) (modes : List RelationArgMode) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [.application "LCons" [
    .application "PremiseQueryArguments" [.natural frame.rowIndex, .natural (frame.index + 1),
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
      InferenceCettaWire.encodePatterns schemas, InferenceCettaWire.encodePatterns values,
      encodeList PremiseOperationsExecution.GeneralExecution.modeTerm modes,
      RetainedMatchingWire.originsTerm codec.choiceTerm (frame.origins ++ [(frame.index, [])])], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]])

private def inputValue {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode) : Atom :=
  match instantiateAt? request.context.rule request.context.spec request.context.bound.length
      (request.context.site frame.index) [] 0 frame.assignment schema with
  | none => encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
      .application "LCons" [.application "PremiseInputUnavailable" [.natural frame.rowIndex, .natural frame.index], .symbol "LNil"]]])
  | some actual =>
      if matcher.acceptsInput (Query.matchingRequest request frame.index frame.assignment schema value) actual
      then inputAcceptedValue codec environment request frame schemas values modes
      else encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]])

private theorem input_expansion (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .input :: modes) :
    expansionValue codec (Query.expand environment request (.arguments frame)) =
      inputValue codec environment request frame schema schemas value values modes := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = _ at schemasFound
  change values' = _ at valuesFound
  change modes' = _ at modesFound
  subst schemas'
  subst values'
  subst modes'
  dsimp only [Query.expand, Query.expandArguments]
  split
  · rename_i found
    simp only [inputValue, found]
    rfl
  · rename_i actual found
    simp only [inputValue, found]
    split <;> rfl

theorem input_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .input :: modes)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)))
    (compared : ∀ actual,
      instantiateAt? request.context.rule request.context.spec request.context.bound.length
        (request.context.site frame.index) [] 0 frame.assignment schema = some actual →
      PureReturns program [] host (WireKit.apply "gslt:premise:matching-input"
        [encoded profile, encoded (InferenceCettaWire.encodePattern actual), encoded (InferenceCettaWire.encodePattern value)])
        host (Effects.boolean (matcher.acceptsInput (Query.matchingRequest request frame.index frame.assignment schema value) actual))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.arguments frame)])
      host (expansionValue codec (Query.expand environment request (.arguments frame))) := by
  have size := lower.length [] host (request.context.bound.map InferenceCettaWire.AuthoredRule.typeTerm)
    (encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.context.bound)) (by
      simpa only [encodeList_map, Function.id_comp] using
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil
          (encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.context.bound)))
  simp only [List.length_map] at size
  have interpreted := lower.instantiate [] host request.context.rule request.context.spec request.context.bound.length
    (request.context.site frame.index) [] 0 frame.assignment schema
    (.symbol "None") (encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.context.rule))
    (encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.context.spec))
    (number request.context.bound.length) (encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site frame.index)))
    (.symbol "LNil") (number 0) (encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment))
    (encoded (InferenceCettaWire.encodePattern schema)) (captured_closed _)
  rw [input_expansion environment request matcher codec frame schema schemas value values modes schemasFound valuesFound modesFound]
  apply expand_branch_returns program agreement host environment request matcher codec (.arguments frame) free profile
    (argumentsConsCaller codec environment request frame free profile schema schemas value values modes) inputBody _ view
  · simp [task_cases_syntax, input_shape, taskValue, RetainedMatchingWire.queryTaskTerm,
      schemasFound, valuesFound, modesFound,
      PremiseOperationsExecution.GeneralExecution.modeTerm, InferenceCettaWire.encodePatterns, encodeList,
      argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      WireKit.apply, v, Subst.lookup]
  · unfold inputBody inputValue
    split
    · rename_i found
      have instantiated := interpreted
      simp only [found] at instantiated
      query_eval program agreement [size, instantiated] unfolding [inputSiteData, inputInstantiateBody, inputInstantiateCases,
        inputUnavailableData, inputActualBody, inputAdvanceBody, inputAcceptedData, emptyData,
        argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
        encodeList, encodeOption, WireKit.apply, v]
    · rename_i actual found
      have instantiated := interpreted
      simp only [found] at instantiated
      have comparison := compared actual found
      have appended := PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.append_encoded_returns
        program lower (fun origin : Nat × List matcher.Choice => .application "ArgumentOrigin"
          [.natural origin.1, encodeList codec.choiceTerm origin.2]) [] host frame.origins [(frame.index, [])]
        (encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins))
        (encoded (RetainedMatchingWire.originsTerm codec.choiceTerm [(frame.index, [])])) (captured_closed _)
      split
      · rename_i accepted
        query_eval program agreement [size, instantiated, comparison, appended] unfolding [inputSiteData, inputInstantiateBody, inputInstantiateCases,
          inputUnavailableData, inputActualBody, inputAdvanceBody, inputAcceptedData, inputAcceptedValue, emptyData, accepted,
          argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
          GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm, RetainedMatchingWire.originsTerm,
          encodeList, encodeOption, WireKit.apply, v]
      · rename_i rejected
        have failed : matcher.acceptsInput (Query.matchingRequest request frame.index frame.assignment schema value) actual = false :=
          Bool.eq_false_iff.mpr rejected
        query_eval program agreement [size, instantiated, comparison] unfolding [inputSiteData, inputInstantiateBody, inputInstantiateCases,
          inputUnavailableData, inputActualBody, inputAdvanceBody, inputAcceptedData, inputAcceptedValue, emptyData, failed,
          argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
          GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
          encodeList, encodeOption, WireKit.apply, v]


private def argumentsAcceptedData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil",
    WireKit.apply "LCons" [WireKit.apply "PremiseQueryAnswer" [v "rowIndex", v "assignment", v "origins"], .symbol "LNil"],
    .symbol "LNil"]]

private def argumentsDoneBody : Atom :=
  WireKit.apply "if" [WireKit.apply "gslt:premise:check-assignment"
    [v "declarations", v "free", v "bound", v "rule", v "spec", v "assignment"], argumentsAcceptedData, emptyData]

private theorem arguments_done_shape : taskBody 2 = argumentsDoneBody := by decide +kernel

def argumentsDoneCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term) : Subst :=
  [("origins", encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins)),
    ("assignment", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment)),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller codec environment request (.arguments frame) free profile

private def argumentsDoneValue {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request) (frame : Query.ArgumentsFrame environment request matcher) : Atom :=
  if checkTypedAssignment environment request.context frame.assignment then
    encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil",
      .application "LCons" [.application "PremiseQueryAnswer" [.natural frame.rowIndex,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
        RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins], .symbol "LNil"], .symbol "LNil"]])
  else encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]])

private theorem arguments_done_expansion (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = []) :
    expansionValue codec (Query.expand environment request (.arguments frame)) =
      argumentsDoneValue codec environment request frame := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = [] at schemas
  change values' = [] at values
  change modes' = [] at modes
  subst schemas'
  subst values'
  subst modes'
  dsimp only [Query.expand, Query.expandArguments]
  split <;> simp only [argumentsDoneValue, *] <;> rfl

theorem arguments_done_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = [])
    (footprint : List String) (profile : Term)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (covers : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.arguments frame)])
      host (expansionValue codec (Query.expand environment request (.arguments frame))) := by
  let free := environment.free.entriesOn footprint
  rw [arguments_done_expansion environment request matcher codec frame schemas values modes]
  apply expand_branch_returns program agreement host environment request matcher codec (.arguments frame) free profile
    (argumentsDoneCaller codec environment request frame free profile) argumentsDoneBody _ view
  · simp [task_cases_syntax, arguments_done_shape, taskValue, RetainedMatchingWire.queryTaskTerm,
      schemas, values, modes, InferenceCettaWire.encodePatterns, encodeList,
      argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      WireKit.apply, v, Subst.lookup]
  · have checked := lower.assignment [] host environment.language free request.context.bound request.context.rule
      request.context.spec frame.assignment
      (encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms))
      (encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free))
      (encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.context.bound))
      (encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.context.rule))
      (encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.context.spec))
      (encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment)) (captured_closed _)
    simp only [free, ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
      request.context.bound request.context.rule request.context.spec frame.assignment footprint covers] at checked
    unfold argumentsDoneBody argumentsDoneValue
    split
    · rename_i valid
      change ConditionalEquationExecution.checkAssignment environment.language environment.free request.context.bound
        request.context.rule request.context.spec frame.assignment = true at valid
      query_eval program agreement [checked] unfolding [valid, argumentsAcceptedData, emptyData, free,
        argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        GeneralPremise.checkTypedAssignment,
        encodeList, WireKit.apply, v]
    · rename_i invalid
      have failed : checkTypedAssignment environment request.context frame.assignment = false := Bool.eq_false_iff.mpr invalid
      change ConditionalEquationExecution.checkAssignment environment.language environment.free request.context.bound
        request.context.rule request.context.spec frame.assignment = false at failed
      query_eval program agreement [checked] unfolding [failed, argumentsAcceptedData, emptyData, free,
        argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        GeneralPremise.checkTypedAssignment,
        encodeList, WireKit.apply, v]


private def argumentShapeData : Atom :=
  WireKit.apply "Some" [WireKit.apply "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    WireKit.apply "LCons" [WireKit.apply "PremiseArgumentShape" [v "rowIndex", v "index"], .symbol "LNil"]]]

private theorem argument_shape_body : taskBody 5 = argumentShapeData := by decide +kernel

private def argumentShapeCaller {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term) : Subst :=
  [("origins", encoded (RetainedMatchingWire.originsTerm codec.choiceTerm frame.origins)),
    ("modes", encoded (encodeList PremiseOperationsExecution.GeneralExecution.modeTerm frame.modes)),
    ("values", encoded (InferenceCettaWire.encodePatterns frame.values)),
    ("schemas", encoded (InferenceCettaWire.encodePatterns frame.schemas)),
    ("assignment", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment)),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller codec environment request (.arguments frame) free profile

theorem arguments_shape_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (free : List (String × TypeExpr)) (profile : Term)
    (shape : ¬ (frame.schemas.isEmpty = frame.values.isEmpty ∧ frame.values.isEmpty = frame.modes.isEmpty))
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.arguments frame)])
      host (expansionValue codec (Query.expand environment request (.arguments frame))) := by
  have original : expansionValue codec (Query.expand environment request (.arguments frame)) =
      encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
        .application "LCons" [.application "PremiseArgumentShape" [.natural frame.rowIndex, .natural frame.index], .symbol "LNil"]]]) := by
    simp only [Query.expand, Query.expandArguments]
    split
    · rename_i schemasFound valuesFound modesFound
      exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
      exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    · rfl
  rw [original]
  apply expand_branch_returns program agreement host environment request matcher codec (.arguments frame) free profile
    (argumentShapeCaller codec environment request frame free profile) argumentShapeData _ view
  · cases schemasFound : frame.schemas <;> cases valuesFound : frame.values <;> cases modesFound : frame.modes
    case nil.nil.nil => exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    case cons.cons.cons => exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    case nil.nil.cons mode modes =>
      cases mode <;>
        simp [task_cases_syntax, argument_shape_body, taskValue, RetainedMatchingWire.queryTaskTerm,
          schemasFound, valuesFound, modesFound, InferenceCettaWire.encodePatterns, encodeList,
          PremiseOperationsExecution.GeneralExecution.modeTerm, argumentShapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          WireKit.apply, v, Subst.lookup]
    case nil.cons.cons value values mode modes =>
      cases mode <;>
        simp [task_cases_syntax, argument_shape_body, taskValue, RetainedMatchingWire.queryTaskTerm,
          schemasFound, valuesFound, modesFound, InferenceCettaWire.encodePatterns, encodeList,
          PremiseOperationsExecution.GeneralExecution.modeTerm, argumentShapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          WireKit.apply, v, Subst.lookup]
    case cons.nil.cons schema schemas mode modes =>
      cases mode <;>
        simp [task_cases_syntax, argument_shape_body, taskValue, RetainedMatchingWire.queryTaskTerm,
          schemasFound, valuesFound, modesFound, InferenceCettaWire.encodePatterns, encodeList,
          PremiseOperationsExecution.GeneralExecution.modeTerm, argumentShapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          WireKit.apply, v, Subst.lookup]
    all_goals
      simp [task_cases_syntax, argument_shape_body, taskValue, RetainedMatchingWire.queryTaskTerm,
        schemasFound, valuesFound, modesFound, InferenceCettaWire.encodePatterns, encodeList,
        argumentShapeCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callerFor, formals,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        WireKit.apply, v, Subst.lookup]
  · query_eval program agreement unfolding [argumentShapeData, argumentShapeCaller, frameCaller, requestCaller,
      contextCaller, environmentCaller, callerFor, formals, WireKit.apply, v]

theorem arguments_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Query.ArgumentsFrame environment request matcher) (footprint : List String) (profile : Term)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations program matcher codec profile requestReady stateReady valueReady)
    (captures : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (supported : ∀ schema schemas value values mode modes,
      frame.schemas = schema :: schemas → frame.values = value :: values → frame.modes = mode :: modes →
      requestReady (Query.matchingRequest request frame.index frame.assignment schema value) ∧
        (mode = .input → ∀ actual, instantiateAt? request.context.rule request.context.spec request.context.bound.length
          (request.context.site frame.index) [] 0 frame.assignment schema = some actual → valueReady actual))
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))))
    (queryRead : ∀ index assignment schema value,
      PureReturns program [] host (WireKit.apply "gslt:premise:query-matching-request"
        [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm request.context), number index,
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment),
          encoded (InferenceCettaWire.encodePattern schema), encoded (InferenceCettaWire.encodePattern value)])
        host (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
          (Query.matchingRequest request index assignment schema value)))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec (.arguments frame)])
      host (expansionValue codec (Query.expand environment request (.arguments frame))) := by
  cases schemasFound : frame.schemas <;> cases valuesFound : frame.values <;> cases modesFound : frame.modes
  case nil.nil.nil =>
    exact arguments_done_returns program agreement host environment request matcher codec frame schemasFound valuesFound modesFound
      footprint profile lower captures view
  case cons.cons.cons schema schemas value values mode modes =>
    have ready := supported schema schemas value values mode modes schemasFound valuesFound modesFound
    cases mode with
    | input =>
      exact input_returns program agreement host environment request matcher codec frame (environment.free.entriesOn footprint) profile
        schema schemas value values modes schemasFound valuesFound modesFound lower view
        (fun actual instantiated => operations.input host _ actual ready.1 (ready.2 rfl actual instantiated))
    | output =>
      exact output_returns program agreement host environment request matcher codec frame (environment.free.entriesOn footprint) profile
        schema schemas value values modes schemasFound valuesFound modesFound view
        (queryRead frame.index frame.assignment schema value) (operations.start host _ ready.1)
  all_goals
    exact arguments_shape_returns program agreement host environment request matcher codec frame
      (environment.free.entriesOn footprint) profile (by simp [schemasFound, valuesFound, modesFound]) view

theorem expand_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (host : Effects.State) (environment : Environment) (request : Query.Request)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (task : Query.Task environment request matcher) (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String) (profile : Term)
    (lower : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations program matcher codec profile requestReady stateReady valueReady)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request matcher, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (arguments : ∀ frame : Query.ArgumentsFrame environment request matcher, task = .arguments frame →
      ∀ schema schemas value values mode modes,
      frame.schemas = schema :: schemas → frame.values = value :: values → frame.modes = mode :: modes →
      requestReady (Query.matchingRequest request frame.index frame.assignment schema value) ∧
        (mode = .input → ∀ actual, instantiateAt? request.context.rule request.context.spec request.context.bound.length
          (request.context.site frame.index) [] 0 frame.assignment schema = some actual → valueReady actual))
    (matching : ∀ frame : Query.MatcherFrame environment request matcher, task = .matcher frame → stateReady frame.state)
    (view : PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment" [encoded profile])
      host (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))))
    (queryRead : ∀ index assignment schema value,
      PureReturns program [] host (WireKit.apply "gslt:premise:query-matching-request"
        [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm request.context), number index,
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment),
          encoded (InferenceCettaWire.encodePattern schema), encoded (InferenceCettaWire.encodePattern value)])
        host (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
          (Query.matchingRequest request index assignment schema value)))) :
    PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" [encoded profile,
      encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request), taskValue codec task])
      host (expansionValue codec (Query.expand environment request task)) := by
  cases task with
  | start =>
      exact start_returns program agreement host environment request matcher codec (environment.free.entriesOn footprint) profile
        lower unregistered view
  | rows frame => exact rows_returns program agreement host environment request matcher codec frame footprint profile lower provider view
  | arguments frame =>
      exact arguments_returns program agreement host environment request matcher codec frame footprint profile lower
        requestReady stateReady valueReady operations (captures frame rfl) (arguments frame rfl) view queryRead
  | matcher frame =>
      apply matcher_returns program agreement host environment request matcher codec frame (environment.free.entriesOn footprint) profile
        view (operations.answer host frame.state frame.cursor) (operations.complete host frame.state)
        (operations.tick host frame.query frame.state (matching frame rfl))
      intro left right
      exact PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.append_encoded_returns
        program lower (fun origin : Nat × List matcher.Choice => .application "ArgumentOrigin"
          [.natural origin.1, encodeList codec.choiceTerm origin.2]) [] host left right
        (encoded (RetainedMatchingWire.originsTerm codec.choiceTerm left))
        (encoded (RetainedMatchingWire.originsTerm codec.choiceTerm right)) (captured_closed _)
  | dynamicInputs frame => exact False.elim (unregistered frame.registered)
  | dynamicRows frame => exact False.elim (unregistered frame.registered)

theorem capture_return (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program) (caller : Subst) (host : Effects.State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = 3) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] host (WireKit.apply "gslt:premise:query-expand-in" values) host answer) :
    PureReturns program caller host (WireKit.apply "gslt:premise:query-expand-in" arguments) host answer :=
  Parameterized.helper_capture program agreement .expand caller host arguments values answer length captured returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expand_branch_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.matcher_branch_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.matcher_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.start_branch_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.rows_branch_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.rows_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.output_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.input_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.arguments_done_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.arguments_shape_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.arguments_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expand_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.capture_return
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.template_in_program
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.data_in_program_returns

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval BridgeKit WireKit

private def matchingCases (helper : Helper) : SpaceSemantics.Cases := sourceCases (queryEquation helper).body

private theorem matching_shape (helper : Helper)
    (matching : helper = .matchingEnvironment ∨ helper = .matchingStart ∨ helper = .matchingTick ∨
      helper = .matchingComplete ∨ helper = .matchingAnswer ∨ helper = .matchingInput) :
    (queryEquation helper).body = caseData (v "environment") (matchingCases helper) := by
  rcases matching with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem ordinary_environment_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr)) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-environment"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)) := by
  apply Parameterized.helper_call program agreement .matchingEnvironment [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingEnvironment (by simp)]
  query_eval program agreement unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm]

theorem ordinary_start_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (lower : Parameterized.LowerOperations program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr))
    (query : GeneralScopedMatchMachine.Request) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-start"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query)]) host
      (encoded (RetainedMatchingWire.ordinaryCodec.stateTerm (MatchingExecution.ordinary.start query))) := by
  have started := lower.start [] host query
    (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query)) (by simp)
  apply Parameterized.helper_call program agreement .matchingStart [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingStart (by simp)]
  query_eval program agreement [started] unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm, RetainedMatchingWire.ordinaryCodec]

theorem ordinary_tick_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (lower : Parameterized.LowerOperations program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr))
    (query : GeneralScopedMatchMachine.Request) (machine : MatchingExecution.ordinary.State) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-tick"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query),
        encoded (RetainedMatchingWire.ordinaryCodec.stateTerm machine)]) host
      (encoded (RetainedMatchingWire.ordinaryCodec.stateTerm (MatchingExecution.ordinary.tick query machine))) := by
  have stepped := lower.tick [] host query machine
    (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm query))
    (encoded (RetainedMatchingWire.ordinaryCodec.stateTerm machine)) (captured_closed _)
  apply Parameterized.helper_call program agreement .matchingTick [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingTick (by simp)]
  query_eval program agreement [stepped] unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm, RetainedMatchingWire.ordinaryCodec]

theorem ordinary_complete_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (lower : Parameterized.LowerOperations program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr))
    (machine : MatchingExecution.ordinary.State) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-complete"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free),
        encoded (RetainedMatchingWire.ordinaryCodec.stateTerm machine)]) host
      (Effects.boolean (MatchingExecution.ordinary.complete machine)) := by
  have complete := lower.complete [] host machine
    (encoded (RetainedMatchingWire.ordinaryCodec.stateTerm machine)) (by simp [RetainedMatchingWire.ordinaryCodec])
  apply Parameterized.helper_call program agreement .matchingComplete [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingComplete (by simp)]
  query_eval program agreement [complete] unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm, RetainedMatchingWire.ordinaryCodec]

theorem ordinary_matcher_answer_terms :
    (RetainedMatchingWire.matcherAnswerTerm RetainedMatchingWire.ordinaryCodec : GeneralScopedMatchMachine.Answer → Term) =
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm :=
  funext RetainedMatchingWire.ordinary_matcherAnswer

theorem ordinary_answer_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (lower : Parameterized.LowerOperations program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr))
    (machine : MatchingExecution.ordinary.State) (cursor : Nat) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-answer-at"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free),
        encoded (RetainedMatchingWire.ordinaryCodec.stateTerm machine), number cursor]) host
      (encoded (encodeOption (RetainedMatchingWire.matcherAnswerTerm RetainedMatchingWire.ordinaryCodec)
        (MatchingExecution.ordinary.answers machine)[cursor]?)) := by
  rw [ordinary_matcher_answer_terms]
  have row := Parameterized.row_encoded_returns program lower
    RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm [] host cursor machine.answers
    (number cursor) (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
      machine.answers)) (captured_closed _)
  apply Parameterized.helper_call program agreement .matchingAnswer [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingAnswer (by simp)]
  query_eval program agreement [row] unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm, RetainedMatchingWire.ordinaryCodec,
    RuleInstantiationExecution.GeneralExecution.matcherStateTerm, RetainedMatchingWire.ordinary_matcherAnswer]

theorem ordinary_input_returns (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (host : Effects.State) (environment : Environment) (free : List (String × TypeExpr))
    (query : GeneralScopedMatchMachine.Request) (actual : Pattern) :
    PureReturns program [] host (WireKit.apply "gslt:premise:matching-input"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free),
        encoded (InferenceCettaWire.encodePattern actual), encoded (InferenceCettaWire.encodePattern query.target)]) host
      (Effects.boolean (MatchingExecution.ordinary.acceptsInput query actual)) := by
  change PureReturns program [] host _ host (Effects.boolean (actual == query.target))
  have same : (actual == query.target) =
      decide (InferenceCettaWire.encodePattern actual = InferenceCettaWire.encodePattern query.target) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, InferenceCettaWire.encodePattern_injective.eq_iff]
  rw [same]
  apply Parameterized.helper_call program agreement .matchingInput [] host _ _ _ rfl (captured_closed _)
  rw [matching_shape .matchingInput (by simp)]
  query_eval program agreement unfolding [matchingCases, queryEquation, callee, Helper.names,
    PremiseOperationsExecution.GeneralExecution.environmentTerm]

theorem ordinary_operations (program : Program)
    (agreement : ProgramAgreementOn Parameterized.ownedHeads runtime program)
    (lower : Parameterized.LowerOperations program) (environment : Environment) (free : List (String × TypeExpr)) :
    RetainedMatchingWire.MatchingOperations program MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)
      (fun _ => True) (fun _ => True) (fun _ => True) where
  start := fun host query _ => ordinary_start_returns program agreement lower host environment free query
  tick := fun host query machine _ => ordinary_tick_returns program agreement lower host environment free query machine
  complete := fun host machine => ordinary_complete_returns program agreement lower host environment free machine
  answer := fun host machine cursor => ordinary_answer_returns program agreement lower host environment free machine cursor
  input := fun host query actual _ _ => ordinary_input_returns program agreement host environment free query actual

theorem ordinary_expansionTerm {environment : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task environment request) (Query.Answer environment request) Query.Obligation) :
    expansionTerm RetainedMatchingWire.ordinaryCodec expansion = queryExpansionTerm expansion := by
  have tasks : (RetainedMatchingWire.queryTaskTerm RetainedMatchingWire.ordinaryCodec : Query.Task environment request → Term) =
      PremiseOperationsExecution.GeneralExecution.queryTaskTerm := funext RetainedMatchingWire.ordinary_query_task
  have answers : (RetainedMatchingWire.queryAnswerTerm RetainedMatchingWire.ordinaryCodec : Query.Answer environment request → Term) =
      queryAnswerTerm := funext RetainedMatchingWire.ordinary_query_answer
  unfold expansionTerm queryExpansionTerm
  rw [tasks, answers]

theorem ordinary_expansion_terms {environment : Environment} {request : Query.Request} :
    (expansionTerm RetainedMatchingWire.ordinaryCodec :
      Scheduler.Expansion (Query.Task environment request) (Query.Answer environment request) Query.Obligation → Term) =
        queryExpansionTerm :=
  funext ordinary_expansionTerm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem query_expand_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) := by
  have returned := Interpreted.expand_returns program agreement state environment request MatchingExecution.ordinary
    RetainedMatchingWire.ordinaryCodec task unregistered footprint
    (environmentTerm environment (environment.free.entriesOn footprint)) lower
    (fun _ => True) (fun _ => True) (fun _ => True)
    (Interpreted.ordinary_operations program agreement lower environment (environment.free.entriesOn footprint))
    provider captures (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩)
    (fun _ _ => trivial)
    (Interpreted.ordinary_environment_returns program agreement state environment (environment.free.entriesOn footprint))
    (fun index assignment schema value => query_matching_request_returns program agreement lower state request index assignment schema value)
  simpa only [Interpreted.taskValue, RetainedMatchingWire.ordinary_query_task,
    Interpreted.expansionValue, Interpreted.ordinary_expansion_terms] using returned

theorem query_expand_captured_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (caller : Subst) (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) :
    PureReturns program caller state (a "gslt:premise:query-expand-in" [one, two, three]) state
      (expansionValue (Query.expand environment request task)) :=
  helper_capture program agreement .expand caller state _ _ _ rfl captured
    (query_expand_returns program agreement lower state environment request task unregistered footprint provider captures)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_environment_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_tick_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_matcher_answer_terms
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_answer_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_input_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_operations
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_expansionTerm
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_expansion_terms
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.query_expand_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.query_expand_captured_returns

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace Trajectory

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

theorem query_expand_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Query.taskFreeWithin footprint task) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) := by
  apply query_expand_returns program agreement lower state environment request task unregistered footprint provider
  intro frame same
  subst task
  exact Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_free_names_covered _ _ covered.1

theorem query_expand_prefix_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (fuel : Nat) (task : Query.Task environment request)
    (member : task ∈ (Query.run environment request fuel (Query.start environment request)).agenda) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn
        (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)),
        queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) :=
  query_expand_within_returns program agreement lower state environment request task
    (by simp only [finiteProvider, List.not_mem_nil, not_false_eq_true]) _
    (fun _ occurs => List.mem_append_right _ occurs)
    ((Query.run_finite_free_within Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinary_preservesFreeNames environment request
      (Query.DynamicOutputsFreeWithin.of_unregistered _ _ finiteProvider) fuel).1 _ member)


end Trajectory

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval
open QueryExecution (a v encoded number stringValue boundValue patternValue ruleValue assignmentValue)

private def operationArities : List (String × Nat) :=
  [("gslt:premise:signature", 3), ("gslt:premise:check-row", 5), ("gslt:rule:scope-instantiate-at", 9), ("gslt:premise:check-assignment", 6)]

private theorem raw_at (head : String) (arity index : Nat)
    (member : (head, arity) ∈ operationArities) (bound : index < arity) :
    argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true := by
  have checked : operationArities.all (fun operation =>
      (List.range operation.2).all (argumentIsRaw RuleExecutionProgram.scopedMachineProgram operation.1)) = true := by rfl
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (head, arity) member) index (List.mem_range.mpr bound)

private theorem raw_arguments (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) (arguments : List Atom) (length : arguments.length = arity) :
    ∀ index argument, arguments[index]? = some argument →
      argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true ∨ passiveArgument argument = true := by
  intro index argument picked
  exact Or.inl (raw_at head arity index member (by
    have bound := (List.getElem?_eq_some_iff.mp picked).1
    simpa only [length] using bound))

private theorem ordinary_dispatch (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) :
    (ioHead head || StdLib.known head || RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == head)) = true := by
  have checked : operationArities.all (fun operation =>
      ioHead operation.1 || StdLib.known operation.1 ||
        RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == operation.1)) = true := by rfl
  exact List.all_eq_true.mp checked (head, arity) member

private theorem pattern_option_representation (result : Option Pattern) :
    encoded (MatchAutomataBindingExecution.patternOptionTerm result) =
      encoded (encodeOption InferenceCettaWire.encodePattern result) := by
  cases result <;> rfl

theorem signature_returns (caller : Subst) (state : State) (provider : ProviderSnapshot) (relation : String) (arity : Nat)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [stringValue relation, number arity, encoded (providerTerm provider)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:signature" [one, two, three]) state (encoded (encodeOption signatureTerm (signature? provider relation arity))) := by
  let capturedCaller : Subst := [("one", stringValue relation), ("two", number arity), ("three", encoded (providerTerm provider))]
  have capturedNames : [v "one", v "two", v "three"].map (applySubst capturedCaller) = [stringValue relation, number arity, encoded (providerTerm provider)] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := signature_captured_returns capturedCaller state provider relation arity (v "one") (v "two") (v "three") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:premise:signature"
    [v "one", v "two", v "three"] [one, two, three] _
    (ordinary_dispatch _ 3 (by simp [operationArities])) (by decide)
    (raw_arguments _ 3 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 3 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem row_typed_returns (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (signature : Signature) (row : ProviderRow)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) = [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:check-row" [one, two, three, four, five]) state (Effects.boolean (checkRow language (FreeTypeContext.ofList free) bound signature row)) := by
  let capturedCaller : Subst := [("one", encoded (DeclarationTyping.declarationsTerm language.terms)), ("two", encoded (DeclarationTyping.freeContextTerm free)), ("three", boundValue bound), ("four", encoded (signatureTerm signature)), ("five", encoded (providerRowTerm row))]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five"].map (applySubst capturedCaller) = [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := check_row_captured_returns capturedCaller state language free bound signature row (v "one") (v "two") (v "three") (v "four") (v "five") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:premise:check-row"
    [v "one", v "two", v "three", v "four", v "five"] [one, two, three, four, five] _
    (ordinary_dispatch _ 5 (by simp [operationArities])) (by decide)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem instantiate_returns (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern)
    (one two three four five six seven eight nine : Atom)
    (captured : [one, two, three, four, five, six, seven, eight, nine].map (applySubst caller) = [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path), number depth, assignmentValue assignment, patternValue pattern]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-instantiate-at" [one, two, three, four, five, six, seven, eight, nine]) state (encoded (encodeOption InferenceCettaWire.encodePattern (instantiateAt? rule spec ambient site path depth assignment pattern))) := by
  let capturedCaller : Subst := [("one", .symbol "None"), ("two", ruleValue rule), ("three", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)), ("four", number ambient), ("five", encoded (InferenceCettaWire.AuthoredRule.siteTerm site)), ("six", encoded (encodeList Term.natural path)), ("seven", number depth), ("eight", assignmentValue assignment), ("nine", patternValue pattern)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"].map (applySubst capturedCaller) = [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path), number depth, assignmentValue assignment, patternValue pattern] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := ScopedInstantiationExecution.instantiate_ordinary_captured_returns capturedCaller state
    rule spec ambient site path depth assignment pattern [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"]
    (by simpa only [ScopedInstantiationExecution.instantiationValues] using capturedNames)
  have actual := path_of_closed_agreement ScopedInstantiationExecution.runtime_closed ScopedInstantiationExecution.scoped_machine_agreement
    ⟨by change codeWithin ScopedInstantiationExecution.executionHeads (a "gslt:rule:scope-instantiate-at" [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"]) = true
        decide +kernel, rfl⟩ source
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:rule:scope-instantiate-at"
    [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"] [one, two, three, four, five, six, seven, eight, nine] _
    (ordinary_dispatch _ 9 (by simp [operationArities])) (by decide)
    (raw_arguments _ 9 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 9 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) (by simpa only [pattern_option_representation] using actual)

theorem assignment_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (assignment : Assignment) (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, ruleValue rule,
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (FreeTypeContext.ofList free) bound rule spec assignment)) := by
  let capturedCaller : Subst :=
    [("one", encoded (DeclarationTyping.declarationsTerm language.terms)), ("two", encoded (DeclarationTyping.freeContextTerm free)), ("three", boundValue bound),
      ("four", ruleValue rule), ("five", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)), ("six", assignmentValue assignment)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five", v "six"].map
      (applySubst capturedCaller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, ruleValue rule,
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := check_assignment_captured_returns capturedCaller state language free bound rule spec
    assignment (v "one") (v "two") (v "three") (v "four") (v "five") (v "six") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state
    "gslt:premise:check-assignment" [v "one", v "two", v "three", v "four", v "five", v "six"]
    [one, two, three, four, five, six] _
    (ordinary_dispatch _ 6 (by simp [operationArities])) (by decide)
    (raw_arguments _ 6 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 6 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual


theorem operations : QueryExecution.Parameterized.LowerOperations RuleExecutionProgram.scopedMachineProgram where
  row := RuleInstantiationExecution.GeneralExecution.Mechanical.row_returns
  length := RuleInstantiationExecution.GeneralExecution.Mechanical.length_returns
  append := RuleInstantiationExecution.GeneralExecution.Mechanical.append_returns
  signature := signature_returns
  rowTyped := row_typed_returns
  assignment := assignment_returns
  start := RuleInstantiationExecution.GeneralExecution.Mechanical.start_returns
  tick := RuleInstantiationExecution.GeneralExecution.Mechanical.tick_returns
  complete := RuleInstantiationExecution.GeneralExecution.Mechanical.complete_returns
  instantiate := instantiate_returns


open SpaceSemantics (Program Equation)
open BridgeKit

theorem move_raw (program : Program)
    (agreement : ProgramAgreementOn RetainedMatchingWire.scopedPrimitiveHeads RuleExecutionProgram.scopedMachineProgram program) (head : String) (names : List String)
    (kept : RetainedMatchingWire.scopedPrimitiveHeads head = true) (notEval : head ≠ "eval")
    (dispatch : (ioHead head || StdLib.known head || RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == head)) = true)
    (ordinary : head ∉ specialForms) (distinct : names.Nodup)
    (raw : ∀ index < names.length, argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true)
    (caller : Subst) (host : Effects.State) (arguments : List Atom) (answer : Atom)
    (count : arguments.length = names.length)
    (fact : PureReturns RuleExecutionProgram.scopedMachineProgram caller host (WireKit.apply head arguments) host answer) :
    PureReturns program caller host (WireKit.apply head arguments) host answer := by
  let values := arguments.map (applySubst caller)
  have rawArguments : ∀ index < arguments.length, argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true := by
    simpa only [count] using raw
  have special : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
    simpa only [specialForms] using ordinary
  have atValues : PureReturns RuleExecutionProgram.scopedMachineProgram [] host (WireKit.apply head values) host answer :=
    PureData.raw_capture_returns RuleExecutionProgram.scopedMachineProgram caller [] host host head arguments values answer dispatch
      rawArguments special (QueryExecution.captured_closed values).symm fact
  have length : values.length = names.length := by simpa only [values, List.length_map] using count
  have moved := BridgeKit.transport_call RetainedMatchingWire.scopedPrimitive_closed agreement kept notEval dispatch ordinary
    names distinct length raw atValues
  apply PureData.raw_capture_returns program [] caller host host head values arguments answer
    _ _ special (QueryExecution.captured_closed values) moved
  · rw [← agreement.dispatch head kept]
    exact dispatch
  · intro index bounded
    rw [← agreement.demand head index kept]
    exact raw index (by simpa only [length] using bounded)

syntax "lower_transport% " term:max term:max " [" str,* "] " term:max : term
macro_rules
  | `(lower_transport% $program $agreement [$names,*] $fact) =>
      `(move_raw $program $agreement _ [$names,*] (by decide +kernel) (by decide) (by decide +kernel)
        (by decide) (by decide) (by decide +kernel) _ _ _ _ (by rfl) $fact)

theorem operations_in (program : Program)
    (agreement : ProgramAgreementOn RetainedMatchingWire.scopedPrimitiveHeads RuleExecutionProgram.scopedMachineProgram program) : PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.LowerOperations program where
  row := by
    intro caller host index values one two captured
    exact lower_transport% program agreement ["index", "rows"]
      (operations.row caller host index values one two captured)
  length := by
    intro caller host values input captured
    exact lower_transport% program agreement ["values"] (operations.length caller host values input captured)
  append := by
    intro caller host left right one two captured
    exact lower_transport% program agreement ["left", "right"] (operations.append caller host left right one two captured)
  signature := by
    intro caller host provider relation arity one two three captured
    exact lower_transport% program agreement ["relation", "arity", "provider"]
      (operations.signature caller host provider relation arity one two three captured)
  rowTyped := by
    intro caller host language free bound signature row one two three four five captured
    exact lower_transport% program agreement ["declarations", "free", "bound", "signature", "row"]
      (operations.rowTyped caller host language free bound signature row one two three four five captured)
  assignment := by
    intro caller host language free bound rule spec assignment one two three four five six captured
    exact lower_transport% program agreement ["declarations", "free", "bound", "rule", "spec", "assignment"]
      (operations.assignment caller host language free bound rule spec assignment one two three four five six captured)
  start := by
    intro caller host request input captured
    exact lower_transport% program agreement ["request"] (operations.start caller host request input captured)
  tick := by
    intro caller host request machine one two captured
    exact lower_transport% program agreement ["request", "state"] (operations.tick caller host request machine one two captured)
  complete := by
    intro caller host machine input captured
    exact lower_transport% program agreement ["state"] (operations.complete caller host machine input captured)
  instantiate := by
    intro caller host rule spec ambient site path depth assignment pattern one two three four five six seven eight nine captured
    exact lower_transport% program agreement ["override", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "pattern"]
      (operations.instantiate caller host rule spec ambient site path depth assignment pattern
        one two three four five six seven eight nine captured)

theorem interpreted_operations : QueryExecution.Parameterized.LowerOperations RuleExecutionProgram.interpretedPremiseProgram :=
  operations_in RuleExecutionProgram.interpretedPremiseProgram RetainedMatchingWire.scopedPrimitive_agreement


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower.move_raw
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower.operations_in
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower.interpreted_operations
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open SpaceSemantics (Program)
open Eval

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private local instance interpretedEquationEq : DecidableEq SpaceSemantics.Equation := by
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

private theorem grouped_agreement (program : Program)
    (equations : ∀ group ∈ sourceHeadGroups,
      runtime.equations.filter (fun row => group.contains row.head) =
        program.equations.filter (fun row => group.contains row.head))
    (declarations : ∀ group ∈ sourceHeadGroups,
      runtime.declarations.filter (retainedCallDeclaration group.contains) =
        program.declarations.filter (retainedCallDeclaration group.contains)) :
    ProgramAgreementOn ownedHeads runtime program := by
  have locate (head : String) (supported : ownedHeads head = true) :
      ∃ group, group ∈ sourceHeadGroups ∧ group.contains head = true := by
    have member : head ∈ sourceHeadGroups.flatten := List.contains_iff_mem.mp supported
    obtain ⟨group, present, found⟩ := List.mem_flatten.mp member
    exact ⟨group, present, List.contains_iff_mem.mpr found⟩
  have agreed (group : List String) (present : group ∈ sourceHeadGroups) :
      ProgramAgreementOn group.contains runtime program :=
    programAgreementOn_of_retained_rows _ _ _ (equations group present) (declarations group present)
  constructor
  · intro head supported
    obtain ⟨group, present, found⟩ := locate head supported
    exact (agreed group present).dispatch head found
  · intro head index supported
    obtain ⟨group, present, found⟩ := locate head supported
    exact (agreed group present).demand head index found
  · intro head values supported
    obtain ⟨group, present, found⟩ := locate head supported
    exact (agreed group present).bodies head values found

private theorem interpreted_group_equations (group : List String)
    (present : group ∈ sourceHeadGroups) :
    runtime.equations.filter (fun row => group.contains row.head) =
      RuleExecutionProgram.interpretedPremiseProgram.equations.filter (fun row => group.contains row.head) := by
  simp only [sourceHeadGroups, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem interpreted_group_declarations (group : List String)
    (present : group ∈ sourceHeadGroups) :
    runtime.declarations.filter (retainedCallDeclaration group.contains) =
      RuleExecutionProgram.interpretedPremiseProgram.declarations.filter (retainedCallDeclaration group.contains) := by
  simp only [sourceHeadGroups, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem interpreted_agreement :
    ProgramAgreementOn ownedHeads runtime RuleExecutionProgram.interpretedPremiseProgram :=
  grouped_agreement RuleExecutionProgram.interpretedPremiseProgram interpreted_group_equations interpreted_group_declarations

private theorem scoped_group_equations (group : List String)
    (present : group ∈ sourceHeadGroups) :
    runtime.equations.filter (fun row => group.contains row.head) =
      RuleExecutionProgram.scopedMachineProgram.equations.filter (fun row => group.contains row.head) := by
  simp only [sourceHeadGroups, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem scoped_group_declarations (group : List String)
    (present : group ∈ sourceHeadGroups) :
    runtime.declarations.filter (retainedCallDeclaration group.contains) =
      RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration group.contains) := by
  simp only [sourceHeadGroups, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem scoped_agreement :
    ProgramAgreementOn ownedHeads runtime RuleExecutionProgram.scopedMachineProgram :=
  grouped_agreement RuleExecutionProgram.scopedMachineProgram scoped_group_equations scoped_group_declarations


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.ControlAssembly

open Eval

theorem query_agreement :
    ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime RuleExecutionProgram.scopedMachineProgram :=
  QueryExecution.Parameterized.scoped_agreement

theorem scheduler_retained_equations :
    PremiseSchedulerExecution.runtime.equations.filter (fun equation => PremiseSchedulerExecution.executionHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => PremiseSchedulerExecution.executionHeads equation.head) := by rfl

theorem scheduler_retained_declarations :
    PremiseSchedulerExecution.runtime.declarations.filter (retainedCallDeclaration PremiseSchedulerExecution.executionHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration PremiseSchedulerExecution.executionHeads) := by rfl

theorem scheduler_agreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ scheduler_retained_equations scheduler_retained_declarations


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.ControlAssembly


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def queryRequestCases : SpaceSemantics.Cases := sourceCases (taskBody 2)
def queryRequestBody : Atom := (queryRequestCases.head!).2
def queryContextCases : SpaceSemantics.Cases := sourceCases queryRequestBody
def queryContextBody : Atom := (queryContextCases.head!).2
def queryStateCases : SpaceSemantics.Cases := sourceCases queryContextBody
def queryStateBody : Atom := (queryStateCases.head!).2
def queryAnswerCases : SpaceSemantics.Cases := sourceCases queryStateBody
def queryAnswerBody : Atom := (queryAnswerCases.head!).2
def queryAgendaCases : SpaceSemantics.Cases := sourceCases ((queryAnswerCases[1]!).2)
def queryEmptyBody : Atom := (queryAgendaCases.head!).2
def queryProgressBody : Atom := ((queryAgendaCases[1]!).2)

theorem query_task_shape : taskBody 2 = caseData (v "request") queryRequestCases := by decide +kernel
theorem query_request_shape : queryRequestBody = caseData (v "context") queryContextCases := by decide +kernel
theorem query_context_shape : queryContextBody = caseData (v "queryState") queryStateCases := by decide +kernel
theorem query_state_shape : queryStateBody =
    caseData (a "gslt:rule:row-at" [v "cursor", v "answers"]) queryAnswerCases := by decide +kernel
theorem query_none_shape : (queryAnswerCases[1]!).2 = caseData (v "agenda") queryAgendaCases := by decide +kernel

theorem query_request_cases_syntax : queryRequestCases =
    [(a "PremiseQueryRequest" [v "context", v "relation", v "arguments", v "initial"], queryRequestBody),
      (v "badRequest", .symbol "None")] := by decide +kernel
theorem query_context_cases_syntax : queryContextCases =
    [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premiseIndex", v "quantifiers"], queryContextBody),
      (v "badContext", .symbol "None")] := by decide +kernel
theorem query_state_cases_syntax : queryStateCases =
    [(a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"], queryStateBody),
      (v "badState", .symbol "None")] := by decide +kernel
theorem query_answer_cases_syntax : queryAnswerCases =
    [(a "Some" [a "PremiseQueryAnswer" [v "rowIndex", v "assignment", v "origins"]], queryAnswerBody),
      (.symbol "None", caseData (v "agenda") queryAgendaCases),
      (v "badAnswer", .symbol "None")] := by decide +kernel
theorem query_agenda_cases_syntax : queryAgendaCases =
    [(.symbol "LNil", queryEmptyBody),
      (a "LCons" [v "queryTask", v "queryRest"], queryProgressBody),
      (v "badAgenda", .symbol "None")] := by decide +kernel

def queryTaskCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue tail), ("cursor", number cursor),
    ("queryState", encoded (queryStateTerm machine)), ("request", QueryExecution.queryValue request)] ++
    taskCaller environment (.query request machine cursor tail) free

def queryRequestCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("initial", assignmentValue request.initial), ("arguments", patternsValue request.arguments),
    ("relation", stringValue request.relation), ("context", contextValue request.context)] ++
    queryTaskCaller environment outer request machine cursor tail free

def queryContextCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("quantifiers", number request.context.quantifierDepth), ("premiseIndex", number request.context.premiseIndex),
    ("bound", boundValue request.context.bound), ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.context.spec)),
    ("rule", ruleValue request.context.rule), ("ruleIndex", number request.context.ruleIndex)] ++
    queryRequestCaller environment outer request machine cursor tail free

def queryMachineCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("work", number machine.work), ("unresolved", encoded (encodeList queryObligationTerm machine.unresolved)),
    ("answers", encoded (encodeList QueryExecution.queryAnswerTerm machine.answers)),
    ("agenda", encoded (encodeList queryTaskTerm machine.agenda))] ++
    queryContextCaller environment outer request machine cursor tail free

theorem query_task_selected (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.query request machine cursor tail) free)
      (taskValue (.query request machine cursor tail)) taskCases =
      some (queryTaskCaller environment outer request machine cursor tail free, taskBody 2) := by
  simp [task_cases_syntax, taskValue, taskTerm, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem expand_query_body_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns program (queryMachineCaller environment outer request machine cursor tail free)
      state queryStateBody state answer) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state answer := by
  apply expand_branch_returns program agreement state environment outer (.query request machine cursor tail) free
    (queryTaskCaller environment outer request machine cursor tail free) (taskBody 2) answer
    (query_task_selected environment outer request machine cursor tail free)
  rw [query_task_shape]
  apply branch_returns program (queryTaskCaller environment outer request machine cursor tail free)
    (queryRequestCaller environment outer request machine cursor tail free) state _ (QueryExecution.queryValue request)
    queryRequestCases queryRequestBody answer
  · simpa [queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (queryTaskCaller environment outer request machine cursor tail free) state "request"
  · simp [query_request_cases_syntax, QueryExecution.queryValue, queryRequestTerm,
      queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [query_request_shape]
    apply branch_returns program (queryRequestCaller environment outer request machine cursor tail free)
      (queryContextCaller environment outer request machine cursor tail free) state _ (contextValue request.context)
      queryContextCases queryContextBody answer
    · simpa [queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
        applySubst, Subst.lookup] using
        variable_returns program (queryRequestCaller environment outer request machine cursor tail free) state "context"
    · simp [query_context_cases_syntax, contextValue, contextTerm,
        queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [query_context_shape]
      apply branch_returns program (queryContextCaller environment outer request machine cursor tail free)
        (queryMachineCaller environment outer request machine cursor tail free) state _ (encoded (queryStateTerm machine))
        queryStateCases queryStateBody answer
      · simpa [queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
          applySubst, Subst.lookup] using
          variable_returns program (queryContextCaller environment outer request machine cursor tail free) state "queryState"
      · simp [query_state_cases_syntax, queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm, queryMachineCaller, queryContextCaller, queryRequestCaller,
          queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · exact returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem query_commit_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (caller : Subst) (state : State) (environment : Environment) (request : Query.Request)
    (machine : Query.State environment request) (current : Query.Task environment request)
    (rest : List (Query.Task environment request)) (agenda : machine.agenda = current :: rest)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [QueryExecution.encoded (queryStateTerm machine),
        QueryExecution.encoded (encodeOption QueryExecution.queryExpansionTerm
          (some (Query.expand environment request current)))]) :
    PureReturns program caller state (QueryExecution.a "gslt:premise:machine-commit" arguments) state
      (QueryExecution.encoded (encodeOption queryStateTerm (some (Query.tick environment request machine)))) := by
  let values := [QueryExecution.encoded (queryStateTerm machine),
    QueryExecution.encoded (encodeOption QueryExecution.queryExpansionTerm
      (some (Query.expand environment request current)))]
  let aliases : Subst := [("queryState", values[0]!), ("queryExpansion", values[1]!)]
  have sourceCaptured : arguments.map (applySubst caller) =
      [CettaWireAtom.encode (PremiseSchedulerExecution.schedulerStateTerm
        queryTaskTerm QueryExecution.queryAnswerTerm queryObligationTerm machine),
       CettaWireAtom.encode (encodeOption (PremiseSchedulerExecution.schedulerExpansionTerm
         queryTaskTerm QueryExecution.queryAnswerTerm queryObligationTerm)
         (machine.agenda.head?.map (Query.expand environment request)))] := by
    simp only [agenda, List.head?_cons, Option.map_some]
    exact captured
  have returned := PremiseSchedulerExecution.commit_captured_returns caller state queryTaskTerm
    QueryExecution.queryAnswerTerm queryObligationTerm (Query.expand environment request) machine arguments sourceCaptured
  have transported := captured_call_in_extension PremiseSchedulerExecution.runtime_closed agreement
    caller aliases state state "gslt:premise:machine-commit" arguments ["queryState", "queryExpansion"] _
    (by decide) (by decide) (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < arguments.length := (List.getElem?_eq_some_iff.mp selected).1
      have length : arguments.length = 2 := by
        have same := congrArg List.length captured
        simpa only [List.length_map, List.length_cons, List.length_nil] using same
      have small : offset = 0 ∨ offset = 1 := by omega
      rcases small with rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      simpa [aliases, values, applySubst, Subst.lookup] using captured) returned
  exact transported


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace QueryFrame

def answeredData : Atom := a "Some" [a "PremiseExpansion" [
  a "LCons" [a "PremiseDeliver" [a "PremiseResult" [
    a "PremiseGoal" [v "context", a "RelationQuery" [v "relation", v "arguments"], v "initial"],
    a "PremiseAnswer" [v "assignment", a "PremiseQueryEvent" [v "premiseIndex", v "quantifiers", v "rowIndex", v "origins"]]],
    v "continuation"], a "LCons" [a "PremiseQuery" [v "request", v "queryState", v "next", v "continuation"], .symbol "LNil"]],
  .symbol "LNil", .symbol "LNil"]]
def emptyData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", v "reasons"]]
def pendingData : Atom := a "Some" [a "PremiseExpansion" [a "LCons" [
  a "PremiseQuery" [v "request", v "nextState", v "cursor", v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def commitCases : SpaceSemantics.Cases :=
  [(a "Some" [v "nextState"], pendingData), (v "badCommit", .symbol "None")]
def commitBody : Atom := caseData (a "gslt:premise:machine-commit" [v "queryState", v "expanded"]) commitCases

theorem answered_shape : queryAnswerBody = a "let" [v "next", a "+" [v "cursor", number 1], answeredData] := by decide +kernel
theorem empty_shape : queryEmptyBody =
    a "let" [v "reasons", a Helper.queryObligations.head [v "unresolved"], emptyData] := by decide +kernel
theorem progress_shape : queryProgressBody = a "let" [v "expanded",
    a "gslt:premise:query-expand-in" [v "environment", v "request", v "queryTask"], commitBody] := by decide +kernel

local macro "environment_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

theorem answered_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program answeredData := by unfold answeredData; environment_template (program) (agreement)
theorem empty_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program emptyData := by unfold emptyData; environment_template (program) (agreement)
theorem pending_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program pendingData := by unfold pendingData; environment_template (program) (agreement)

theorem expand_query_answer_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (answer : Query.Answer environment request)
    (found : machine.answers[cursor]? = some answer) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let selected := [("origins", encoded (originsTerm answer.origins)), ("assignment", assignmentValue answer.assignment),
    ("rowIndex", number answer.rowIndex)] ++ caller
  let final := ("next", number (cursor + 1)) :: selected
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller selected state _ (encoded (encodeOption QueryExecution.queryAnswerTerm (some answer)))
    queryAnswerCases queryAnswerBody _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa only [found] using returned
  · simp [query_answer_cases_syntax, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
      queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, QueryExecution.queryAnswerTerm,
      assignmentValue, encodeOption,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [answered_shape]
    apply named_let_returns program selected state "next" _ (number (cursor + 1)) answeredData _
    · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
        taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · apply QueryExecution.Parameterized.add_returns program queryAgreement selected state cursor 1
        (v "cursor") (number 1)
      · simpa [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
          variable_returns program selected state "cursor"
      · exact grounded_returns program selected state (.int 1)
    · unfold expansionValue Execution.expandQuery
      rw [found]
      exact (by
        simpa [answeredData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, resultTerm, goalTerm, eventTerm,
          InferenceCettaWire.AuthoredRule.premiseTerm, final, selected, caller,
          queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, assignmentValue, QueryExecution.assignmentValue,
          QueryExecution.queryValue, queryRequestTerm, contextValue, QueryExecution.contextValue,
          stringValue, patternsValue, QueryExecution.patternsValue, number, encodeOption, encodeList,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program final state answeredData (answered_template program agreement))

theorem expand_query_empty_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (missing : machine.answers[cursor]? = none)
    (empty : machine.agenda = []) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let final := ("reasons", encoded (encodeList obligationTerm (machine.unresolved.map Execution.Obligation.query))) :: caller
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller caller state _ (.symbol "None") queryAnswerCases
    (caseData (v "agenda") queryAgendaCases) _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa [missing, encodeOption, CettaWireAtom.encode] using returned
  · simp [query_answer_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · apply branch_returns program caller caller state _ (.symbol "LNil") queryAgendaCases queryEmptyBody _
    · simpa [caller, queryMachineCaller, empty, encodeList, applySubst, Subst.lookup, CettaWireAtom.encode] using
        variable_returns program caller state "agenda"
    · simp [query_agenda_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · rw [empty_shape]
      apply named_let_returns program caller state "reasons" _
        (encoded (encodeList obligationTerm (machine.unresolved.map Execution.Obligation.query))) emptyData _
      · simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · exact query_obligations_captured_returns program agreement caller state machine.unresolved (v "unresolved")
          (by simp [caller, queryMachineCaller, applySubst, Subst.lookup])
      · unfold expansionValue Execution.expandQuery
        rw [missing]
        simp only [empty, List.isEmpty_nil, ↓reduceIte]
        exact (by
          simpa [emptyData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, final, caller, encodeOption, encodeList,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program final state emptyData (empty_template program agreement))


theorem expand_query_progress_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (schedulerAgreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.stateFreeWithin
      footprint environment request machine)
    (missing : machine.answers[cursor]? = none)
    (current : Query.Task environment request) (rest : List (Query.Task environment request))
    (agenda : machine.agenda = current :: rest) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let free := environment.free.entriesOn footprint
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let selected := [("queryRest", encoded (encodeList queryTaskTerm rest)), ("queryTask", encoded (queryTaskTerm current))] ++ caller
  let expanded := ("expanded", QueryExecution.expansionValue (Query.expand environment request current)) :: selected
  let final := ("nextState", encoded (queryStateTerm (Query.tick environment request machine))) :: expanded
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller caller state _ (.symbol "None") queryAnswerCases
    (caseData (v "agenda") queryAgendaCases) _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa [missing, encodeOption, CettaWireAtom.encode] using returned
  · simp [query_answer_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · apply branch_returns program caller selected state _ (encoded (encodeList queryTaskTerm (current :: rest)))
      queryAgendaCases queryProgressBody _
    · simpa [caller, queryMachineCaller, agenda, applySubst, Subst.lookup] using
        variable_returns program caller state "agenda"
    · simp [query_agenda_cases_syntax, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
        queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, encodeList,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [progress_shape]
      apply named_let_returns program selected state "expanded" _
        (QueryExecution.expansionValue (Query.expand environment request current)) commitBody _
      · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · apply QueryExecution.Parameterized.helper_capture program queryAgreement .expand selected state
          [v "environment", v "request", v "queryTask"]
          [environmentValue environment free, QueryExecution.queryValue request, QueryExecution.taskValue current] _ rfl
        · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
            taskCaller, environmentCaller, callee, Helper.names, QueryExecution.taskValue, applySubst, Subst.lookup]
        · exact QueryExecution.Parameterized.Trajectory.query_expand_within_returns program queryAgreement lower
            state environment request current unregistered footprint provider (covered.1 current (by simp [agenda]))
      · unfold commitBody
        apply branch_returns program expanded final state _
          (encoded (encodeOption queryStateTerm (some (Query.tick environment request machine)))) commitCases pendingData _
        · exact query_commit_in_extension_returns program schedulerAgreement expanded state environment request machine current rest agenda
            [v "queryState", v "expanded"] (by
              simp [expanded, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
                taskCaller, environmentCaller, callee, Helper.names, QueryExecution.expansionValue,
                applySubst, Subst.lookup])
        · simp [commitCases, final, expanded, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
            queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, encodeOption,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · unfold expansionValue Execution.expandQuery
          rw [missing]
          simp only [agenda, List.isEmpty_cons]
          exact (by
            simpa [pendingData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, final, expanded, selected, caller, queryMachineCaller,
              queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
              QueryExecution.queryValue, queryRequestTerm, number, encodeOption, encodeList,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program final state pendingData (pending_template program agreement))

theorem expand_query_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (schedulerAgreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.stateFreeWithin
      footprint environment request machine) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expand environment outer (.query request machine cursor tail))) := by
  cases found : machine.answers[cursor]? with
  | some answer => exact expand_query_answer_returns program agreement queryAgreement lower state environment outer request machine cursor tail _ answer found
  | none =>
      cases agenda : machine.agenda with
      | nil => exact expand_query_empty_returns program agreement lower state environment outer request machine cursor tail _ found agenda
      | cons current rest =>
          exact expand_query_progress_returns program agreement queryAgreement schedulerAgreement lower
            state environment outer request machine cursor tail unregistered footprint provider covered found current rest agenda


end QueryFrame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.interpreted_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.Trajectory.query_expand_within_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.Trajectory.query_expand_prefix_returns
