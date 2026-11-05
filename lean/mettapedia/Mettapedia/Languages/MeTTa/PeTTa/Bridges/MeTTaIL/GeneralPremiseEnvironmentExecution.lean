import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

/-! Source clauses and admission for the original finite premise environment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open scoped ProgramQuotation

def admissionSource : Program := RuleExecutionProgram.premiseAdmissionProgram

def environmentSource : Program := RuleExecutionProgram.premiseFullEnvironmentProgram

def sourceProgram : Program := admissionSource.append environmentSource

def runtime : Program := premiseRuntimeProgram.append sourceProgram

theorem source_head_inventory : sourceProgram.equations.map (·.head) =
    ["gslt:premise:admission-keys", "gslt:premise:admission-occurrence-keys", "gslt:premise:admission-nodup",
      "gslt:premise:admission-context-covered", "gslt:premise:admission-occurrences", "gslt:premise:binding-admitted",
      "gslt:premise:query-obligations", "gslt:premise:machine-deliver-in", "gslt:premise:machine-evaluate-in",
      "gslt:premise:machine-expand-in"] := by decide +kernel

#print axioms source_head_inventory

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

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
abbrev environmentValue (environment : Environment) (free : List (String × TypeExpr)) : Atom := encoded (environmentTerm environment free)

def caseData (expression : Atom) (rows : SpaceSemantics.Cases) : Atom :=
  a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]

theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

abbrev goalValue (goal : Execution.Goal) : Atom := encoded (goalTerm goal)
abbrev continuationValue {environment : Environment} {goal outer : Execution.Goal}
    (tail : Execution.Continuation environment goal outer) : Atom := encoded (continuationTerm tail)
abbrev resultValue {environment : Environment} {goal : Execution.Goal}
    (result : Execution.Result environment goal) : Atom := encoded (resultTerm result)
abbrev taskValue {environment : Environment} {outer : Execution.Goal}
    (task : Execution.Task environment outer) : Atom := encoded (taskTerm task)
abbrev expansionValue {environment : Environment} {outer : Execution.Goal}
    (expanded : Scheduler.Expansion (Execution.Task environment outer) (Execution.Result environment outer) Execution.Obligation) : Atom :=
  encoded (encodeOption expansionTerm (some expanded))

inductive Helper where
  | keys | occurrenceKeys | nodup | contextCovered | occurrences | admitted
  | queryObligations | deliver | evaluate | expand
  deriving DecidableEq

def Helper.index : Helper → Nat
  | .keys => 0 | .occurrenceKeys => 1 | .nodup => 2 | .contextCovered => 3 | .occurrences => 4
  | .admitted => 5 | .queryObligations => 6 | .deliver => 7 | .evaluate => 8 | .expand => 9

def Helper.head : Helper → String
  | .keys => "gslt:premise:admission-keys"
  | .occurrenceKeys => "gslt:premise:admission-occurrence-keys"
  | .nodup => "gslt:premise:admission-nodup"
  | .contextCovered => "gslt:premise:admission-context-covered"
  | .occurrences => "gslt:premise:admission-occurrences"
  | .admitted => "gslt:premise:binding-admitted"
  | .queryObligations => "gslt:premise:query-obligations"
  | .deliver => "gslt:premise:machine-deliver-in"
  | .evaluate => "gslt:premise:machine-evaluate-in"
  | .expand => "gslt:premise:machine-expand-in"

def Helper.names : Helper → List String
  | .keys | .occurrenceKeys => ["rows"]
  | .nodup => ["keys"]
  | .contextCovered => ["context", "dependencies"]
  | .occurrences => ["rule", "spec", "rows"]
  | .admitted => ["rule", "spec"]
  | .queryObligations => ["reasons"]
  | .deliver => ["environment", "result", "continuation"]
  | .evaluate => ["environment", "goal", "continuation"]
  | .expand => ["environment", "task"]

def equation (helper : Helper) : SpaceSemantics.Equation :=
  sourceProgram.equations[helper.index]'(by cases helper <;> decide +kernel)

def callee (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

def dataHeads : List String :=
  ["LCons", "LNil", "Some", "None", "RuleOccurrence", "PremiseExpansion", "PremiseQueryObligation", "PremiseQuery",
    "PremiseQueryRequest", "PremiseState", "PremiseDeliver", "PremiseResult", "PremiseGoal", "PremiseAnswer",
    "PremiseQueryEvent", "PremiseFreshnessEvent", "PremiseFreshnessProjection", "PremiseStepProjection", "PremiseStepSort",
    "PremiseStepCall", "StepsGoal", "PremiseStepped", "PremiseRootMatch", "ScopedMatcherRequest", "RulePremise",
    "PremiseBindingUnavailable", "PremiseRuleUnavailable", "PremiseBindingRejected", "PremiseSourceRejected", "RelationQuery", "PremiseEvaluate"]

def ownedHeads (head : String) : Bool :=
  ([Helper.keys.head, Helper.occurrenceKeys.head, Helper.nodup.head, Helper.contextCovered.head, Helper.occurrences.head,
    Helper.admitted.head, Helper.queryObligations.head, Helper.deliver.head, Helper.evaluate.head, Helper.expand.head,
    "+", "=="] ++ dataHeads).contains head

theorem helper_supported (helper : Helper) : ownedHeads helper.head = true := by cases helper <;> decide

set_option maxHeartbeats 4000000 in
theorem helper_clause (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (values : List Atom) (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (callee helper values) (equation helper).body] := by
  apply PureData.selected_clause_agreement agreement (helper_supported helper)
  apply PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
  · cases helper <;> rfl
  · cases helper <;> decide +kernel
  · cases helper <;> decide
  · exact length

set_option maxHeartbeats 4000000 in
theorem helper_raw (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  rw [← agreement.demand helper.head index (helper_supported helper)]
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases small with rfl | rfl | rfl <;> first | omega | decide +kernel

theorem helper_call (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (callee helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (callee helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide) _ _ _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
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
    cases helper <;> decide +kernel
  · intro index bounded
    exact helper_raw program agreement helper index (by omega)
  · simpa only [captured_closed] using captured.symm

theorem data_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have supported : ownedHeads head = true := by simp [ownedHeads, member]
    rw [← agreement.dispatch head supported]
    have checked : dataHeads.all (fun name => decide
        ((ioHead name || StdLib.known name || runtime.equations.any (·.head == name)) = false ∧
          name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])) = true := by
      rfl
    have row := List.all_eq_true.mp checked head member
    rw [decide_eq_true_eq] at row
    exact row.1
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

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

#print axioms helper_clause
#print axioms helper_raw
#print axioms helper_call
#print axioms helper_capture
#print axioms data_template

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

def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [.symbol "case", _, .expression rows] => (readCases rows).getD []
  | _ => []

def environmentCases (helper : Helper) : SpaceSemantics.Cases := sourceCases (equation helper).body
def environmentBody (helper : Helper) : Atom :=
  ((environmentCases helper)[0]?).map Prod.snd |>.getD (.symbol "None")

def taskCases : SpaceSemantics.Cases := sourceCases (environmentBody .expand)
def taskBody (index : Nat) : Atom := ((taskCases[index]?).map Prod.snd).getD (.symbol "None")
def goalCases : SpaceSemantics.Cases := sourceCases (environmentBody .evaluate)
def goalBody (index : Nat) : Atom := ((goalCases[index]?).map Prod.snd).getD (.symbol "None")

def environmentPattern : Atom := a "PremiseEnvironment" [v "declarations", v "rewrites", v "specifications",
  a "PremiseProvider" [v "signatures", v "rows"], v "reflection", v "free"]

theorem expand_environment_shape : (equation .expand).body =
    caseData (v "environment") (environmentCases .expand) := by decide +kernel
theorem evaluate_environment_shape : (equation .evaluate).body =
    caseData (v "environment") (environmentCases .evaluate) := by decide +kernel

theorem expand_environment_cases : environmentCases .expand =
    [(environmentPattern, caseData (v "task") taskCases), (v "badEnvironment", .symbol "None")] := by decide +kernel
theorem evaluate_environment_cases : environmentCases .evaluate =
    [(environmentPattern, caseData (v "goal") goalCases), (v "badEnvironment", .symbol "None")] := by decide +kernel

theorem task_cases_syntax : taskCases =
  [(a "PremiseEvaluate" [v "goal", v "continuation"], taskBody 0),
    (a "PremiseDeliver" [v "result", v "continuation"], taskBody 1),
    (a "PremiseQuery" [v "request", v "queryState", v "cursor", v "continuation"], taskBody 2),
    (a "PremiseRootMatch" [v "bound", v "type", v "source", v "index", v "rule", v "spec", v "matcher", v "cursor", v "continuation"], taskBody 3),
    (a "PremiseTargetMatch" [v "call", v "index", v "trace", v "captured", v "completed", v "history", v "target", v "matcher", v "cursor", v "continuation"], taskBody 4),
    (a "PremiseScanChildren" [v "bound", v "type", v "source", v "limit", v "cursor", v "continuation"], taskBody 5),
    (v "badTask", .symbol "None")] := by decide +kernel

theorem goal_cases_syntax : goalCases =
  [(a "PremiseGoal" [v "context", v "premise", v "initial"], goalBody 0),
    (a "RootGoal" [v "bound", v "type", v "source", v "index"], goalBody 1),
    (a "PremisesGoal" [v "context", v "premises", v "initial"], goalBody 2),
    (a "QuantifiedGoal" [v "context", v "parameter", v "body", v "index", v "elements", v "initial"], goalBody 3),
    (a "StepsGoal" [v "bound", v "type", v "source", v "limit"], goalBody 4),
    (v "badGoal", .symbol "None")] := by decide +kernel

def environmentCaller (helper : Helper) (environment : Environment) (free : List (String × TypeExpr))
    (values : List Atom) : Subst :=
  [("free", encoded (DeclarationTyping.freeContextTerm free)), ("reflection", encoded (reflectionTerm environment.reflection)),
    ("rows", encoded (encodeList providerRowTerm environment.provider.rows)),
    ("signatures", encoded (encodeList signatureTerm environment.provider.signatures)),
    ("specifications", encoded (encodeList specificationTerm environment.specifications)),
    ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)),
    ("declarations", encoded (DeclarationTyping.declarationsTerm environment.language.terms))] ++ callee helper values

def taskCaller (environment : Environment) {outer : Execution.Goal} (task : Execution.Task environment outer)
    (free : List (String × TypeExpr)) : Subst :=
  environmentCaller .expand environment free [environmentValue environment free, taskValue task]

def goalCaller (environment : Environment) (outer goal : Execution.Goal)
    (continuation : Execution.Continuation environment goal outer) (free : List (String × TypeExpr)) : Subst :=
  environmentCaller .evaluate environment free [environmentValue environment free, goalValue goal, continuationValue continuation]

theorem environment_fields_match (helper : Helper) (environment : Environment) (free : List (String × TypeExpr))
    (values : List Atom) (allowed : helper = .expand ∨ helper = .evaluate) :
    SpaceSemantics.matchValue (callee helper values) environmentPattern (environmentValue environment free) =
      some (environmentCaller helper environment free values) := by
  rcases allowed with rfl | rfl
  all_goals rcases values with _ | ⟨one, _ | ⟨two, _ | ⟨three, rest⟩⟩⟩
  all_goals simp [environmentPattern, environmentValue, environmentValue, environmentTerm,
    providerTerm, environmentCaller, callee, Helper.names, encoded, a, v,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]; rfl

theorem expand_branch_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (task : Execution.Task environment outer)
    (free : List (String × TypeExpr)) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (taskCaller environment task free) (taskValue task) taskCases = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a Helper.expand.head [environmentValue environment free, taskValue task]) state answer := by
  let caller := callee .expand [environmentValue environment free, taskValue task]
  apply helper_call program agreement .expand [] state _ _ _ rfl (captured_closed _)
  rw [expand_environment_shape]
  apply branch_returns program caller (taskCaller environment task free) state _ (environmentValue environment free)
    (environmentCases .expand) (caseData (v "task") taskCases) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "environment"
  · rw [expand_environment_cases, SpaceSemantics.selectCase,
      environment_fields_match .expand environment free _ (Or.inl rfl)]
    rfl
  · apply branch_returns program (taskCaller environment task free) selected state _ (taskValue task) taskCases body _ _ matched returned
    simpa [taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (taskCaller environment task free) state "task"

theorem evaluate_branch_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer goal : Execution.Goal)
    (continuation : Execution.Continuation environment goal outer) (free : List (String × TypeExpr))
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (goalCaller environment outer goal continuation free) (goalValue goal) goalCases = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue goal, continuationValue continuation]) state answer := by
  let caller := callee .evaluate [environmentValue environment free, goalValue goal, continuationValue continuation]
  apply helper_call program agreement .evaluate [] state _ _ _ rfl (captured_closed _)
  rw [evaluate_environment_shape]
  apply branch_returns program caller (goalCaller environment outer goal continuation free) state _ (environmentValue environment free)
    (environmentCases .evaluate) (caseData (v "goal") goalCases) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "environment"
  · rw [evaluate_environment_cases, SpaceSemantics.selectCase,
      environment_fields_match .evaluate environment free _ (Or.inr rfl)]
    rfl
  · apply branch_returns program (goalCaller environment outer goal continuation free) selected state _ (goalValue goal) goalCases body _ _ matched returned
    simpa [goalCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (goalCaller environment outer goal continuation free) state "goal"

#print axioms task_cases_syntax
#print axioms goal_cases_syntax
#print axioms environment_fields_match
#print axioms expand_branch_returns
#print axioms evaluate_branch_returns

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

attribute [local simp] a v encoded number stringValue

private def keysData : Atom := a "LCons" [v "name", v "keys"]
private def keysCons : Atom := a "let" [v "keys", a Helper.keys.head [v "rest"], keysData]
private def keysCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "TypeBinding" [v "name", v "type"], v "rest"], keysCons),
    (a "LCons" [a "RuleDependency" [v "name", v "types"], v "rest"], keysCons),
    (v "bad", .symbol "None")]
private theorem keys_shape : (equation .keys).body = caseData (v "rows") keysCases := by decide +kernel

private def keyTag (dependency : Bool) : String := if dependency then "RuleDependency" else "TypeBinding"
private def payloadName (dependency : Bool) : String := if dependency then "types" else "type"
private def keyRowsTerm (dependency : Bool) (rows : List (String × Term)) : Term :=
  encodeList (fun row => .application (keyTag dependency) [.string row.1, row.2]) rows
private def keyNamesTerm (rows : List (String × Term)) : Term := encodeList Term.string (rows.map Prod.fst)

theorem admission_keys_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (dependency : Bool) (rows : List (String × Term)) :
    PureReturns program [] state (a "gslt:premise:admission-keys" [encoded (keyRowsTerm dependency rows)]) state
      (encoded (keyNamesTerm rows)) := by
  induction rows with
  | nil =>
      let caller := callee .keys [encoded (keyRowsTerm dependency [])]
      apply helper_call program agreement .keys [] state _ _ _ rfl (captured_closed _)
      rw [keys_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") keysCases (.symbol "LNil") _
      · simpa [caller, callee, Helper.names, keyRowsTerm, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "rows"
      · simp [keysCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons entry rows ih =>
      rcases entry with ⟨name, payload⟩
      let caller := callee .keys [encoded (keyRowsTerm dependency ((name, payload) :: rows))]
      let selected := [("rest", encoded (keyRowsTerm dependency rows)),
        (payloadName dependency, encoded payload), ("name", stringValue name)] ++ caller
      let final := ("keys", encoded (keyNamesTerm rows)) :: selected
      apply helper_call program agreement .keys [] state _ _ _ rfl (captured_closed _)
      rw [keys_shape]
      apply branch_returns program caller selected state _ (encoded (keyRowsTerm dependency ((name, payload) :: rows))) keysCases keysCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "rows"
      · cases dependency <;>
          simp [keysCases, keyRowsTerm, keyTag, payloadName, selected, caller, callee, Helper.names, encodeList,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold keysCons
        apply named_let_returns program selected state "keys" _ (encoded (keyNamesTerm rows)) keysData _
        · cases dependency <;>
            simp [selected, payloadName, caller, callee, Helper.names, Subst.lookup]
        · exact helper_capture program agreement .keys selected state _ _ _ rfl
            (by cases dependency <;>
              simp [selected, payloadName, caller, callee, Helper.names, applySubst, Subst.lookup]) ih
        · have templated : PureData.Template program keysData := by
            apply data_template program agreement "LCons" _ (by decide)
            intro child member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl <;> exact .captured _
          cases dependency <;>
            simpa [keysData, keyNamesTerm, encodeList, final, selected, payloadName, caller, callee, Helper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program final state _ templated

theorem admission_context_keys_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (context : List (String × TypeExpr)) :
    PureReturns program [] state (a "gslt:premise:admission-keys"
      [encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm context)]) state
      (encoded (encodeList Term.string (context.map Prod.fst))) := by
  unfold InferenceCettaWire.AuthoredRule.typeBindingTerm
  simpa [keyRowsTerm, keyNamesTerm, keyTag, encodeList_map, Function.comp_def,
    List.map_map] using
    admission_keys_returns program agreement state false
      (context.map fun entry => (entry.1, InferenceCettaWire.AuthoredRule.typeTerm entry.2))

theorem admission_dependency_keys_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (dependencies : List (String × List TypeExpr)) :
    PureReturns program [] state (a "gslt:premise:admission-keys"
      [encoded (encodeList InferenceCettaWire.AuthoredRule.dependencyTerm dependencies)]) state
      (encoded (encodeList Term.string (dependencies.map Prod.fst))) := by
  unfold InferenceCettaWire.AuthoredRule.dependencyTerm
  simpa [keyRowsTerm, keyNamesTerm, keyTag, encodeList_map, Function.comp_def,
    List.map_map] using
    admission_keys_returns program agreement state true
      (dependencies.map fun entry => (entry.1, InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm entry.2))

#print axioms admission_keys_returns
#print axioms admission_context_keys_returns
#print axioms admission_dependency_keys_returns

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

attribute [local simp] a v encoded number stringValue

def occurrenceKeyTerm (row : MetavariableOccurrence) : Term :=
  InferenceCettaWire.AuthoredRule.occurrenceTerm { row with arguments := [] }

private def occurrenceKeysData : Atom := a "LCons" [
  a "RuleOccurrence" [v "name", v "site", v "path", .symbol "LNil"], v "keys"]
private def occurrenceKeysCons : Atom := a "let" [v "keys", a Helper.occurrenceKeys.head [v "rest"], occurrenceKeysData]
private def occurrenceKeysCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "RuleOccurrence" [v "name", v "site", v "path", v "arguments"], v "rest"], occurrenceKeysCons),
    (v "bad", .symbol "None")]
private theorem occurrence_keys_shape : (equation .occurrenceKeys).body = caseData (v "rows") occurrenceKeysCases := by
  decide +kernel

theorem admission_occurrence_keys_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (rows : List MetavariableOccurrence) :
    PureReturns program [] state (a Helper.occurrenceKeys.head
      [encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)]) state
      (encoded (encodeList occurrenceKeyTerm rows)) := by
  induction rows with
  | nil =>
      let caller := callee .occurrenceKeys [encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm [])]
      apply helper_call program agreement .occurrenceKeys [] state _ _ _ rfl (captured_closed _)
      rw [occurrence_keys_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") occurrenceKeysCases (.symbol "LNil") _
      · simpa [caller, callee, Helper.names, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "rows"
      · simp [occurrenceKeysCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons row rows ih =>
      let caller := callee .occurrenceKeys [encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm (row :: rows))]
      let selected := [("rest", encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)),
        ("arguments", encoded (InferenceCettaWire.encodePatterns row.arguments)),
        ("path", encoded (InferenceCettaWire.encodeList Term.natural row.path)),
        ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm row.site)), ("name", stringValue row.name)] ++ caller
      let final := ("keys", encoded (encodeList occurrenceKeyTerm rows)) :: selected
      apply helper_call program agreement .occurrenceKeys [] state _ _ _ rfl (captured_closed _)
      rw [occurrence_keys_shape]
      apply branch_returns program caller selected state _
        (encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm (row :: rows)))
        occurrenceKeysCases occurrenceKeysCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "rows"
      · simp [occurrenceKeysCases, selected, caller, callee, Helper.names,
          InferenceCettaWire.AuthoredRule.occurrenceTerm, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold occurrenceKeysCons
        apply named_let_returns program selected state "keys" _ (encoded (encodeList occurrenceKeyTerm rows)) occurrenceKeysData _
        · simp [selected, caller, callee, Helper.names, Subst.lookup]
        · exact helper_capture program agreement .occurrenceKeys selected state _ _ _ rfl
            (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup]) ih
        · have templated : PureData.Template program occurrenceKeysData := by
            apply data_template program agreement "LCons" _ (by decide)
            intro child member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · apply data_template program agreement "RuleOccurrence" _ (by decide)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl | rfl
              all_goals first | exact .captured _ | exact .symbol _
            · exact .captured _
          simpa [occurrenceKeysData, occurrenceKeyTerm, InferenceCettaWire.AuthoredRule.occurrenceTerm,
            InferenceCettaWire.encodePatterns, encodeList, final, selected, caller, callee, Helper.names,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program final state _ templated

def MemberReturns (program : Program) : Prop :=
  ∀ (caller : Subst) (state : State) (key : Term) (keys : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [encoded key, encoded (encodeList id keys)] →
    PureReturns program caller state (a "gslt:automata:member" [one, two]) state
      (Effects.boolean (decide (key ∈ keys)))

private def nodupCons : Atom := a "if" [a "gslt:automata:member" [v "key", v "rest"],
  Effects.boolean false, a Helper.nodup.head [v "rest"]]
private def nodupCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true), (a "LCons" [v "key", v "rest"], nodupCons),
    (v "bad", Effects.boolean false)]
private theorem nodup_shape : (equation .nodup).body = caseData (v "keys") nodupCases := by decide +kernel

theorem admission_nodup_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (memberReturns : MemberReturns program) (state : State) (keys : List Term) :
    PureReturns program [] state (a Helper.nodup.head [encoded (encodeList id keys)]) state
      (Effects.boolean (decide keys.Nodup)) := by
  induction keys with
  | nil =>
      let caller := callee .nodup [encoded (encodeList id [])]
      apply helper_call program agreement .nodup [] state _ _ _ rfl (captured_closed _)
      rw [nodup_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") nodupCases (Effects.boolean true) _
      · simpa [caller, callee, Helper.names, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "keys"
      · simp [nodupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program caller state (.bool true)
  | cons key keys ih =>
      let caller := callee .nodup [encoded (encodeList id (key :: keys))]
      let selected := [("rest", encoded (encodeList id keys)), ("key", encoded key)] ++ caller
      apply helper_call program agreement .nodup [] state _ _ _ rfl (captured_closed _)
      rw [nodup_shape]
      apply branch_returns program caller selected state _ (encoded (encodeList id (key :: keys))) nodupCases nodupCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "keys"
      · simp [nodupCases, selected, caller, callee, Helper.names, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold nodupCons
        apply bool_if_returns program selected state _ (decide (key ∈ keys)) _ _ _
        · exact memberReturns selected state key keys (v "key") (v "rest")
            (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])
        · by_cases present : key ∈ keys
          · simpa [present, List.nodup_cons, Effects.boolean] using grounded_returns program selected state (.bool false)
          · simpa [present, List.nodup_cons] using
              helper_capture program agreement .nodup selected state _ _ _ rfl
                (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup]) ih

private def coveredCons : Atom := a "if" [a "gslt:automata:member" [v "name", v "dependencies"],
  a Helper.contextCovered.head [v "rest", v "dependencies"], Effects.boolean false]
private def coveredCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true), (a "LCons" [v "name", v "rest"], coveredCons),
    (v "bad", Effects.boolean false)]
private theorem covered_shape : (equation .contextCovered).body = caseData (v "context") coveredCases := by decide +kernel

theorem admission_context_covered_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (memberReturns : MemberReturns program) (state : State) (context dependencies : List Term) :
    PureReturns program [] state (a Helper.contextCovered.head
      [encoded (encodeList id context), encoded (encodeList id dependencies)]) state
      (Effects.boolean (context.all fun name => decide (name ∈ dependencies))) := by
  induction context with
  | nil =>
      let caller := callee .contextCovered [encoded (encodeList id []), encoded (encodeList id dependencies)]
      apply helper_call program agreement .contextCovered [] state _ _ _ rfl (captured_closed _)
      rw [covered_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") coveredCases (Effects.boolean true) _
      · simpa [caller, callee, Helper.names, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "context"
      · simp [coveredCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program caller state (.bool true)
  | cons name context ih =>
      let caller := callee .contextCovered [encoded (encodeList id (name :: context)), encoded (encodeList id dependencies)]
      let selected := [("rest", encoded (encodeList id context)), ("name", encoded name)] ++ caller
      apply helper_call program agreement .contextCovered [] state _ _ _ rfl (captured_closed _)
      rw [covered_shape]
      apply branch_returns program caller selected state _ (encoded (encodeList id (name :: context))) coveredCases coveredCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "context"
      · simp [coveredCases, selected, caller, callee, Helper.names, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold coveredCons
        apply bool_if_returns program selected state _ (decide (name ∈ dependencies)) _ _ _
        · exact memberReturns selected state name dependencies (v "name") (v "dependencies")
            (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])
        · by_cases present : name ∈ dependencies
          · simpa [present] using
              helper_capture program agreement .contextCovered selected state _ _ _ rfl
                (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup]) ih
          · simpa [present, Effects.boolean] using grounded_returns program selected state (.bool false)

#print axioms admission_occurrence_keys_returns
#print axioms admission_nodup_returns
#print axioms admission_context_covered_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

private def occurrenceTupleTerm (key : String × RulePatternSite × List Nat) : Term :=
  InferenceCettaWire.AuthoredRule.occurrenceTerm ⟨key.1, key.2.1, key.2.2, []⟩

private theorem occurrence_tuple_injective : Function.Injective occurrenceTupleTerm := by
  intro left right same
  rcases left with ⟨leftName, leftSite, leftPath⟩
  rcases right with ⟨rightName, rightSite, rightPath⟩
  have original := InferenceCettaWire.AuthoredRule.occurrenceTerm_injective same
  cases original
  rfl

theorem admission_string_nodup_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (memberReturns : MemberReturns program) (state : State) (keys : List String) :
    PureReturns program [] state (a Helper.nodup.head [encoded (encodeList Term.string keys)]) state
      (Effects.boolean (decide keys.Nodup)) := by
  have source := admission_nodup_returns program agreement memberReturns state (keys.map Term.string)
  have injective : Function.Injective Term.string := fun _ _ same => Term.string.inj same
  simpa only [encodeList_map, Function.id_comp, List.nodup_map_iff injective] using source

theorem admission_occurrence_nodup_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (memberReturns : MemberReturns program) (state : State) (rows : List MetavariableOccurrence) :
    PureReturns program [] state (a Helper.nodup.head [encoded (encodeList occurrenceKeyTerm rows)]) state
      (Effects.boolean (decide (rows.map fun row => (row.name, row.site, row.path)).Nodup)) := by
  have same : rows.map occurrenceKeyTerm =
      (rows.map fun row => (row.name, row.site, row.path)).map occurrenceTupleTerm := by
    simp only [List.map_map]
    rfl
  have source := admission_nodup_returns program agreement memberReturns state (rows.map occurrenceKeyTerm)
  have nodup : (rows.map occurrenceKeyTerm).Nodup ↔
      (rows.map fun row => (row.name, row.site, row.path)).Nodup := by
    rw [same, List.nodup_map_iff occurrence_tuple_injective]
  simpa only [encodeList_map, Function.id_comp, nodup] using source

private theorem string_member (name : String) (keys : List String) :
    Term.string name ∈ keys.map Term.string ↔ name ∈ keys := by
  simp only [List.mem_map, Term.string.injEq]
  simp

theorem admission_names_covered_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (memberReturns : MemberReturns program) (state : State) (context dependencies : List String) :
    PureReturns program [] state (a Helper.contextCovered.head
      [encoded (encodeList Term.string context), encoded (encodeList Term.string dependencies)]) state
      (Effects.boolean (context.all fun name => decide (name ∈ dependencies))) := by
  have source := admission_context_covered_returns program agreement memberReturns state
    (context.map Term.string) (dependencies.map Term.string)
  simpa [encodeList_map, Function.comp_def, string_member] using source

theorem context_coverage_value (context : List (String × TypeExpr))
    (dependencies : List (String × List TypeExpr)) :
    ((context.map Prod.fst).all fun name => decide (name ∈ dependencies.map Prod.fst)) =
      context.all (fun entry => dependencies.any (fun declared => declared.1 == entry.1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
  constructor
  · intro covered entry present
    rcases covered entry.1 ⟨entry, present, rfl⟩ with ⟨declared, included, same⟩
    exact ⟨declared, included, same⟩
  · intro covered name present
    rcases present with ⟨entry, included, rfl⟩
    exact covered entry included

#print axioms admission_string_nodup_returns
#print axioms admission_occurrence_nodup_returns
#print axioms admission_names_covered_returns
#print axioms context_coverage_value

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number stringValue

structure AdmissionOperations (program : Program) : Prop where
  member : MemberReturns program
  length : ∀ (caller : Subst) (state : State) (values : List Term) (input : Atom),
    applySubst caller input = encoded (encodeList id values) →
    PureReturns program caller state (a "gslt:automata:length" [input]) state (number values.length)
  declared : ∀ (caller : Subst) (state : State) (rule : RewriteRule) (row : MetavariableOccurrence) (one two : Atom),
    [one, two].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm row)] →
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-declared" [one, two]) state
      (Effects.boolean (occurrenceDeclared rule row))
  dependencies : ∀ (caller : Subst) (state : State) (spec : RuleBindingSpec) (name : String) (one two : Atom),
    [one, two].map (applySubst caller) =
      [encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), stringValue name] →
    PureReturns program caller state (a "gslt:rule:scope-metadata-dependencies" [one, two]) state
      (encoded (encodeOption (encodeList InferenceCettaWire.AuthoredRule.typeTerm) (dependencies? spec name)))
  depth : ∀ (caller : Subst) (state : State) (rule : RewriteRule) (site : RulePatternSite)
    (path : List Nat) (one two three : Atom),
    [one, two, three].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.siteTerm site),
        encoded (InferenceCettaWire.encodeList Term.natural path)] →
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-depth-at-site" [one, two, three]) state
      (encoded (encodeOption Term.natural (occurrenceDepthAtSite? rule site path)))
  ground : ∀ (caller : Subst) (state : State) (depth : Nat) (arguments : List Pattern) (one two : Atom),
    [one, two].map (applySubst caller) = [number depth, patternsValue arguments] →
    PureReturns program caller state (a "gslt:premise:ground-list-at" [one, two]) state
      (Effects.boolean (Pattern.isGroundListAt depth arguments))

theorem admission_length_encoded_returns {α : Type} (program : Program) (lower : AdmissionOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (values : List α) (input : Atom)
    (captured : applySubst caller input = encoded (encodeList encoder values)) :
    PureReturns program caller state (a "gslt:automata:length" [input]) state (number values.length) := by
  simpa only [List.length_map] using lower.length caller state (values.map encoder) input
    (by simpa only [encodeList_map, Function.id_comp] using captured)

theorem ground_list_eq_all (depth : Nat) (arguments : List Pattern) :
    Pattern.isGroundListAt depth arguments = arguments.all (fun argument => argument.isGroundAt depth) := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih => simp only [Pattern.isGroundListAt, List.all_cons, ih]

private def occurrenceValid (rule : RewriteRule) (spec : RuleBindingSpec) (row : MetavariableOccurrence) : Bool :=
  occurrenceDeclared rule row &&
    match dependencies? spec row.name, occurrenceDepthAtSite? rule row.site row.path with
    | some dependencies, some depth =>
        row.arguments.length == dependencies.length && row.arguments.all (fun argument => argument.isGroundAt depth)
    | _, _ => false

private def groundBody : Atom := a "if" [a "gslt:premise:ground-list-at" [v "depth", v "arguments"],
  a Helper.occurrences.head [v "rule", v "spec", v "rest"], Effects.boolean false]
private def arityBody : Atom := a "if" [a "==" [v "arity", v "expected"], groundBody, Effects.boolean false]
private def lengthBody : Atom := a "let*" [.expression [
  .expression [v "arity", a "gslt:automata:length" [v "arguments"]],
  .expression [v "expected", a "gslt:automata:length" [v "dependencies"]]], arityBody]
private def depthCases : SpaceSemantics.Cases :=
  [(a "Some" [v "depth"], lengthBody), (v "missingDepth", Effects.boolean false)]
private def depthBody : Atom := caseData (a "gslt:rule:scope-metadata-occurrence-depth-at-site"
  [v "rule", v "site", v "path"]) depthCases
private def dependenciesCases : SpaceSemantics.Cases :=
  [(a "Some" [v "dependencies"], depthBody), (v "missingDependencies", Effects.boolean false)]
private def dependenciesBody : Atom := caseData (a "gslt:rule:scope-metadata-dependencies"
  [v "spec", v "name"]) dependenciesCases
private def occurrencesCons : Atom := a "if" [a "gslt:rule:scope-metadata-occurrence-declared" [v "rule",
  a "RuleOccurrence" [v "name", v "site", v "path", v "arguments"]], dependenciesBody, Effects.boolean false]
private def occurrencesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
    (a "LCons" [a "RuleOccurrence" [v "name", v "site", v "path", v "arguments"], v "rest"], occurrencesCons),
    (v "bad", Effects.boolean false)]
private theorem occurrences_shape : (equation .occurrences).body = caseData (v "rows") occurrencesCases := by
  decide +kernel

theorem admission_occurrences_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (lower : AdmissionOperations program) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (rows : List MetavariableOccurrence) :
    PureReturns program [] state (a Helper.occurrences.head [ruleValue rule,
      encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
      encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)]) state
      (Effects.boolean (rows.all (occurrenceValid rule spec))) := by
  induction rows with
  | nil =>
      let caller := callee .occurrences [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
        encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm [])]
      apply helper_call program agreement .occurrences [] state _ _ _ rfl (captured_closed _)
      rw [occurrences_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") occurrencesCases (Effects.boolean true) _
      · simpa [caller, callee, Helper.names, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "rows"
      · simp [occurrencesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program caller state (.bool true)
  | cons row rows ih =>
      let caller := callee .occurrences [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
        encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm (row :: rows))]
      let selected := [("rest", encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)),
        ("arguments", patternsValue row.arguments),
        ("path", encoded (InferenceCettaWire.encodeList Term.natural row.path)),
        ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm row.site)), ("name", stringValue row.name)] ++ caller
      apply helper_call program agreement .occurrences [] state _ _ _ rfl (captured_closed _)
      rw [occurrences_shape]
      apply branch_returns program caller selected state _
        (encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm (row :: rows)))
        occurrencesCases occurrencesCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "rows"
      · simp [occurrencesCases, selected, caller, callee, Helper.names, patternsValue, patternsValue,
          InferenceCettaWire.AuthoredRule.occurrenceTerm, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold occurrencesCons
        apply bool_if_returns program selected state _ (occurrenceDeclared rule row) _ _ _
        · exact lower.declared selected state rule row (v "rule")
            (a "RuleOccurrence" [v "name", v "site", v "path", v "arguments"])
            (by simp [selected, caller, callee, Helper.names, InferenceCettaWire.AuthoredRule.occurrenceTerm,
              patternsValue, patternsValue, applySubst, applySubst.applySubstList, Subst.lookup,
              CettaWireAtom.encode, CettaWireAtom.encodeMany])
        · cases declared : occurrenceDeclared rule row with
          | false =>
              simpa [occurrenceValid, declared, Effects.boolean] using grounded_returns program selected state (.bool false)
          | true =>
              simp only [List.all_cons, occurrenceValid, declared, Bool.true_and]
              have dependenciesReturned := lower.dependencies selected state spec row.name (v "spec") (v "name")
                (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup])
              unfold dependenciesBody
              cases dependenciesFound : dependencies? spec row.name with
              | none =>
                  apply branch_returns program selected (("missingDependencies", .symbol "None") :: selected)
                    state _ (.symbol "None") dependenciesCases (Effects.boolean false) _
                  · simpa [dependenciesFound, encodeOption, CettaWireAtom.encode] using dependenciesReturned
                  · simp [dependenciesCases, selected, caller, callee, Helper.names,
                      SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                  · simpa [dependenciesFound, Effects.boolean] using grounded_returns program _ state (.bool false)
              | some dependencies =>
                  let dependencyCaller := ("dependencies", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies)) :: selected
                  apply branch_returns program selected dependencyCaller state _
                    (encoded (encodeOption (encodeList InferenceCettaWire.AuthoredRule.typeTerm) (some dependencies)))
                    dependenciesCases depthBody _
                  · simpa only [dependenciesFound] using dependenciesReturned
                  · simp [dependenciesCases, dependencyCaller, selected, caller, callee, Helper.names, encodeOption,
                      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
                  · have depthReturned := lower.depth dependencyCaller state rule row.site row.path
                      (v "rule") (v "site") (v "path")
                      (by simp [dependencyCaller, selected, caller, callee, Helper.names, applySubst, Subst.lookup])
                    unfold depthBody
                    cases depthFound : occurrenceDepthAtSite? rule row.site row.path with
                    | none =>
                        apply branch_returns program dependencyCaller (("missingDepth", .symbol "None") :: dependencyCaller)
                          state _ (.symbol "None") depthCases (Effects.boolean false) _
                        · simpa [depthFound, encodeOption, CettaWireAtom.encode] using depthReturned
                        · simp [depthCases, dependencyCaller, selected, caller, callee, Helper.names,
                            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                        · simpa [dependenciesFound, depthFound, Effects.boolean] using grounded_returns program _ state (.bool false)
                    | some depth =>
                        let depthCaller := ("depth", number depth) :: dependencyCaller
                        let arityCaller := ("arity", number row.arguments.length) :: depthCaller
                        let final := ("expected", number dependencies.length) :: arityCaller
                        apply branch_returns program dependencyCaller depthCaller state _
                          (encoded (encodeOption Term.natural (some depth))) depthCases lengthBody _
                        · simpa only [depthFound] using depthReturned
                        · simp [depthCases, depthCaller, dependencyCaller, selected, caller, callee, Helper.names, encodeOption,
                            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
                        · unfold lengthBody
                          apply PureData.let_bindings_return (pairs := [
                            (v "arity", a "gslt:automata:length" [v "arguments"]),
                            (v "expected", a "gslt:automata:length" [v "dependencies"])])
                            (final := final) (middle := state) _ state arityBody _ _
                          · apply PureData.BindingsReturn.cons (bound := arityCaller) (middle := state)
                              (value := number row.arguments.length)
                            · exact admission_length_encoded_returns program lower InferenceCettaWire.encodePattern depthCaller state
                                row.arguments (v "arguments")
                                (by simp [depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                  patternsValue, patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList,
                                  applySubst, Subst.lookup])
                            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names, Subst.lookup]
                            · apply PureData.BindingsReturn.cons (bound := final) (middle := state) (value := number dependencies.length)
                              · exact admission_length_encoded_returns program lower InferenceCettaWire.AuthoredRule.typeTerm arityCaller state
                                  dependencies (v "dependencies")
                                  (by simp [arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                    applySubst, Subst.lookup])
                              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                  final, arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names, Subst.lookup]
                              · exact .nil _ _
                          · have compared := CettaWireAtom.equality_captured_returns program final state
                              (.natural row.arguments.length) (.natural dependencies.length) "arity" "expected"
                              (by simp [final, arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                applySubst, Subst.lookup])
                              (by simp [final, arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                applySubst, Subst.lookup])
                            have tested : PureReturns program final state (a "==" [v "arity", v "expected"]) state
                                (Effects.boolean (row.arguments.length == dependencies.length)) := by
                              simpa only [Term.natural.injEq, beq_eq_decide] using compared
                            unfold arityBody
                            apply bool_if_returns program final state _ (row.arguments.length == dependencies.length) _ _ _ tested
                            cases sameLength : row.arguments.length == dependencies.length with
                            | false =>
                                simpa [dependenciesFound, depthFound, sameLength, Effects.boolean] using
                                  grounded_returns program final state (.bool false)
                            | true =>
                                unfold groundBody
                                apply bool_if_returns program final state _ (Pattern.isGroundListAt depth row.arguments) _ _ _
                                · exact lower.ground final state depth row.arguments (v "depth") (v "arguments")
                                    (by simp [final, arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                      applySubst, Subst.lookup])
                                · cases ground : Pattern.isGroundListAt depth row.arguments with
                                  | false =>
                                      simpa [dependenciesFound, depthFound, sameLength, ← ground_list_eq_all, ground, Effects.boolean] using
                                        grounded_returns program final state (.bool false)
                                  | true =>
                                      simpa [dependenciesFound, depthFound, sameLength, ← ground_list_eq_all, ground] using
                                        helper_capture program agreement .occurrences final state _ _ _ rfl
                                          (by simp [final, arityCaller, depthCaller, dependencyCaller, selected, caller, callee, Helper.names,
                                            applySubst, Subst.lookup]) ih

theorem admission_occurrences_original_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : AdmissionOperations program)
    (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (rows : List MetavariableOccurrence) :
    PureReturns program [] state (a Helper.occurrences.head [ruleValue rule,
      encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
      encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)]) state
      (Effects.boolean (rows.all (fun row => occurrenceDeclared rule row &&
        match dependencies? spec row.name, occurrenceDepthAtSite? rule row.site row.path with
        | some dependencies, some depth => row.arguments.length == dependencies.length &&
            row.arguments.all (fun argument => argument.isGroundAt depth)
        | _, _ => false))) := by
  exact admission_occurrences_returns program agreement lower state rule spec rows

#print axioms admission_length_encoded_returns
#print axioms ground_list_eq_all
#print axioms admission_occurrences_returns
#print axioms admission_occurrences_original_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number stringValue

theorem inference_list_wire {α : Type} (encoder : α → Term) (values : List α) :
    InferenceCettaWire.encodeList encoder values = encodeList encoder values := by
  rfl

private def coveredBody : Atom := a "if" [a Helper.contextCovered.head [v "contextKeys", v "dependencyKeys"],
  a Helper.occurrences.head [v "rule", v "spec", v "occurrences"], Effects.boolean false]
private def countBody : Atom := a "if" [a "==" [v "contextCount", v "dependencyCount"], coveredBody, Effects.boolean false]
private def countsBody : Atom := a "let*" [.expression [
  .expression [v "contextCount", a "gslt:automata:length" [v "context"]],
  .expression [v "dependencyCount", a "gslt:automata:length" [v "dependencies"]]], countBody]
private def occurrenceNodupBody : Atom := a "if" [a Helper.nodup.head [v "occurrenceKeys"], countsBody, Effects.boolean false]
private def dependencyNodupBody : Atom := a "if" [a Helper.nodup.head [v "dependencyKeys"], occurrenceNodupBody, Effects.boolean false]
private def contextNodupBody : Atom := a "if" [a Helper.nodup.head [v "contextKeys"], dependencyNodupBody, Effects.boolean false]
private def keysBody : Atom := a "let*" [.expression [
  .expression [v "contextKeys", a Helper.keys.head [v "context"]],
  .expression [v "dependencyKeys", a Helper.keys.head [v "dependencies"]],
  .expression [v "occurrenceKeys", a Helper.occurrenceKeys.head [v "occurrences"]]], contextNodupBody]
private def specCases : SpaceSemantics.Cases :=
  [(a "RuleBindingSpec" [v "dependencies", v "occurrences"], keysBody), (v "badSpec", Effects.boolean false)]
private def specBody : Atom := caseData (v "spec") specCases
private def ruleCases : SpaceSemantics.Cases :=
  [(a "ScopedRewriteRuleV1" [v "label", v "context", v "premises", v "left", v "right", v "bindings"], specBody),
    (v "badRule", Effects.boolean false)]
private theorem admitted_shape : (equation .admitted).body = caseData (v "rule") ruleCases := by decide +kernel

theorem binding_admitted_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (lower : AdmissionOperations program) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) :
    PureReturns program [] state (a Helper.admitted.head [ruleValue rule,
      encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) state (Effects.boolean (admittedFor rule spec)) := by
  let caller := callee .admitted [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]
  let ruleCaller := [("bindings", encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)),
    ("right", patternValue rule.right), ("left", patternValue rule.left),
    ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)),
    ("context", encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)),
    ("label", stringValue rule.name)] ++ caller
  let specCaller := [("occurrences", encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm spec.occurrences)),
    ("dependencies", encoded (encodeList InferenceCettaWire.AuthoredRule.dependencyTerm spec.dependencies))] ++ ruleCaller
  let contextKeys := ("contextKeys", encoded (encodeList Term.string (rule.typeContext.map Prod.fst))) :: specCaller
  let dependencyKeys := ("dependencyKeys", encoded (encodeList Term.string (spec.dependencies.map Prod.fst))) :: contextKeys
  let final := ("occurrenceKeys", encoded (encodeList occurrenceKeyTerm spec.occurrences)) :: dependencyKeys
  apply helper_call program agreement .admitted [] state _ _ _ rfl (captured_closed _)
  rw [admitted_shape]
  apply branch_returns program caller ruleCaller state _ (ruleValue rule) ruleCases specBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "rule"
  · simp [ruleCases, ruleValue, ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
      inference_list_wire, patternValue, patternValue, ruleCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold specBody
    apply branch_returns program ruleCaller specCaller state _
      (encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)) specCases keysBody _
    · simpa [ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program ruleCaller state "spec"
    · simp [specCases, InferenceCettaWire.AuthoredRule.bindingSpecTerm, inference_list_wire,
        specCaller, ruleCaller, caller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · unfold keysBody
      apply PureData.let_bindings_return (pairs := [
        (v "contextKeys", a Helper.keys.head [v "context"]),
        (v "dependencyKeys", a Helper.keys.head [v "dependencies"]),
        (v "occurrenceKeys", a Helper.occurrenceKeys.head [v "occurrences"])])
        (final := final) (middle := state) _ state contextNodupBody _ _
      · apply PureData.BindingsReturn.cons (bound := contextKeys) (middle := state)
          (value := encoded (encodeList Term.string (rule.typeContext.map Prod.fst)))
        · exact helper_capture program agreement .keys specCaller state _ _ _ rfl
            (by simp [specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
            (admission_context_keys_returns program agreement state rule.typeContext)
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := dependencyKeys) (middle := state)
            (value := encoded (encodeList Term.string (spec.dependencies.map Prod.fst)))
          · exact helper_capture program agreement .keys contextKeys state _ _ _ rfl
              (by simp [contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
              (admission_dependency_keys_returns program agreement state spec.dependencies)
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
              (value := encoded (encodeList occurrenceKeyTerm spec.occurrences))
            · exact helper_capture program agreement .occurrenceKeys dependencyKeys state _ _ _ rfl
                (by simp [dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
                (admission_occurrence_keys_returns program agreement state spec.occurrences)
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, Subst.lookup]
            · exact .nil _ _
      · unfold contextNodupBody
        apply bool_if_returns program final state _ (decide (rule.typeContext.map Prod.fst).Nodup) _ _ _
        · exact helper_capture program agreement .nodup final state _ _ _ rfl
            (by simp [final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
            (admission_string_nodup_returns program agreement lower.member state (rule.typeContext.map Prod.fst))
        · cases contextUnique : decide (rule.typeContext.map Prod.fst).Nodup with
          | false => simpa [admittedFor, contextUnique, Effects.boolean] using grounded_returns program final state (.bool false)
          | true =>
              unfold dependencyNodupBody
              apply bool_if_returns program final state _ (decide (spec.dependencies.map Prod.fst).Nodup) _ _ _
              · exact helper_capture program agreement .nodup final state _ _ _ rfl
                  (by simp [final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
                  (admission_string_nodup_returns program agreement lower.member state (spec.dependencies.map Prod.fst))
              · cases dependenciesUnique : decide (spec.dependencies.map Prod.fst).Nodup with
                | false => simpa [admittedFor, contextUnique, dependenciesUnique, Effects.boolean] using grounded_returns program final state (.bool false)
                | true =>
                    unfold occurrenceNodupBody
                    apply bool_if_returns program final state _
                      (decide (spec.occurrences.map fun row => (row.name, row.site, row.path)).Nodup) _ _ _
                    · exact helper_capture program agreement .nodup final state _ _ _ rfl
                        (by simp [final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
                        (admission_occurrence_nodup_returns program agreement lower.member state spec.occurrences)
                    · cases occurrencesUnique : decide (spec.occurrences.map fun row => (row.name, row.site, row.path)).Nodup with
                      | false => simpa [admittedFor, contextUnique, dependenciesUnique, occurrencesUnique, Effects.boolean] using
                          grounded_returns program final state (.bool false)
                      | true =>
                          let counted := ("contextCount", number rule.typeContext.length) :: final
                          let compared := ("dependencyCount", number spec.dependencies.length) :: counted
                          unfold countsBody
                          apply PureData.let_bindings_return (pairs := [
                            (v "contextCount", a "gslt:automata:length" [v "context"]),
                            (v "dependencyCount", a "gslt:automata:length" [v "dependencies"])])
                            (final := compared) (middle := state) _ state countBody _ _
                          · apply PureData.BindingsReturn.cons (bound := counted) (middle := state)
                              (value := number rule.typeContext.length)
                            · exact admission_length_encoded_returns program lower InferenceCettaWire.AuthoredRule.typeBindingTerm final state
                                rule.typeContext (v "context")
                                (by simp [final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
                            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, Subst.lookup]
                            · apply PureData.BindingsReturn.cons (bound := compared) (middle := state)
                                (value := number spec.dependencies.length)
                              · exact admission_length_encoded_returns program lower InferenceCettaWire.AuthoredRule.dependencyTerm counted state
                                  spec.dependencies (v "dependencies")
                                  (by simp [counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names,
                                    applySubst, Subst.lookup])
                              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                                  compared, counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names, Subst.lookup]
                              · exact .nil _ _
                          · have tested := CettaWireAtom.equality_captured_returns program compared state
                              (.natural rule.typeContext.length) (.natural spec.dependencies.length) "contextCount" "dependencyCount"
                              (by simp [compared, counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names,
                                applySubst, Subst.lookup])
                              (by simp [compared, counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names,
                                applySubst, Subst.lookup])
                            have lengthsChecked : PureReturns program compared state (a "==" [v "contextCount", v "dependencyCount"]) state
                                (Effects.boolean (rule.typeContext.length == spec.dependencies.length)) := by
                              simpa only [Term.natural.injEq, beq_eq_decide] using tested
                            unfold countBody
                            apply bool_if_returns program compared state _ (rule.typeContext.length == spec.dependencies.length) _ _ _ lengthsChecked
                            cases lengthsEqual : rule.typeContext.length == spec.dependencies.length with
                            | false => simpa [admittedFor, contextUnique, dependenciesUnique, occurrencesUnique, lengthsEqual, Effects.boolean] using
                                grounded_returns program compared state (.bool false)
                            | true =>
                                have covered := helper_capture program agreement .contextCovered compared state
                                  [v "contextKeys", v "dependencyKeys"] _ _ rfl
                                  (by simp [compared, counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names,
                                    applySubst, Subst.lookup])
                                  (admission_names_covered_returns program agreement lower.member state
                                    (rule.typeContext.map Prod.fst) (spec.dependencies.map Prod.fst))
                                rw [context_coverage_value] at covered
                                unfold coveredBody
                                apply bool_if_returns program compared state _
                                  (rule.typeContext.all (fun entry => spec.dependencies.any (fun declared => declared.1 == entry.1))) _ _ _ covered
                                cases coverage : rule.typeContext.all (fun entry => spec.dependencies.any (fun declared => declared.1 == entry.1)) with
                                | false => simpa [admittedFor, contextUnique, dependenciesUnique, occurrencesUnique, lengthsEqual, coverage, Effects.boolean] using
                                    grounded_returns program compared state (.bool false)
                                | true =>
                                    simp only [admittedFor, contextUnique, dependenciesUnique, occurrencesUnique, lengthsEqual, coverage,
                                      Bool.true_and, ↓reduceIte]
                                    exact helper_capture program agreement .occurrences compared state _ _ _ rfl
                                      (by simp [compared, counted, final, dependencyKeys, contextKeys, specCaller, ruleCaller, caller, callee, Helper.names,
                                        applySubst, Subst.lookup])
                                      (admission_occurrences_original_returns program agreement lower state rule spec spec.occurrences)

theorem binding_admitted_captured_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (lower : AdmissionOperations program) (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) :
    PureReturns program caller state (a Helper.admitted.head [one, two]) state (Effects.boolean (admittedFor rule spec)) :=
  helper_capture program agreement .admitted caller state _ _ _ rfl captured
    (binding_admitted_returns program agreement lower state rule spec)

#print axioms inference_list_wire
#print axioms binding_admitted_returns
#print axioms binding_admitted_captured_returns

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

attribute [local simp] a v encoded number stringValue

private def queryReasonsData : Atom := a "LCons" [a "PremiseQueryObligation" [v "reason"], v "tail"]
private def queryReasonsCons : Atom := a "let" [v "tail", a Helper.queryObligations.head [v "rest"], queryReasonsData]
private def queryReasonsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [v "reason", v "rest"], queryReasonsCons), (v "badReasons", .symbol "None")]
private theorem query_reasons_shape : (equation .queryObligations).body = caseData (v "reasons") queryReasonsCases := by
  decide +kernel

theorem query_obligations_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (reasons : List Query.Obligation) :
    PureReturns program [] state (a Helper.queryObligations.head
      [encoded (encodeList queryObligationTerm reasons)]) state
      (encoded (encodeList obligationTerm (reasons.map Execution.Obligation.query))) := by
  induction reasons with
  | nil =>
      let caller := callee .queryObligations [encoded (encodeList queryObligationTerm [])]
      apply helper_call program agreement .queryObligations [] state _ _ _ rfl (captured_closed _)
      rw [query_reasons_shape]
      apply branch_returns program caller caller state _ (.symbol "LNil") queryReasonsCases (.symbol "LNil") _
      · simpa [caller, callee, Helper.names, encodeList, applySubst, Subst.lookup,
          CettaWireAtom.encode] using variable_returns program caller state "reasons"
      · simp [queryReasonsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons reason reasons ih =>
      let caller := callee .queryObligations [encoded (encodeList queryObligationTerm (reason :: reasons))]
      let selected := [("rest", encoded (encodeList queryObligationTerm reasons)), ("reason", encoded (queryObligationTerm reason))] ++ caller
      let final := ("tail", encoded (encodeList obligationTerm (reasons.map Execution.Obligation.query))) :: selected
      apply helper_call program agreement .queryObligations [] state _ _ _ rfl (captured_closed _)
      rw [query_reasons_shape]
      apply branch_returns program caller selected state _
        (encoded (encodeList queryObligationTerm (reason :: reasons))) queryReasonsCases queryReasonsCons _
      · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "reasons"
      · simp [queryReasonsCases, selected, caller, callee, Helper.names, encodeList,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · unfold queryReasonsCons
        apply named_let_returns program selected state "tail" _
          (encoded (encodeList obligationTerm (reasons.map Execution.Obligation.query))) queryReasonsData _
        · simp [selected, caller, callee, Helper.names, Subst.lookup]
        · exact helper_capture program agreement .queryObligations selected state _ _ _ rfl
            (by simp [selected, caller, callee, Helper.names, applySubst, Subst.lookup]) ih
        · have templated : PureData.Template program queryReasonsData := by
            apply data_template program agreement "LCons" _ (by decide)
            intro child member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · apply data_template program agreement "PremiseQueryObligation" _ (by decide)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              subst child
              exact .captured _
            · exact .captured _
          simpa [queryReasonsData, obligationTerm, encodeList, final, selected, caller, callee, Helper.names,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program final state _ templated

theorem query_obligations_captured_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (caller : Subst) (state : State)
    (reasons : List Query.Obligation) (input : Atom)
    (captured : applySubst caller input = encoded (encodeList queryObligationTerm reasons)) :
    PureReturns program caller state (a Helper.queryObligations.head [input]) state
      (encoded (encodeList obligationTerm (reasons.map Execution.Obligation.query))) := by
  apply helper_capture program agreement .queryObligations caller state _ _ _ rfl _
    (query_obligations_returns program agreement state reasons)
  simpa only [List.map_cons, List.map_nil] using congrArg (fun value => [value]) captured

#print axioms query_obligations_returns
#print axioms query_obligations_captured_returns

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

namespace RootFrame

def lookupCases : SpaceSemantics.Cases := sourceCases (goalBody 1)
def foundBody : Atom := ((lookupCases[1]?).map Prod.snd).getD (.symbol "None")
def ruleCases : SpaceSemantics.Cases := sourceCases foundBody
def ruleBody : Atom := ((ruleCases[0]?).map Prod.snd).getD (.symbol "None")
def specificationCases : SpaceSemantics.Cases := sourceCases ruleBody
def admittedBody : Atom := ((specificationCases[1]?).map Prod.snd).getD (.symbol "None")

def refusedData (head : String) : Atom := a "Some" [a "PremiseExpansion"
  [.symbol "LNil", .symbol "LNil", a "LCons" [a head [v "index"], .symbol "LNil"]]]
def rootPairs : List (Atom × Atom) :=
  [(v "ambient", a "gslt:automata:length" [v "bound"]),
   (v "query", a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", .symbol "RuleLeft",
     .symbol "LNil", number 0, .symbol "LNil", v "left", v "source"]),
   (v "matcher", a "gslt:rule:scope-matcher-start" [v "query"])]
def rootData : Atom := a "Some" [a "PremiseExpansion"
  [a "LCons" [a "PremiseRootMatch" [v "bound", v "type", v "source", v "index", v "rule", v "spec",
    v "matcher", number 0, v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def acceptedBody : Atom := a "let*"
  [.expression (rootPairs.map fun pair => .expression [pair.1, pair.2]), rootData]

theorem lookup_shape : goalBody 1 = caseData (a "gslt:rule:row-at" [v "index", v "rewrites"]) lookupCases := by
  decide +kernel
theorem lookup_cases_syntax : lookupCases =
    [(.symbol "None", refusedData "PremiseRuleUnavailable"),
     (a "Some" [v "rule"], foundBody), (v "badLookup", .symbol "None")] := by decide +kernel
theorem found_shape : foundBody = caseData (v "rule") ruleCases := by decide +kernel
theorem rule_cases_syntax : ruleCases =
    [(a "ScopedRewriteRuleV1" [v "ruleName", v "ruleTypes", v "premises", v "left", v "right", v "bindings"], ruleBody),
     (v "badRule", .symbol "None")] := by decide +kernel
theorem rule_shape : ruleBody =
    caseData (a "gslt:premise:specification" [v "index", v "specifications"]) specificationCases := by decide +kernel
theorem specification_cases_syntax : specificationCases =
    [(.symbol "None", refusedData "PremiseBindingUnavailable"),
     (a "Some" [v "spec"], admittedBody), (v "badSpec", .symbol "None")] := by decide +kernel
theorem admitted_shape : admittedBody = a "if" [a "gslt:premise:binding-admitted" [v "rule", v "spec"],
    a "if" [a "gslt:premise:open-well-sorted" [v "declarations", v "free", v "bound", v "type", v "source"],
      acceptedBody, refusedData "PremiseSourceRejected"], refusedData "PremiseBindingRejected"] := by decide +kernel

def rootCaller (environment : Environment) (outer : Execution.Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("index", number index), ("source", encoded (InferenceCettaWire.encodePattern source)),
   ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)),
   ("bound", boundValue bound)] ++
    goalCaller environment outer (.root bound type source index) tail free

theorem root_goal_selected (environment : Environment) (outer : Execution.Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (goalCaller environment outer (.root bound type source index) tail free)
      (goalValue (.root bound type source index)) goalCases =
      some (rootCaller environment outer bound type source index tail free, goalBody 1) := by
  rw [goal_cases_syntax]
  simp [goalValue, goalTerm, rootCaller, goalCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem evaluate_root_body_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns program (rootCaller environment outer bound type source index tail free)
      state (goalBody 1) state answer) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.root bound type source index), continuationValue tail]) state answer :=
  evaluate_branch_returns program agreement state environment outer _ tail free _ _ _
    (root_goal_selected environment outer bound type source index tail free) returned

#print axioms lookup_shape
#print axioms admitted_shape
#print axioms root_goal_selected
#print axioms evaluate_root_body_returns

end RootFrame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Tasks

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open SpaceSemantics (Program)
open Eval

theorem evaluate_shape : taskBody 0 = a Helper.evaluate.head [v "environment", v "goal", v "continuation"] := by decide +kernel
theorem deliver_shape : taskBody 1 = a Helper.deliver.head [v "environment", v "result", v "continuation"] := by decide +kernel
theorem root_shape : taskBody 3 = a "gslt:premise:root-match-expand-in" [v "environment", v "task"] := by decide +kernel
theorem target_shape : taskBody 4 = a "gslt:premise:target-match-expand-in" [v "environment", v "task"] := by decide +kernel
theorem scan_shape : taskBody 5 = a "gslt:premise:machine-expand" [v "declarations", v "free", v "task"] := by decide +kernel

def evaluateCaller (environment : Environment) (outer goal : Execution.Goal)
    (tail : Execution.Continuation environment goal outer) (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue tail), ("goal", goalValue goal)] ++ taskCaller environment (.evaluate goal tail) free

def deliverCaller (environment : Environment) (outer goal : Execution.Goal) (result : Execution.Result environment goal)
    (tail : Execution.Continuation environment goal outer) (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue tail), ("result", resultValue result)] ++ taskCaller environment (.deliver result tail) free

def rootCaller (environment : Environment) (outer : Execution.Goal) (frame : Execution.RootMatchFrame environment outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue frame.tail), ("cursor", number frame.cursor), ("matcher", encoded (matcherStateTerm frame.state)),
    ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm frame.spec)), ("rule", ruleValue frame.rule),
    ("index", number frame.index), ("source", patternValue frame.source),
    ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm frame.type)), ("bound", boundValue frame.bound)] ++
    taskCaller environment (.rootMatch frame) free

def targetCaller (environment : Environment) (outer : Execution.Goal) (frame : Execution.TargetMatchFrame environment outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue frame.tail), ("cursor", number frame.cursor), ("matcher", encoded (matcherStateTerm frame.state)),
    ("target", patternValue frame.target), ("history", encoded (eventsTerm frame.history)),
    ("completed", assignmentValue frame.completed), ("captured", assignmentValue frame.captured),
    ("trace", encoded (traceTerm frame.trace)), ("index", number frame.index), ("call", encoded (stepCallTerm frame.call))] ++
    taskCaller environment (.targetMatch frame) free

def scanCaller (environment : Environment) (outer : Execution.Goal) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (limit cursor : Nat) (tail : Execution.Continuation environment (.steps bound type source limit) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue tail), ("cursor", number cursor), ("limit", number limit),
    ("source", patternValue source), ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm type)), ("bound", boundValue bound)] ++
    taskCaller environment (.scanChildren bound type source limit cursor tail) free

theorem evaluate_selected (environment : Environment) (outer goal : Execution.Goal)
    (tail : Execution.Continuation environment goal outer) (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.evaluate goal tail) free) (taskValue (.evaluate goal tail)) taskCases =
      some (evaluateCaller environment outer goal tail free, taskBody 0) := by
  simp [task_cases_syntax, taskValue, taskTerm, evaluateCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem deliver_selected (environment : Environment) (outer goal : Execution.Goal) (result : Execution.Result environment goal)
    (tail : Execution.Continuation environment goal outer) (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.deliver result tail) free) (taskValue (.deliver result tail)) taskCases =
      some (deliverCaller environment outer goal result tail free, taskBody 1) := by
  simp [task_cases_syntax, taskValue, taskTerm, deliverCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem root_selected (environment : Environment) (outer : Execution.Goal) (frame : Execution.RootMatchFrame environment outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.rootMatch frame) free) (taskValue (.rootMatch frame)) taskCases =
      some (rootCaller environment outer frame free, taskBody 3) := by
  simp [task_cases_syntax, taskValue, taskTerm, rootCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem target_selected (environment : Environment) (outer : Execution.Goal) (frame : Execution.TargetMatchFrame environment outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.targetMatch frame) free) (taskValue (.targetMatch frame)) taskCases =
      some (targetCaller environment outer frame free, taskBody 4) := by
  simp [task_cases_syntax, taskValue, taskTerm, targetCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem scan_selected (environment : Environment) (outer : Execution.Goal) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (limit cursor : Nat) (tail : Execution.Continuation environment (.steps bound type source limit) outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.scanChildren bound type source limit cursor tail) free)
      (taskValue (.scanChildren bound type source limit cursor tail)) taskCases =
      some (scanCaller environment outer bound type source limit cursor tail free, taskBody 5) := by
  simp [task_cases_syntax, taskValue, taskTerm, scanCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

#print axioms evaluate_selected
#print axioms deliver_selected
#print axioms root_selected
#print axioms target_selected
#print axioms scan_selected

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Tasks

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Eval Effects

def memberHeadNames : List String :=
  ["==",
   "LCons",
   "LNil",
   "case",
   "gslt:automata:member",
   "if",
   "let"]

def memberHeads (head : String) : Bool := memberHeadNames.contains head

def metadataHeadNames : List String :=
  ["+",
   "-",
   "<",
   "==",
   "Congruence",
   "FVar",
   "ForAll",
   "Freshness",
   "LCons",
   "LNil",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "RSome",
   "RelationQuery",
   "RuleBindingSpec",
   "RuleDependency",
   "RuleLeft",
   "RuleOccurrence",
   "RulePremise",
   "RuleRight",
   "ScopedRewriteRuleV1",
   "ScopedStep",
   "Some",
   "case",
   "gslt:automata:length",
   "gslt:rule:row-at",
   "gslt:rule:scope-metadata-dependencies",
   "gslt:rule:scope-metadata-dependency-rows",
   "gslt:rule:scope-metadata-occurrence-declared",
   "gslt:rule:scope-metadata-occurrence-depth",
   "gslt:rule:scope-metadata-occurrence-depth-at-site",
   "gslt:rule:scope-metadata-occurrence-name",
   "gslt:rule:scope-metadata-premise-depth",
   "gslt:rule:scope-metadata-premise-pattern",
   "gslt:rule:scope-metadata-quantified-body",
   "gslt:rule:scope-metadata-site-depth",
   "gslt:rule:scope-metadata-site-pattern",
   "gslt:rule:scope-metadata-site-premise",
   "if",
   "let"]

def metadataHeads (head : String) : Bool := metadataHeadNames.contains head

def groundHeadNames : List String :=
  ["+",
   "<",
   "FVar",
   "LCons",
   "LNil",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "RNone",
   "Var",
   "case",
   "gslt:premise:ground-at",
   "gslt:premise:ground-list-at",
   "if",
   "let"]

def groundHeads (head : String) : Bool := groundHeadNames.contains head

theorem member_closed : ProgramClosed memberHeads MatchAutomataProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : MatchAutomataProgram.program.equations.all (fun equation =>
        !memberHeads equation.head || codeWithin memberHeads equation.body) = true := by
      rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem member_retained_equations :
    MatchAutomataProgram.program.equations.filter (fun equation => memberHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => memberHeads equation.head) := by
  rfl

theorem member_retained_declarations :
    MatchAutomataProgram.program.declarations.filter (retainedCallDeclaration memberHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration memberHeads) := by
  rfl

theorem member_agreement : ProgramAgreementOn memberHeads MatchAutomataProgram.program RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ member_retained_equations member_retained_declarations

theorem metadata_closed : ProgramClosed metadataHeads RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !metadataHeads equation.head || codeWithin metadataHeads equation.body) = true := by
      rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem metadata_retained_equations :
    RuleExecutionProgram.program.equations.filter (fun equation => metadataHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => metadataHeads equation.head) := by
  rfl

theorem metadata_retained_declarations :
    RuleExecutionProgram.program.declarations.filter (retainedCallDeclaration metadataHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration metadataHeads) := by
  rfl

theorem metadata_agreement : ProgramAgreementOn metadataHeads RuleExecutionProgram.program RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ metadata_retained_equations metadata_retained_declarations

theorem ground_closed : ProgramClosed groundHeads premiseRuntimeProgram := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : premiseRuntimeProgram.equations.all (fun equation =>
        !groundHeads equation.head || codeWithin groundHeads equation.body) = true := by
      rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem ground_retained_equations :
    premiseRuntimeProgram.equations.filter (fun equation => groundHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => groundHeads equation.head) := by
  rfl

theorem ground_retained_declarations :
    premiseRuntimeProgram.declarations.filter (retainedCallDeclaration groundHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration groundHeads) := by
  rfl

theorem ground_agreement : ProgramAgreementOn groundHeads premiseRuntimeProgram RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ ground_retained_equations ground_retained_declarations

#print axioms member_closed
#print axioms member_retained_equations
#print axioms member_retained_declarations
#print axioms member_agreement
#print axioms metadata_closed
#print axioms metadata_retained_equations
#print axioms metadata_retained_declarations
#print axioms metadata_agreement
#print axioms ground_closed
#print axioms ground_retained_equations
#print axioms ground_retained_declarations
#print axioms ground_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval EnvironmentExecution

private abbrev specValue (spec : RuleBindingSpec) : Atom := encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)

abbrev stringValue (name : String) : Atom := encoded (.string name)
abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

private theorem raw_admitted (program : Program) (head : String) (arguments : List Atom)
    (checked : (List.range arguments.length).all (fun index => argumentIsRaw program head index) = true) :
    ∀ offset argument, arguments[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true := by
  intro offset argument selected
  obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp selected
  exact Or.inl (List.all_eq_true.mp checked offset (List.mem_range.mpr bounded))

theorem member_returns (caller : Subst) (state : State) (key : Term) (keys : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded key, encoded (encodeList id keys)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:member" [one, two]) state
      (Effects.boolean (decide (key ∈ keys))) := by
  let aliases : Subst := [("key", encoded key), ("keys", encoded (encodeList id keys))]
  have concrete : PureReturns RuleExecutionProgram.scopedMachineProgram [] state
      (a "gslt:automata:member" [encoded key, encoded (encodeList id keys)]) state
      (Effects.boolean (decide (key ∈ keys))) := by
    apply captured_call_in_extension member_closed member_agreement [] aliases state state
      "gslt:automata:member" [encoded key, encoded (encodeList id keys)] ["key", "keys"] _
      (by decide) (by decide) (by decide +kernel) (by decide)
    · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
    · simp [aliases, applySubst, Subst.lookup]
    · exact MatchAutomataSourceExecution.member_returns state key keys
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram [] caller state state "gslt:automata:member"
    [encoded key, encoded (encodeList id keys)] [one, two] _
    (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa using captured.symm
  · exact concrete

theorem length_returns (caller : Subst) (state : State) (values : List Term) (input : Atom)
    (captured : applySubst caller input = encoded (encodeList id values)) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:length" [input]) state (number values.length) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.length_returns caller state values input captured

theorem declared_returns (caller : Subst) (state : State) (rule : RewriteRule) (row : MetavariableOccurrence)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm row)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-metadata-occurrence-declared" [one, two]) state
      (Effects.boolean (occurrenceDeclared rule row)) := by
  let aliases : Subst := [("rule", ruleValue rule), ("row", encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm row))]
  apply captured_call_in_extension metadata_closed metadata_agreement caller aliases state state
    "gslt:rule:scope-metadata-occurrence-declared" [one, two] ["rule", "row"] _
    (by decide) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured
  · exact RuleInstantiationExecution.ScopedMetadata.occurrence_declared_captured_returns caller state rule row one two captured

theorem dependencies_returns (caller : Subst) (state : State) (spec : RuleBindingSpec) (name : String)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), stringValue name]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-metadata-dependencies" [one, two]) state
      (encoded (encodeOption (encodeList InferenceCettaWire.AuthoredRule.typeTerm) (dependencies? spec name))) := by
  let aliases : Subst := [("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)), ("name", stringValue name)]
  apply captured_call_in_extension metadata_closed metadata_agreement caller aliases state state
    "gslt:rule:scope-metadata-dependencies" [one, two] ["spec", "name"] _
    (by decide) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured
  · have returned := RuleInstantiationExecution.ScopedMetadata.dependencies_captured_returns caller state spec name one two captured
    cases found : dependencies? spec name <;>
      simpa only [found, RuleInstantiationExecution.ScopedMetadata.dependencyOptionTerm, encodeOption] using returned

theorem depth_returns (caller : Subst) (state : State) (rule : RewriteRule) (site : RulePatternSite)
    (path : List Nat) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.siteTerm site),
        encoded (InferenceCettaWire.encodeList Term.natural path)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:rule:scope-metadata-occurrence-depth-at-site" [one, two, three]) state
      (encoded (encodeOption Term.natural (occurrenceDepthAtSite? rule site path))) := by
  let aliases : Subst := [("rule", ruleValue rule), ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm site)),
    ("path", encoded (InferenceCettaWire.encodeList Term.natural path))]
  apply captured_call_in_extension metadata_closed metadata_agreement caller aliases state state
    "gslt:rule:scope-metadata-occurrence-depth-at-site" [one, two, three] ["rule", "site", "path"] _
    (by decide) (by decide) (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured
  · have returned := RuleInstantiationExecution.ScopedMetadata.depth_at_site_captured_returns caller state rule site path
      one two three captured
    cases found : occurrenceDepthAtSite? rule site path <;>
      simpa only [found, RuleInstantiationExecution.ScopedCapture.naturalOptionTerm, encodeOption] using returned

theorem ground_returns (caller : Subst) (state : State) (depth : Nat) (arguments : List Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number depth, patternsValue arguments]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:ground-list-at" [one, two]) state
      (Effects.boolean (Pattern.isGroundListAt depth arguments)) := by
  let aliases : Subst := [("depth", number depth), ("arguments", patternsValue arguments)]
  have baseReturned := ground_list_at_captured_returns aliases state arguments depth (v "depth") (v "arguments")
    (by simp [aliases, patternsValue, applySubst, Subst.lookup])
  have elevated : PureReturns premiseRuntimeProgram aliases state
      (a "gslt:premise:ground-list-at" [v "depth", v "arguments"]) state
      (Effects.boolean (Pattern.isGroundListAt depth arguments)) :=
    premise_previous_returns (by decide +kernel) baseReturned
  have transported : PureReturns RuleExecutionProgram.scopedMachineProgram aliases state
      (a "gslt:premise:ground-list-at" [v "depth", v "arguments"]) state
      (Effects.boolean (Pattern.isGroundListAt depth arguments)) :=
    path_of_closed_agreement ground_closed ground_agreement
      ⟨by change codeWithin groundHeads (a "gslt:premise:ground-list-at" [v "depth", v "arguments"]) = true; decide, rfl⟩ elevated
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram aliases caller state state "gslt:premise:ground-list-at"
    [v "depth", v "arguments"] [one, two] _
    (by decide +kernel) (by decide)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · exact raw_admitted _ _ _ (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  · simpa [aliases, applySubst, Subst.lookup] using captured.symm
  · exact transported

#print axioms member_returns
#print axioms length_returns
#print axioms declared_returns
#print axioms dependencies_returns
#print axioms depth_returns
#print axioms ground_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower.Assembly

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem operations : EnvironmentExecution.AdmissionOperations RuleExecutionProgram.scopedMachineProgram where
  member := member_returns
  length := length_returns
  declared := declared_returns
  dependencies := dependencies_returns
  depth := depth_returns
  ground := ground_returns

theorem retained_equations :
    EnvironmentExecution.runtime.equations.filter (fun equation => EnvironmentExecution.ownedHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => EnvironmentExecution.ownedHeads equation.head) := by
  rfl

theorem retained_declarations :
    EnvironmentExecution.runtime.declarations.filter (retainedCallDeclaration EnvironmentExecution.ownedHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration EnvironmentExecution.ownedHeads) := by
  rfl

theorem agreement : ProgramAgreementOn EnvironmentExecution.ownedHeads EnvironmentExecution.runtime RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ retained_equations retained_declarations

theorem admitted_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state (EnvironmentExecution.a EnvironmentExecution.Helper.admitted.head
      [EnvironmentExecution.ruleValue rule, EnvironmentExecution.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) state
      (Effects.boolean (admittedFor rule spec)) :=
  EnvironmentExecution.binding_admitted_returns RuleExecutionProgram.scopedMachineProgram agreement operations state rule spec

theorem admitted_captured_returns (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [EnvironmentExecution.ruleValue rule, EnvironmentExecution.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (EnvironmentExecution.a "gslt:premise:binding-admitted" [one, two]) state
      (Effects.boolean (admittedFor rule spec)) := by
  apply captured_call_returns RuleExecutionProgram.scopedMachineProgram [] caller state state "gslt:premise:binding-admitted"
    [EnvironmentExecution.ruleValue rule, EnvironmentExecution.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)]
    [one, two] _ (by decide +kernel) (by decide)
  · intro index argument selected
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp selected
    exact Or.inl (EnvironmentExecution.helper_raw RuleExecutionProgram.scopedMachineProgram agreement .admitted index bounded)
  · intro index argument selected
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp selected
    exact Or.inl (EnvironmentExecution.helper_raw RuleExecutionProgram.scopedMachineProgram agreement .admitted index bounded)
  · simpa using captured.symm
  · exact admitted_returns state rule spec

theorem admitted_captured_completed_iff (caller : Subst) (state after : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [EnvironmentExecution.ruleValue rule, EnvironmentExecution.encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)])
    (answers input output : List Atom) :
    (∃ fuel, Eval.run RuleExecutionProgram.scopedMachineProgram fuel
      {state, control := .evaluate caller (EnvironmentExecution.a "gslt:premise:binding-admitted" [one, two])} =
      .complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (admittedFor rule spec)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (admitted_captured_returns caller state rule spec one two captured) after answers input output

#print axioms operations
#print axioms retained_equations
#print axioms retained_declarations
#print axioms agreement
#print axioms admitted_returns
#print axioms admitted_captured_returns
#print axioms admitted_captured_completed_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AdmissionLower.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Effects (State)
open Eval

def premiseContextCases : SpaceSemantics.Cases := sourceCases (goalBody 0)
def premiseContextBody : Atom := (premiseContextCases.head!).2
def premiseCases : SpaceSemantics.Cases := sourceCases premiseContextBody
def premiseBody (index : Nat) : Atom := ((premiseCases[index]?).map Prod.snd).getD (.symbol "None")

theorem premise_goal_shape : goalBody 0 = caseData (v "context") premiseContextCases := by decide +kernel
theorem premise_context_shape : premiseContextBody = caseData (v "premise") premiseCases := by decide +kernel
theorem premise_context_cases : premiseContextCases =
    [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premiseIndex", v "quantifiers"], premiseContextBody),
      (v "badContext", .symbol "None")] := by decide +kernel
theorem premise_cases : premiseCases =
    [(a "RelationQuery" [v "relation", v "arguments"], premiseBody 0),
      (a "Freshness" [v "name", v "subjectSchema"], premiseBody 1),
      (a "ForAll" [v "collection", v "parameter", v "body"], premiseBody 2),
      (a "Congruence" [v "sourceSchema", v "targetSchema"], premiseBody 3),
      (a "ScopedStep" [v "binders", v "type", v "sourceSchema", v "targetSchema"], premiseBody 4),
      (v "badPremise", .symbol "None")] := by decide +kernel

def premiseGoalCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (premise : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context premise initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("initial", assignmentValue initial), ("premise", encoded (InferenceCettaWire.AuthoredRule.premiseTerm premise)),
    ("context", contextValue context)] ++ goalCaller environment outer (.premise context premise initial) tail free

def premiseContextCaller (environment : Environment) (outer : Execution.Goal) (context : Context)
    (premise : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context premise initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("quantifiers", number context.quantifierDepth), ("premiseIndex", number context.premiseIndex),
    ("bound", boundValue context.bound), ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm context.spec)),
    ("rule", ruleValue context.rule), ("ruleIndex", number context.ruleIndex)] ++
    premiseGoalCaller environment outer context premise initial tail free

theorem evaluate_premise_body_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (context : Context)
    (premise : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context premise initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns program (premiseContextCaller environment outer context premise initial tail free)
      state premiseContextBody state answer) :
    PureReturns program [] state (a Helper.evaluate.head
      [environmentValue environment free, goalValue (.premise context premise initial), continuationValue tail]) state answer := by
  apply evaluate_branch_returns program agreement state environment outer (.premise context premise initial) tail free
    (premiseGoalCaller environment outer context premise initial tail free) (goalBody 0) answer
  · simp [goal_cases_syntax, goalValue, goalTerm, premiseGoalCaller, goalCaller,
      environmentCaller, callee, Helper.names, assignmentValue,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [premise_goal_shape]
    apply branch_returns program (premiseGoalCaller environment outer context premise initial tail free)
      (premiseContextCaller environment outer context premise initial tail free) state _ (contextValue context)
      premiseContextCases premiseContextBody answer
    · simpa [premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
        applySubst, Subst.lookup] using
        variable_returns program (premiseGoalCaller environment outer context premise initial tail free) state "context"
    · simp [premise_context_cases, contextValue, contextTerm,
        premiseContextCaller, premiseGoalCaller, goalCaller, environmentCaller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · exact returned

#print axioms premise_cases
#print axioms evaluate_premise_body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions
