import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseEnvironmentExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage

attribute [local simp]
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution.schedulerExpansionTerm
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution.schedulerStateTerm

/-!
# Native execution of original premise matching frames

Root and target matching suspend and resume the original scoped matcher. The
root-body and stepped continuations retain the original assignments, physical
choice histories, premise events and declaration positions. Finite context
coverage is obtained from actual original task trajectories.
-/

section MatchingSource
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames


def sourceProgram : SpaceSemantics.Program := RuleExecutionProgram.premiseMatchingProgram

theorem source_without_initializers : sourceProgram.initializers = [] := by decide +kernel

theorem source_heads_unique : (sourceProgram.equations.map (·.head)).Nodup := by decide +kernel


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingSource


section MatchingFramework
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
abbrev v (name : String) : Atom := .var name
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev number (value : Nat) : Atom := encoded (.natural value)
abbrev termListValue (values : List Term) : Atom := encoded (encodeList id values)
abbrev typeValue (type : TypeExpr) : Atom := encoded (InferenceCettaWire.AuthoredRule.typeTerm type)
abbrev boundValue (bound : List TypeExpr) : Atom :=
  encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
abbrev freeValue (free : List (String × TypeExpr)) : Atom :=
  encoded (DeclarationTyping.freeContextTerm free)
abbrev declarationsValue (language : LanguageDef) : Atom :=
  encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms)
abbrev ruleValue (rule : RewriteRule) : Atom := encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
abbrev specValue (spec : RuleBindingSpec) : Atom := encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)
abbrev assignmentValue (assignment : Assignment) : Atom :=
  encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)
abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
abbrev patternOptionValue (pattern : Option Pattern) : Atom :=
  encoded (encodeOption InferenceCettaWire.encodePattern pattern)
abbrev requestValue (request : GeneralScopedMatchMachine.Request) : Atom := encoded (matcherRequestTerm request)
abbrev matcherValue (state : GeneralScopedMatchMachine.State) : Atom := encoded (matcherStateTerm state)
abbrev reflectionValue (profile : Reflection.ReflectionProfile) : Atom := encoded (reflectionTerm profile)
abbrev selectionValue (profile : Reflection.ReflectionProfile) (rule : RewriteRule) : Atom :=
  encoded (encodeOption InferenceCettaWire.AuthoredRule.reflectivePresentationTerm
    (ReflectiveSubstitution.substitutionPresentationForRule? profile rule))

inductive Helper where | root | target | body | stepped
  deriving DecidableEq

def Helper.head : Helper → String
  | .root => "gslt:premise:root-match-expand-in"
  | .target => "gslt:premise:target-match-expand-in"
  | .body => "gslt:premise:root-body-deliver-in"
  | .stepped => "gslt:premise:stepped-deliver-in"

def Helper.names : Helper → List String
  | .root | .target => ["snapshot", "task"]
  | .body | .stepped => ["snapshot", "result", "continuation"]

def dataHeads : List String :=
  ["LCons", "None", "PremiseAnswer", "PremiseChildEvent", "PremiseContext", "PremiseDeliver",
   "PremiseEnvironment", "PremiseEvaluate", "PremiseExpansion", "PremiseGoal", "PremiseResult",
   "PremiseRootBody", "PremiseRootMatch", "PremiseStepCall", "PremiseStepped", "PremiseTargetMatch",
   "PremiseTargetProjection", "PremisesAnswer", "PremisesGoal", "RootAnswer", "RootGoal", "RulePremise",
   "ScopedMatcherAnswer", "ScopedMatcherRequest", "ScopedMatcherState", "ScopedRewriteRuleV1", "Some", "StepsAnswer"]

/-- Clause and demand agreement is needed only for the four authored entries,
their inert data constructors, and native arithmetic. Lower operations have
separate source realization contracts. -/
def ownedHeads (head : String) : Bool :=
  ([Helper.root.head, Helper.target.head, Helper.body.head, Helper.stepped.head, "+"] ++ dataHeads).contains head

def equation (helper : Helper) : SpaceSemantics.Equation :=
  (sourceProgram.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel)

def callEnvironment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

theorem helper_supported (helper : Helper) : ownedHeads helper.head = true := by cases helper <;> decide

theorem helper_clause (runtime : Program) (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime)
    (helper : Helper) (values : List Atom) (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (callEnvironment helper values) (equation helper).body] := by
  apply PureData.selected_clause_agreement agreement (helper_supported helper)
  exact PureData.named_equation_clause sourceProgram helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel) (by cases helper <;> decide) length

theorem helper_raw (runtime : Program) (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime)
    (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  rw [← agreement.demand helper.head index (helper_supported helper)]
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases small with rfl | rfl | rfl <;> first | omega | decide +kernel

theorem helper_call (runtime : Program) (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (callEnvironment helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (callEnvironment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide) _ _ _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw runtime agreement helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause runtime agreement helper values length

theorem data_template (runtime : Program) (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime)
    (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template runtime argument) :
    PureData.Template runtime (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have supported : ownedHeads head = true := by simp [ownedHeads, member]
    rw [← agreement.dispatch head supported]
    have checked : dataHeads.all (fun head =>
        !(ioHead head || StdLib.known head || sourceProgram.equations.any (·.head == head))) = true := by
      decide +kernel
    have inert := List.all_eq_true.mp checked head member
    cases selected : (ioHead head || StdLib.known head || sourceProgram.equations.any (·.head == head)) with
    | false => rfl
    | true => simp [selected] at inert
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem add_returns (runtime : Program) (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime)
    (caller : Subst) (state : State) (left right : Nat) (one two : Atom)
    (first : PureReturns runtime caller state one state (number left))
    (second : PureReturns runtime caller state two state (number right)) :
    PureReturns runtime caller state (a "+" [one, two]) state (number (left + right)) := by
  have supported : ownedHeads "+" = true := by decide
  apply native_binary_call_returns runtime caller state state state state "+"
    one two (number left) (number right) (number (left + right))
    (by decide) (by decide) _ _ first second _ (by decide)
  · rw [← agreement.demand "+" 0 supported]; decide +kernel
  · rw [← agreement.demand "+" 1 supported]; decide +kernel
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
      StdLib.integer_addition state (left : Int) (right : Int)

/-- Every field is a realization theorem for an actual named lower operation.
These contracts are discharged by the separately checked operation modules
when the coherent source program is assembled. -/
structure LowerOperations (runtime : Program) : Prop where
  row : ∀ (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [number index, termListValue values] →
    PureReturns runtime caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?))
  length : ∀ (caller : Subst) (state : State) (values : List Term) (input : Atom),
    applySubst caller input = termListValue values →
    PureReturns runtime caller state (a "gslt:automata:length" [input]) state (number values.length)
  append : ∀ (caller : Subst) (state : State) (left right : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [termListValue left, termListValue right] →
    PureReturns runtime caller state (a "gslt:automata:append" [one, two]) state (termListValue (left ++ right))
  start : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom),
    applySubst caller input = requestValue request →
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (matcherValue (GeneralScopedMatchMachine.start request))
  tick : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom),
    [one, two].map (applySubst caller) = [requestValue request, matcherValue machine] →
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (matcherValue (GeneralScopedMatchMachine.tick request machine))
  complete : ∀ (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom),
    applySubst caller input = matcherValue machine →
    PureReturns runtime caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine))
  assignment : ∀ (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
    (assignment : Assignment) (one two three four five six : Atom),
    [one, two, three, four, five, six].map (applySubst caller) =
      [declarationsValue language, freeValue free, boundValue bound, ruleValue rule, specValue spec, assignmentValue assignment] →
    PureReturns runtime caller state (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language (FreeTypeContext.ofList free) bound rule spec assignment))
  sorted : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) (one two three four five : Atom),
    [one, two, three, four, five].map (applySubst caller) =
      [declarationsValue language, freeValue free, boundValue bound, typeValue type, patternValue pattern] →
    PureReturns runtime caller state (a "gslt:premise:open-well-sorted" [one, two, three, four, five]) state
      (Effects.boolean (checkOpenPatternWellSorted language (FreeTypeContext.ofList free) bound type pattern))
  selection : ∀ (caller : Subst) (state : State) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (one two : Atom),
    [one, two].map (applySubst caller) = [reflectionValue profile, ruleValue rule] →
    PureReturns runtime caller state (a "gslt:premise:substitution-presentation" [one, two]) state (selectionValue profile rule)
  reduct : ∀ (caller : Subst) (state : State) (profile : Reflection.ReflectionProfile)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) (one two three four five : Atom),
    [one, two, three, four, five].map (applySubst caller) =
      [selectionValue profile rule, ruleValue rule, specValue spec, number ambient, assignmentValue assignment] →
    PureReturns runtime caller state (a "gslt:rule:scope-reduct" [one, two, three, four, five]) state
      (patternOptionValue (reductWith? (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingFramework


section MatchingSyntax
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def caseData (input : Atom) (rows : SpaceSemantics.Cases) : Atom :=
  a "case" [input, .expression (rows.map fun row => .expression [row.1, row.2])]

def caseInput : Atom → Atom
  | .expression [.symbol "case", input, _] => input
  | _ => .symbol "None"

def caseRows : Atom → SpaceSemantics.Cases
  | .expression [.symbol "case", _, .expression rows] =>
      rows.filterMap fun row => match row with
        | .expression [pattern, body] => some (pattern, body)
        | _ => none
  | _ => []

def branchBody (code : Atom) (index : Nat) : Atom :=
  ((caseRows code)[index]?.map Prod.snd).getD (.symbol "None")

def nestedBody (helper : Helper) : Nat → Atom
  | 0 => (equation helper).body
  | level + 1 => branchBody (nestedBody helper level) 0

def nestedRows (helper : Helper) (level : Nat) : SpaceSemantics.Cases := caseRows (nestedBody helper level)

def caseLimit : Helper → Nat
  | .root | .stepped => 5
  | .target => 6
  | .body => 3

theorem nested_case_shape (helper : Helper) (level : Nat) (bounded : level < caseLimit helper) :
    nestedBody helper level = caseData (caseInput (nestedBody helper level)) (nestedRows helper level) := by
  cases helper <;> simp only [caseLimit] at bounded
  all_goals
    have small : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 ∨ level = 4 ∨ level = 5 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

def fields (caller : Subst) (names : List String) (values : List Atom) : Subst :=
  (names.zip values).reverse ++ caller

def snapshotValues (environment : Environment) (free : List (String × TypeExpr)) : List Atom :=
  [declarationsValue environment.language,
   encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites),
   encoded (encodeList specificationTerm environment.specifications), encoded (providerTerm environment.provider),
   reflectionValue environment.reflection, freeValue free]

def snapshotNames : List String := ["declarations", "rewrites", "specifications", "provider", "reflection", "free"]

theorem snapshot_shape (environment : Environment) (free : List (String × TypeExpr)) :
    encoded (environmentTerm environment free) = a "PremiseEnvironment" (snapshotValues environment free) := rfl

theorem snapshot_rows (helper : Helper) : nestedRows helper 0 =
    [(a "PremiseEnvironment" (snapshotNames.map v), nestedBody helper 1), (v "badEnvironment", .symbol "None")] := by
  cases helper <;> decide +kernel

theorem lookup_zip_fresh (names : List String) (values : List Atom) (name : String)
    (fresh : name ∉ names) : Subst.lookup (names.zip values).reverse name = none := by
  unfold Subst.lookup
  have absent : (names.zip values).reverse.find? (fun pair => pair.1 == name) = none := by
    apply List.find?_eq_none.mpr
    intro pair member
    have key : pair.1 ∈ names := (List.of_mem_zip (List.mem_reverse.mp member)).1
    intro equal
    have same : pair.1 = name := beq_iff_eq.mp equal
    exact fresh (same ▸ key)
  rw [absent]
  rfl

theorem snapshot_field_fresh (helper : Helper) (values : List Atom) (name : String)
    (member : name ∈ snapshotNames) : Subst.lookup (callEnvironment helper values) name = none := by
  apply lookup_zip_fresh
  cases helper <;> simp only [snapshotNames, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem snapshot_selected (helper : Helper) (values : List Atom) (environment : Environment)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (callEnvironment helper values) (encoded (environmentTerm environment free))
      (nestedRows helper 0) =
      some (fields (callEnvironment helper values) snapshotNames (snapshotValues environment free), nestedBody helper 1) := by
  rw [snapshot_rows, snapshot_shape]
  have fresh (name : String) (member : name ∈ snapshotNames) := snapshot_field_fresh helper values name member
  have lookupDeclarations := fresh "declarations" (by decide)
  have lookupRewrites := fresh "rewrites" (by decide)
  have lookupSpecifications := fresh "specifications" (by decide)
  have lookupProvider := fresh "provider" (by decide)
  have lookupReflection := fresh "reflection" (by decide)
  have lookupFree := fresh "free" (by decide)
  unfold Subst.lookup at lookupDeclarations lookupRewrites lookupSpecifications lookupProvider lookupReflection lookupFree
  simp [snapshotNames, snapshotValues, fields,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, lookupDeclarations, lookupRewrites, lookupSpecifications, lookupProvider, lookupReflection, lookupFree]

theorem match_fields (caller : Subst) (head : String) (names : List String) (values : List Atom)
    (ordinary : head ≠ "cons") (distinct : names.Nodup) (length : values.length = names.length)
    (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.matchValue caller (a head (names.map v)) (a head values) =
      some (fields caller names values) := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  simp only [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue, matchAtom,
    beq_self_eq_true, Option.bind_eq_bind]
  exact PureData.match_variable_values names values caller distinct length fresh

theorem select_fields_first (caller : Subst) (head : String) (names : List String) (values : List Atom)
    (body : Atom) (rest : SpaceSemantics.Cases) (ordinary : head ≠ "cons") (distinct : names.Nodup)
    (length : values.length = names.length) (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.selectCase caller (a head values) ((a head (names.map v), body) :: rest) =
      some (fields caller names values, body) := by
  rw [SpaceSemantics.selectCase, match_fields caller head names values ordinary distinct length fresh]

theorem branch_returns (runtime : Program) (caller selected : Subst) (state : State)
    (input value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state input state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state (caseData input rows) state answer :=
  case_returns runtime caller selected state state state input value body answer _ rows
    (read_cases_encoded _) computed matched continued

theorem nested_branch_returns (runtime : Program) (helper : Helper) (level : Nat)
    (bounded : level < caseLimit helper) (caller selected : Subst) (state : State) (value body answer : Atom)
    (computed : PureReturns runtime caller state (caseInput (nestedBody helper level)) state value)
    (matched : SpaceSemantics.selectCase caller value (nestedRows helper level) = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state (nestedBody helper level) state answer := by
  rw [nested_case_shape helper level bounded]
  exact branch_returns runtime caller selected state _ value _ body answer computed matched continued

theorem named_let_returns (runtime : Program) (caller : Subst) (state : State) (name : String)
    (code value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (returned : PureReturns runtime caller state code state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, code, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state (v name) code body value answer returned _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

theorem bool_if_returns (runtime : Program) (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

syntax "frame_template " term:max term:max : tactic
macro_rules
  | `(tactic| frame_template $runtime $agreement) => `(tactic|
      first
      | exact PureData.Template.captured _
      | exact PureData.Template.symbol _
      | exact PureData.Template.grounded _
      | apply data_template $runtime $agreement _ _ (by decide)
        intro argument member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        repeat' (first | (rcases member with rfl | member) | (subst argument))
        all_goals frame_template $runtime $agreement)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingSyntax


section MatchingStepped
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def steppedNames (level : Nat) : List String :=
  match level with
  | 1 => ["call", "tail"]
  | 2 => ["context", "premise", "initial", "binders", "type", "source", "target-schema"]
  | 3 => ["rule-index", "rule", "spec", "bound", "premise-index", "quantifiers"]
  | 4 => ["goal", "index", "trace", "captured", "completed", "history", "target"]
  | _ => []

theorem stepped_rows_one : nestedRows .stepped 1 =
    [(a "PremiseStepped" ((steppedNames 1).map v), nestedBody .stepped 2),
     (v "badContinuation", .symbol "None")] := by decide +kernel

theorem stepped_rows_two : nestedRows .stepped 2 =
    [(a "PremiseStepCall" ((steppedNames 2).map v), nestedBody .stepped 3),
     (v "badCall", .symbol "None")] := by decide +kernel

theorem stepped_rows_three : nestedRows .stepped 3 =
    [(a "PremiseContext" ((steppedNames 3).map v), nestedBody .stepped 4),
     (v "badContext", .symbol "None")] := by decide +kernel

theorem stepped_rows_four : nestedRows .stepped 4 =
    [(a "PremiseResult" [v "goal", a "StepsAnswer" ((steppedNames 4).tail.map v)], nestedBody .stepped 5),
     (v "badResult", .symbol "None")] := by decide +kernel

def steppedPairs : List (Atom × Atom) :=
  [(v "ambient", a "gslt:automata:length" [v "bound"]),
   (v "depth", a "gslt:automata:length" [v "binders"]),
   (v "request", a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient",
     a "RulePremise" [v "premise-index", v "quantifiers", number 1], .symbol "LNil", v "depth",
     v "initial", v "target-schema", v "target"]),
   (v "matcher", a "gslt:rule:scope-matcher-start" [v "request"])]

def steppedFinal : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseTargetMatch" [v "call", v "index", v "trace", v "captured", v "completed",
       v "history", v "target", v "matcher", number 0, v "tail"], .symbol "LNil"],
     .symbol "LNil", .symbol "LNil"]]

theorem stepped_let_shape : nestedBody .stepped 5 =
    a "let*" [.expression (steppedPairs.map fun pair => .expression [pair.1, pair.2]), steppedFinal] := by
  decide +kernel

def contextValues (context : GeneralPremise.Context) : List Atom :=
  [number context.ruleIndex, ruleValue context.rule, specValue context.spec, boundValue context.bound,
   number context.premiseIndex, number context.quantifierDepth]

theorem context_shape (context : GeneralPremise.Context) :
    encoded (contextTerm context) = a "PremiseContext" (contextValues context) := rfl

def callValues {environment : Environment} (call : StepCall environment) : List Atom :=
  [encoded (contextTerm call.context), encoded (InferenceCettaWire.AuthoredRule.premiseTerm call.premise),
   assignmentValue call.initial, boundValue call.binders, typeValue call.type,
   patternValue call.source, patternValue call.targetSchema]

theorem call_shape {environment : Environment} (call : StepCall environment) :
    encoded (stepCallTerm call) = a "PremiseStepCall" (callValues call) := rfl

def targetRequest {environment : Environment} (call : StepCall environment) (target : Pattern) :
    GeneralScopedMatchMachine.Request :=
  ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
    [], call.binders.length, call.initial, call.targetSchema, target⟩

theorem length_encoded_returns {α : Type} (runtime : Program) (lower : LowerOperations runtime)
    (element : α → Term) (caller : Subst) (state : State) (values : List α) (input : Atom)
    (captured : applySubst caller input = encoded (encodeList element values)) :
    PureReturns runtime caller state (a "gslt:automata:length" [input]) state (number values.length) := by
  have returned := lower.length caller state (values.map element) input (by
    simpa only [termListValue, encodeList_map, Function.id_comp] using captured)
  simpa only [List.length_map] using returned

theorem stepped_delivered_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (free : List (String × TypeExpr))
    (outer : Goal) (call : StepCall environment)
    (result : Result environment (.steps (call.binders ++ call.context.bound) call.type call.source call.context.ruleIndex))
    (tail : Continuation environment (.premise call.context call.premise call.initial) outer) :
    PureReturns runtime [] state (a Helper.stepped.head
      [encoded (environmentTerm environment free), encoded (resultTerm result),
       encoded (continuationTerm (.stepped call tail))]) state
      (encoded (encodeOption expansionTerm (some (delivered environment outer result (.stepped call tail))))) := by
  cases result with
  | steps index trace captured completed history target earlier valid =>
      let resultValue := encoded (resultTerm (.steps index trace captured completed history target earlier valid))
      let continuationValue := a "PremiseStepped" [encoded (stepCallTerm call), encoded (continuationTerm tail)]
      let inputs := [encoded (environmentTerm environment free), resultValue, continuationValue]
      let caller := callEnvironment .stepped inputs
      let snapshot := fields caller snapshotNames (snapshotValues environment free)
      let continuation := fields snapshot (steppedNames 1) [encoded (stepCallTerm call), encoded (continuationTerm tail)]
      let called := fields continuation (steppedNames 2) (callValues call)
      let context := fields called (steppedNames 3) (contextValues call.context)
      let resultFields := [encoded (goalTerm (.steps (call.binders ++ call.context.bound) call.type call.source call.context.ruleIndex)),
        number index, encoded (traceTerm trace), assignmentValue captured, assignmentValue completed,
        encoded (eventsTerm history), patternValue target]
      let answered := fields context (steppedNames 4) resultFields
      let ambient := ("ambient", number call.context.bound.length) :: answered
      let depth := ("depth", number call.binders.length) :: ambient
      let requested := ("request", requestValue (targetRequest call target)) :: depth
      let matched := ("matcher", matcherValue (GeneralScopedMatchMachine.start (targetRequest call target))) :: requested
      apply helper_call runtime agreement .stepped [] state inputs inputs _ rfl
        (by simp [inputs, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      apply nested_branch_returns runtime .stepped 0 (by decide) caller snapshot state
        (encoded (environmentTerm environment free)) (nestedBody .stepped 1)
      · change PureReturns runtime caller state (v "snapshot") state _
        simpa [caller, inputs, callEnvironment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
          variable_returns runtime caller state "snapshot"
      · exact snapshot_selected .stepped inputs environment free
      · apply nested_branch_returns runtime .stepped 1 (by decide) snapshot continuation state
          continuationValue (nestedBody .stepped 2)
        · change PureReturns runtime snapshot state (v "continuation") state _
          simpa [snapshot, caller, inputs, fields, snapshotNames, snapshotValues,
            callEnvironment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
              variable_returns runtime snapshot state "continuation"
        · rw [stepped_rows_one]
          apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
          intro name member
          simp only [steppedNames, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;>
            simp [snapshot, caller, inputs, fields, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
        · apply nested_branch_returns runtime .stepped 2 (by decide) continuation called state
            (encoded (stepCallTerm call)) (nestedBody .stepped 3)
          · change PureReturns runtime continuation state (v "call") state _
            simpa [continuation, fields, steppedNames, applySubst, applySubst.applySubstList, Subst.lookup] using
              variable_returns runtime continuation state "call"
          · rw [stepped_rows_two, call_shape]
            apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
            intro name member
            simp only [steppedNames, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [continuation, snapshot, caller, inputs, fields, steppedNames, snapshotNames,
                snapshotValues, callEnvironment, Helper.names, Subst.lookup]
          · apply nested_branch_returns runtime .stepped 3 (by decide) called context state
              (encoded (contextTerm call.context)) (nestedBody .stepped 4)
            · change PureReturns runtime called state (v "context") state _
              simpa [called, fields, steppedNames, callValues, applySubst, applySubst.applySubstList, Subst.lookup] using
                variable_returns runtime called state "context"
            · rw [stepped_rows_three, context_shape]
              apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
              intro name member
              simp only [steppedNames, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
                simp [called, continuation, snapshot, caller, inputs, fields, steppedNames, snapshotNames,
                  snapshotValues, callValues, callEnvironment, Helper.names, Subst.lookup]
            · apply nested_branch_returns runtime .stepped 4 (by decide) context answered state
                resultValue (nestedBody .stepped 5)
              · change PureReturns runtime context state (v "result") state _
                simpa [context, called, continuation, snapshot, caller, inputs, fields, steppedNames,
                  contextValues, callValues, snapshotNames, snapshotValues, callEnvironment, Helper.names,
                  applySubst, applySubst.applySubstList, Subst.lookup] using variable_returns runtime context state "result"
              · rw [stepped_rows_four]
                simp [resultValue, resultTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, answered, context, called, continuation, snapshot, caller, inputs,
                  resultFields, fields, steppedNames, contextValues, callValues, snapshotNames, snapshotValues,
                  callEnvironment, Helper.names, Subst.lookup]
              · rw [stepped_let_shape]
                apply PureData.let_bindings_return (final := matched) (pairs := steppedPairs)
                · unfold steppedPairs
                  apply PureData.BindingsReturn.cons (bound := ambient)
                  · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm
                      answered state call.context.bound
                    simp [answered, context, called, fields, steppedNames, resultFields, contextValues,
                      callValues, applySubst, Subst.lookup]
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, ambient,
                      answered, context, called, continuation, snapshot, caller, inputs, resultFields, fields,
                      steppedNames, contextValues, callValues, snapshotNames, snapshotValues,
                      callEnvironment, Helper.names, Subst.lookup]
                  · apply PureData.BindingsReturn.cons (bound := depth)
                    · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm
                        ambient state call.binders
                      simp [ambient, answered, context, called, fields, steppedNames, resultFields,
                        contextValues, callValues, applySubst, Subst.lookup]
                    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, depth, ambient,
                        answered, context, called, continuation, snapshot, caller, inputs, resultFields, fields,
                        steppedNames, contextValues, callValues, snapshotNames, snapshotValues,
                        callEnvironment, Helper.names, Subst.lookup]
                    · apply PureData.BindingsReturn.cons (bound := requested)
                      · have returned := PureData.template_return runtime depth state steppedPairs[2]!.2 (by
                          change PureData.Template runtime (a "ScopedMatcherRequest" _)
                          frame_template runtime agreement)
                        simpa [steppedPairs, depth, ambient, answered, context, called, fields, steppedNames,
                          resultFields, contextValues, callValues, targetRequest, matcherRequestTerm,
                          GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
                          applySubst, applySubst.applySubstList, Subst.lookup] using returned
                      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, requested, depth,
                          ambient, answered, context, called, continuation, snapshot, caller, inputs, resultFields, fields,
                          steppedNames, contextValues, callValues, snapshotNames, snapshotValues,
                          callEnvironment, Helper.names, Subst.lookup]
                        rfl
                      · apply PureData.BindingsReturn.cons (bound := matched)
                        · apply lower.start requested state (targetRequest call target)
                          simp [requested, applySubst, Subst.lookup]
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, matched, requested,
                            depth, ambient, answered, context, called, continuation, snapshot, caller, inputs, resultFields,
                            fields, steppedNames, contextValues, callValues, snapshotNames, snapshotValues,
                            callEnvironment, Helper.names, Subst.lookup]
                        · exact PureData.BindingsReturn.nil matched state
                · have returned := PureData.template_return runtime matched state steppedFinal (by
                    unfold steppedFinal
                    frame_template runtime agreement)
                  simpa [steppedFinal, matched, requested, depth, ambient, answered, context, called, continuation,
                    snapshot, caller, inputs, resultFields, fields, steppedNames, contextValues, callValues,
                    snapshotNames, snapshotValues, callEnvironment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                    delivered, expansionTerm, taskTerm, targetRequest, encodeOption, encodeList,
                    encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingStepped


section MatchingRootBody
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def bodyNames : List String := ["bound", "type", "source", "index", "rule", "spec", "trace", "captured", "tail"]
def bodyAnswerNames : List String := ["goal", "completed", "history"]

theorem body_rows_one : nestedRows .body 1 =
    [(a "PremiseRootBody" (bodyNames.map v), nestedBody .body 2), (v "badContinuation", .symbol "None")] := by
  decide +kernel

theorem body_rows_two : nestedRows .body 2 =
    [(a "PremiseResult" [v "goal", a "PremisesAnswer" [v "completed", v "history"]], nestedBody .body 3),
     (v "badResult", .symbol "None")] := by decide +kernel

def emptyExpansion : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

def bodyUnresolved : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a "PremiseTargetProjection" [v "index"], .symbol "LNil"]]]

def bodySuccess : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseDeliver"
      [a "PremiseResult" [a "RootGoal" [v "bound", v "type", v "source", v "index"],
        a "RootAnswer" [v "trace", v "captured", v "completed", v "history", v "target"]], v "tail"],
      .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

def bodySorted : Atom :=
  a "gslt:premise:open-well-sorted" [v "declarations", v "free", v "bound", v "type", v "target"]

def bodyCases : SpaceSemantics.Cases :=
  [(.symbol "None", bodyUnresolved),
   (a "Some" [v "target"], a "if" [bodySorted, bodySuccess, emptyExpansion]),
   (v "badTarget", .symbol "None")]

def bodyPairs : List (Atom × Atom) :=
  [(v "operation", a "gslt:premise:substitution-presentation" [v "reflection", v "rule"]),
   (v "ambient", a "gslt:automata:length" [v "bound"])]

def bodyReduct : Atom := a "gslt:rule:scope-reduct" [v "operation", v "rule", v "spec", v "ambient", v "completed"]

theorem body_let_shape : nestedBody .body 3 =
    a "let*" [.expression (bodyPairs.map fun pair => .expression [pair.1, pair.2]), caseData bodyReduct bodyCases] := by
  decide +kernel

theorem root_body_delivered_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (index : Nat)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type sourcePattern)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured : Assignment)
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left sourcePattern trace captured)
    (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
    (completed : Assignment) (history : List Event)
    (valid : PremisesHold environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured completed history)
    (tail : Continuation environment (.root bound type sourcePattern index) outer)
    (covers : ∀ target, reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      rule spec bound.length completed = some target → ∀ name ∈ target.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state (a Helper.body.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)),
       encoded (resultTerm (.premises completed history valid)),
       encoded (continuationTerm (.rootBody bound type sourcePattern index rule spec declared specified admitted sorted
         trace captured matched capturedTyped tail))]) state
      (encoded (encodeOption expansionTerm (some (delivered environment outer (.premises completed history valid)
        (.rootBody bound type sourcePattern index rule spec declared specified admitted sorted
          trace captured matched capturedTyped tail))))) := by
  let free := environment.free.entriesOn footprint
  let resultValue := encoded (resultTerm (.premises completed history valid))
  let continuationValue := a "PremiseRootBody"
    [boundValue bound, typeValue type, patternValue sourcePattern, number index, ruleValue rule, specValue spec,
     encoded (traceTerm trace), assignmentValue captured, encoded (continuationTerm tail)]
  let inputs := [encoded (environmentTerm environment free), resultValue, continuationValue]
  let caller := callEnvironment .body inputs
  let snapshot := fields caller snapshotNames (snapshotValues environment free)
  let continuation := fields snapshot bodyNames
    [boundValue bound, typeValue type, patternValue sourcePattern, number index, ruleValue rule, specValue spec,
     encoded (traceTerm trace), assignmentValue captured, encoded (continuationTerm tail)]
  let answered := fields continuation bodyAnswerNames
    [encoded (goalTerm (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured)),
     assignmentValue completed, encoded (eventsTerm history)]
  let operation := ("operation", selectionValue environment.reflection rule) :: answered
  let ambient := ("ambient", number bound.length) :: operation
  apply helper_call runtime agreement .body [] state inputs inputs _ rfl
    (by simp [inputs, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  apply nested_branch_returns runtime .body 0 (by decide) caller snapshot state
    (encoded (environmentTerm environment free)) (nestedBody .body 1)
  · change PureReturns runtime caller state (v "snapshot") state _
    simpa [caller, inputs, callEnvironment, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "snapshot"
  · exact snapshot_selected .body inputs environment free
  · apply nested_branch_returns runtime .body 1 (by decide) snapshot continuation state
      continuationValue (nestedBody .body 2)
    · change PureReturns runtime snapshot state (v "continuation") state _
      simpa [snapshot, caller, inputs, fields, snapshotNames, snapshotValues,
        callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime snapshot state "continuation"
    · rw [body_rows_one]
      apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
      intro name member
      simp only [bodyNames, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [snapshot, caller, inputs, fields, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
    · apply nested_branch_returns runtime .body 2 (by decide) continuation answered state resultValue (nestedBody .body 3)
      · change PureReturns runtime continuation state (v "result") state _
        simpa [continuation, snapshot, caller, inputs, fields, bodyNames, snapshotNames, snapshotValues,
          callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime continuation state "result"
      · rw [body_rows_two]
        simp [resultValue, resultTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, answered, continuation, snapshot, caller, inputs, fields, bodyNames, bodyAnswerNames,
          snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
      · rw [body_let_shape]
        apply PureData.let_bindings_return (final := ambient) (pairs := bodyPairs)
        · unfold bodyPairs
          apply PureData.BindingsReturn.cons (bound := operation)
          · apply lower.selection answered state environment.reflection rule
            simp [answered, continuation, snapshot, fields, bodyNames, bodyAnswerNames, snapshotNames, snapshotValues,
              applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, operation,
              answered, continuation, snapshot, caller, inputs, fields, bodyNames, bodyAnswerNames,
              snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := ambient)
            · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm operation state bound
              simp [operation, answered, continuation, fields, bodyNames, bodyAnswerNames, applySubst, Subst.lookup]
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, ambient, operation,
                answered, continuation, snapshot, caller, inputs, fields, bodyNames, bodyAnswerNames,
                snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
            · exact PureData.BindingsReturn.nil ambient state
        · have reduced := lower.reduct ambient state environment.reflection rule spec bound.length completed
            (v "operation") (v "rule") (v "spec") (v "ambient") (v "completed") (by
              simp [ambient, operation, answered, continuation, fields, bodyNames, bodyAnswerNames, applySubst, Subst.lookup])
          have wire : encoded (encodeOption expansionTerm (some (delivered environment outer
              (.premises completed history valid) (.rootBody bound type sourcePattern index rule spec
                declared specified admitted sorted trace captured matched capturedTyped tail)))) =
              match reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
                  rule spec bound.length completed with
              | none => applySubst ambient bodyUnresolved
              | some target => if checkOpenPatternWellSorted environment.language environment.free bound type target
                  then applySubst (("target", patternValue target) :: ambient) bodySuccess
                  else applySubst (("target", patternValue target) :: ambient) emptyExpansion := by
            simp only [delivered]
            split
            · rename_i converted
              simp [converted, bodyUnresolved, ambient, operation, answered, continuation, fields, bodyNames,
                bodyAnswerNames, applySubst, applySubst.applySubstList, Subst.lookup, expansionTerm, obligationTerm,
                encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · rename_i target converted
              split_ifs with checked
              · simp [converted, checked, bodySuccess, ambient, operation, answered, continuation, fields, bodyNames,
                  bodyAnswerNames, applySubst, applySubst.applySubstList, Subst.lookup, expansionTerm, taskTerm,
                  resultTerm, goalTerm, encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
              · simp [converted, checked, emptyExpansion, applySubst, applySubst.applySubstList, expansionTerm,
                  encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          rw [wire]
          cases converted : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
              rule spec bound.length completed with
          | none =>
              apply branch_returns runtime ambient ambient state bodyReduct (.symbol "None") bodyCases bodyUnresolved
              · simpa only [bodyReduct, converted, patternOptionValue, encodeOption, encoded, CettaWireAtom.encode] using reduced
              · simp [bodyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · have returned := PureData.template_return runtime ambient state bodyUnresolved (by
                  unfold bodyUnresolved
                  frame_template runtime agreement)
                simpa only [converted] using returned
          | some target =>
              let selected := ("target", patternValue target) :: ambient
              apply branch_returns runtime ambient selected state bodyReduct (a "Some" [patternValue target]) bodyCases
                (a "if" [bodySorted, bodySuccess, emptyExpansion])
              · simpa only [bodyReduct, converted, patternOptionValue, encodeOption, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using reduced
              · simp [bodyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, selected, ambient, operation, answered, continuation, snapshot, caller, inputs, fields,
                  bodyNames, bodyAnswerNames, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
              · have tested := lower.sorted selected state environment.language free bound type target
                  (v "declarations") (v "free") (v "bound") (v "type") (v "target") (by
                    simp [selected, ambient, operation, answered, continuation, snapshot, fields, bodyNames,
                      bodyAnswerNames, snapshotNames, snapshotValues, applySubst, Subst.lookup])
                have same := Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot environment.language environment.free bound type target footprint
                  (covers target converted)
                change checkOpenPatternWellSorted environment.language (FreeTypeContext.ofList free) bound type target = _ at same
                rw [same] at tested
                apply bool_if_returns runtime selected state bodySorted
                  (checkOpenPatternWellSorted environment.language environment.free bound type target)
                  bodySuccess emptyExpansion _ tested
                cases checked : checkOpenPatternWellSorted environment.language environment.free bound type target with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have returned := PureData.template_return runtime selected state emptyExpansion (by
                      unfold emptyExpansion
                      frame_template runtime agreement)
                    simpa only [converted, checked, Bool.false_eq_true, ↓reduceIte] using returned
                | true =>
                    simp only [↓reduceIte]
                    have returned := PureData.template_return runtime selected state bodySuccess (by
                      unfold bodySuccess
                      frame_template runtime agreement)
                    simpa only [converted, checked, ↓reduceIte] using returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingRootBody


section MatchingRootExpand
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

abbrev answerTerm := RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
abbrev workTerm := RuleInstantiationExecution.GeneralExecution.matcherWorkTerm

def rootNames : List String := ["bound", "type", "source", "index", "rule", "spec", "matcher", "cursor", "tail"]
def ruleNames : List String := ["name", "types", "premises", "left", "right", "bindings"]
def matcherNames : List String := ["agenda", "answers"]

def rootLater : Atom := a "PremiseRootMatch"
  [v "bound", v "type", v "source", v "index", v "rule", v "spec", v "matcher", v "next", v "tail"]
def rootAccepted : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseEvaluate"
      [a "PremisesGoal" [a "PremiseContext" [v "index", v "rule", v "spec", v "bound", number 0, number 0],
        v "premises", v "assignment"],
       a "PremiseRootBody" [v "bound", v "type", v "source", v "index", v "rule", v "spec", v "trace", v "assignment", v "tail"]],
     a "LCons" [v "later", .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]
def rootSkipped : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [v "later", .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def rootChecked : Atom :=
  a "gslt:premise:check-assignment" [v "declarations", v "free", v "bound", v "rule", v "spec", v "assignment"]
def rootAnswerBody : Atom :=
  a "let" [v "next", a "+" [v "cursor", number 1],
    a "let" [v "later", rootLater, a "if" [rootChecked, rootAccepted, rootSkipped]]]
def rootRequestCode : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", .symbol "RuleLeft", .symbol "LNil", number 0,
    .symbol "LNil", v "left", v "source"]
def rootAdvanced : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseRootMatch" [v "bound", v "type", v "source", v "index", v "rule", v "spec",
      v "advanced", v "cursor", v "tail"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def rootStopBody : Atom :=
  a "if" [a "gslt:rule:scope-matcher-complete" [v "matcher"], emptyExpansion,
    a "let" [v "ambient", a "gslt:automata:length" [v "bound"],
      a "let" [v "request", rootRequestCode,
        a "let" [v "advanced", a "gslt:rule:scope-matcher-tick" [v "request", v "matcher"], rootAdvanced]]]]
def rootAnswerCases : SpaceSemantics.Cases :=
  [(a "Some" [a "ScopedMatcherAnswer" [v "assignment", v "trace"]], rootAnswerBody),
   (.symbol "None", rootStopBody), (v "badAnswer", .symbol "None")]

theorem root_rows_one : nestedRows .root 1 =
    [(a "PremiseRootMatch" (rootNames.map v), nestedBody .root 2), (v "badTask", .symbol "None")] := by decide +kernel
theorem root_rows_two : nestedRows .root 2 =
    [(a "ScopedRewriteRuleV1" (ruleNames.map v), nestedBody .root 3), (v "badRule", .symbol "None")] := by decide +kernel
theorem root_rows_three : nestedRows .root 3 =
    [(a "ScopedMatcherState" (matcherNames.map v), nestedBody .root 4), (v "badMatcher", .symbol "None")] := by decide +kernel
theorem root_row_shape : nestedBody .root 4 = caseData (a "gslt:rule:row-at" [v "cursor", v "answers"]) rootAnswerCases := by
  decide +kernel

def rootValues {environment : Environment} {outer : Goal} (frame : RootMatchFrame environment outer) : List Atom :=
  [boundValue frame.bound, typeValue frame.type, patternValue frame.source, number frame.index,
   ruleValue frame.rule, specValue frame.spec, matcherValue frame.state, number frame.cursor, encoded (continuationTerm frame.tail)]
theorem root_shape {environment : Environment} {outer : Goal} (frame : RootMatchFrame environment outer) :
    encoded (taskTerm (.rootMatch frame)) = a "PremiseRootMatch" (rootValues frame) := rfl

def ruleValues (rule : RewriteRule) : List Atom :=
  [encoded (.string rule.name), encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext),
   encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises), patternValue rule.left,
   patternValue rule.right, encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)]
theorem rule_shape (rule : RewriteRule) : ruleValue rule = a "ScopedRewriteRuleV1" (ruleValues rule) := rfl

def matcherValues (machine : GeneralScopedMatchMachine.State) : List Atom :=
  [encoded (encodeList workTerm machine.agenda), encoded (encodeList answerTerm machine.answers)]
theorem matcher_shape (machine : GeneralScopedMatchMachine.State) :
    matcherValue machine = a "ScopedMatcherState" (matcherValues machine) := rfl

def rootRequest {environment : Environment} {outer : Goal} (frame : RootMatchFrame environment outer) :
    GeneralScopedMatchMachine.Request :=
  ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩

theorem row_encoded_returns {α : Type} (runtime : Program) (lower : LowerOperations runtime)
    (element : α → Term) (caller : Subst) (state : State) (index : Nat) (values : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, encoded (encodeList element values)]) :
    PureReturns runtime caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption element values[index]?)) := by
  have returned := lower.row caller state index (values.map element) one two (by
    simpa only [termListValue, encodeList_map, Function.id_comp] using captured)
  rw [List.getElem?_map] at returned
  cases found : values[index]? <;> simpa [found, encodeOption] using returned

theorem root_match_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (frame : RootMatchFrame environment outer)
    (covers : ∀ answer, frame.state.answers[frame.cursor]? = some answer →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames answer.assignment, name ∈ footprint) :
    PureReturns runtime [] state (a Helper.root.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)), encoded (taskTerm (.rootMatch frame))]) state
      (encoded (encodeOption expansionTerm (some (expandRootMatch environment outer frame)))) := by
  let free := environment.free.entriesOn footprint
  let inputs := [encoded (environmentTerm environment free), encoded (taskTerm (.rootMatch frame))]
  let caller := callEnvironment .root inputs
  let snapshot := fields caller snapshotNames (snapshotValues environment free)
  let framed := fields snapshot rootNames (rootValues frame)
  let ruled := fields framed ruleNames (ruleValues frame.rule)
  let machine := fields ruled matcherNames (matcherValues frame.state)
  let selected (answer : GeneralScopedMatchMachine.Answer) :=
    ("trace", encoded (traceTerm answer.trace)) :: ("assignment", assignmentValue answer.assignment) :: machine
  let next (answer : GeneralScopedMatchMachine.Answer) := ("next", number (frame.cursor + 1)) :: selected answer
  let later (answer : GeneralScopedMatchMachine.Answer) :=
    ("later", encoded (taskTerm (.rootMatch {frame with cursor := frame.cursor + 1}))) :: next answer
  let ambient := ("ambient", number frame.bound.length) :: machine
  let requested := ("request", requestValue (rootRequest frame)) :: ambient
  let advanced := ("advanced", matcherValue (GeneralScopedMatchMachine.tick (rootRequest frame) frame.state)) :: requested
  have wire : encoded (encodeOption expansionTerm (some (expandRootMatch environment outer frame))) =
      match frame.state.answers[frame.cursor]? with
      | some answer => if checkTypedAssignment environment ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment
          then applySubst (later answer) rootAccepted else applySubst (later answer) rootSkipped
      | none => if GeneralScopedMatchMachine.complete frame.state then applySubst machine emptyExpansion
          else applySubst advanced rootAdvanced := by
    simp only [expandRootMatch]
    split
    · rename_i answer found
      simp only [found]
      split_ifs with checked
      · simp [rootAccepted, later, next, selected, machine, ruled, framed, fields, matcherNames,
          matcherValues, ruleNames, ruleValues, rootNames, rootValues, applySubst, applySubst.applySubstList,
          Subst.lookup, expansionTerm, taskTerm, goalTerm, contextTerm, continuationTerm, encodeOption, encodeList,
          encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · simp [rootSkipped, later, next, selected, applySubst, applySubst.applySubstList,
          Subst.lookup, expansionTerm, encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · rename_i found
      simp only [found]
      split_ifs with finished
      · simp [emptyExpansion, applySubst, applySubst.applySubstList,
          expansionTerm, encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · simp [rootAdvanced, advanced, requested, ambient, machine, ruled, framed,
          fields, matcherNames, matcherValues, ruleNames, ruleValues, rootNames, rootValues,
          applySubst, applySubst.applySubstList, Subst.lookup, expansionTerm, taskTerm, rootRequest,
          encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  rw [wire]
  apply helper_call runtime agreement .root [] state inputs inputs _ rfl
    (by simp [inputs])
  apply nested_branch_returns runtime .root 0 (by decide) caller snapshot state
    (encoded (environmentTerm environment free)) (nestedBody .root 1)
  · change PureReturns runtime caller state (v "snapshot") state _
    simpa [caller, inputs, callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime caller state "snapshot"
  · exact snapshot_selected .root inputs environment free
  · apply nested_branch_returns runtime .root 1 (by decide) snapshot framed state
      (encoded (taskTerm (.rootMatch frame))) (nestedBody .root 2)
    · change PureReturns runtime snapshot state (v "task") state _
      simpa [snapshot, caller, inputs, fields, snapshotNames, snapshotValues,
        callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime snapshot state "task"
    · rw [root_rows_one, root_shape]
      apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
      intro name member
      simp only [rootNames, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [snapshot, caller, inputs, fields, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
    · apply nested_branch_returns runtime .root 2 (by decide) framed ruled state (ruleValue frame.rule) (nestedBody .root 3)
      · change PureReturns runtime framed state (v "rule") state _
        simpa [framed, fields, rootNames, rootValues, applySubst, Subst.lookup] using variable_returns runtime framed state "rule"
      · rw [root_rows_two, rule_shape]
        apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
        intro name member
        simp only [ruleNames, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [framed, snapshot, caller, inputs, fields, rootNames, rootValues, snapshotNames, snapshotValues,
            callEnvironment, Helper.names, Subst.lookup]
      · apply nested_branch_returns runtime .root 3 (by decide) ruled machine state (matcherValue frame.state) (nestedBody .root 4)
        · change PureReturns runtime ruled state (v "matcher") state _
          simpa [ruled, framed, fields, ruleNames, ruleValues, rootNames, rootValues, applySubst, Subst.lookup] using
            variable_returns runtime ruled state "matcher"
        · rw [root_rows_three, matcher_shape]
          apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
          intro name member
          simp only [matcherNames, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;>
            simp [ruled, framed, snapshot, caller, inputs, fields, ruleNames, ruleValues, rootNames, rootValues,
              snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
        · rw [root_row_shape]
          have row := row_encoded_returns runtime lower answerTerm machine state frame.cursor frame.state.answers
            (v "cursor") (v "answers") (by
              simp [machine, ruled, framed, fields, matcherNames, matcherValues, ruleNames, ruleValues,
                rootNames, rootValues, applySubst, Subst.lookup])
          cases found : frame.state.answers[frame.cursor]? with
          | some answer =>
              apply branch_returns runtime machine (selected answer) state _
                (a "Some" [encoded (answerTerm answer)]) rootAnswerCases rootAnswerBody
              · simpa only [found, encodeOption, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using row
              · simp [rootAnswerCases, answerTerm, RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
                  encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected, machine,
                  ruled, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues, ruleNames, ruleValues,
                  rootNames, rootValues, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
              · unfold rootAnswerBody
                apply named_let_returns runtime (selected answer) state "next" _ _ _ _
                · simp [selected, machine, ruled, framed, snapshot, caller, inputs, fields, matcherNames,
                    matcherValues, ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues,
                    callEnvironment, Helper.names, Subst.lookup]
                · apply add_returns runtime agreement (selected answer) state frame.cursor 1
                  · simpa [selected, machine, ruled, framed, fields, matcherNames, matcherValues, ruleNames,
                      ruleValues, rootNames, rootValues, applySubst, Subst.lookup] using
                      variable_returns runtime (selected answer) state "cursor"
                  · exact grounded_returns runtime (selected answer) state _
                · change PureReturns runtime (next answer) state (a "let" [v "later", rootLater,
                    a "if" [rootChecked, rootAccepted, rootSkipped]]) state _
                  apply named_let_returns runtime (next answer) state "later" _ _ _ _
                  · simp [next, selected, machine, ruled, framed, snapshot, caller, inputs, fields, matcherNames,
                      matcherValues, ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues,
                      callEnvironment, Helper.names, Subst.lookup]
                  · have returned := PureData.template_return runtime (next answer) state rootLater (by
                      unfold rootLater
                      frame_template runtime agreement)
                    simpa [rootLater, next, selected, machine, ruled, framed, fields, matcherNames, matcherValues,
                      ruleNames, ruleValues, rootNames, rootValues, applySubst, applySubst.applySubstList, Subst.lookup,
                      taskTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
                  · change PureReturns runtime (later answer) state (a "if" [rootChecked, rootAccepted, rootSkipped]) state _
                    have tested := lower.assignment (later answer) state environment.language free frame.bound frame.rule frame.spec answer.assignment
                      (v "declarations") (v "free") (v "bound") (v "rule") (v "spec") (v "assignment") (by
                        simp [later, next, selected, machine, ruled, framed, snapshot, fields, matcherNames, matcherValues,
                          ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues, applySubst, Subst.lookup])
                    have same := ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
                      frame.bound frame.rule frame.spec answer.assignment footprint (covers answer found)
                    rw [same] at tested
                    change PureReturns runtime (later answer) state rootChecked state
                      (Effects.boolean (checkTypedAssignment environment
                        ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment)) at tested
                    apply bool_if_returns runtime (later answer) state rootChecked _ rootAccepted rootSkipped _ tested
                    cases checked : checkTypedAssignment environment
                        ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment with
                    | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        have returned := PureData.template_return runtime (later answer) state rootSkipped (by
                          unfold rootSkipped
                          frame_template runtime agreement)
                        simpa only [found, checked, Bool.false_eq_true, ↓reduceIte] using returned
                    | true =>
                        simp only [↓reduceIte]
                        have returned := PureData.template_return runtime (later answer) state rootAccepted (by
                          unfold rootAccepted
                          frame_template runtime agreement)
                        simpa only [found, checked, ↓reduceIte] using returned
          | none =>
              apply branch_returns runtime machine machine state _ (.symbol "None") rootAnswerCases rootStopBody
              · simpa only [found, encodeOption, encoded, CettaWireAtom.encode] using row
              · simp [rootAnswerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · unfold rootStopBody
                have tested := lower.complete machine state frame.state (v "matcher") (by
                  simp [machine, ruled, framed, fields, matcherNames, matcherValues, ruleNames, ruleValues,
                    rootNames, rootValues, applySubst, Subst.lookup])
                apply bool_if_returns runtime machine state _ _ _ _ _ tested
                cases finished : GeneralScopedMatchMachine.complete frame.state with
                | true =>
                    simp only [↓reduceIte]
                    have returned := PureData.template_return runtime machine state emptyExpansion (by
                      unfold emptyExpansion
                      frame_template runtime agreement)
                    simpa only [found, finished, ↓reduceIte] using returned
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    apply named_let_returns runtime machine state "ambient" _ _ _ _
                    · simp [machine, ruled, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues,
                        ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues,
                        callEnvironment, Helper.names, Subst.lookup]
                    · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm machine state frame.bound
                      simp [machine, ruled, framed, fields, matcherNames, matcherValues, ruleNames, ruleValues,
                        rootNames, rootValues, applySubst, Subst.lookup]
                    · change PureReturns runtime ambient state (a "let" [v "request", rootRequestCode,
                        a "let" [v "advanced", a "gslt:rule:scope-matcher-tick" [v "request", v "matcher"], rootAdvanced]]) state _
                      apply named_let_returns runtime ambient state "request" _ _ _ _
                      · simp [ambient, machine, ruled, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues,
                          ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues,
                          callEnvironment, Helper.names, Subst.lookup]
                      · have returned := PureData.template_return runtime ambient state rootRequestCode (by
                          unfold rootRequestCode
                          frame_template runtime agreement)
                        simpa [rootRequestCode, ambient, machine, ruled, framed, fields, matcherNames, matcherValues,
                          ruleNames, ruleValues, rootNames, rootValues, applySubst, applySubst.applySubstList, Subst.lookup,
                          rootRequest, requestValue, RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
                          InferenceCettaWire.AuthoredRule.siteTerm, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
                      · change PureReturns runtime requested state
                          (a "let" [v "advanced", a "gslt:rule:scope-matcher-tick" [v "request", v "matcher"], rootAdvanced]) state _
                        apply named_let_returns runtime requested state "advanced" _ _ _ _
                        · simp [requested, ambient, machine, ruled, framed, snapshot, caller, inputs, fields, matcherNames,
                            matcherValues, ruleNames, ruleValues, rootNames, rootValues, snapshotNames, snapshotValues,
                            callEnvironment, Helper.names, Subst.lookup]
                        · apply lower.tick requested state (rootRequest frame) frame.state
                          simp [requested, ambient, machine, ruled, framed, fields, matcherNames, matcherValues,
                            ruleNames, ruleValues, rootNames, rootValues, applySubst, Subst.lookup]
                        · change PureReturns runtime advanced state rootAdvanced state _
                          have returned := PureData.template_return runtime advanced state rootAdvanced (by
                            unfold rootAdvanced
                            frame_template runtime agreement)
                          simpa only [found, finished, Bool.false_eq_true, ↓reduceIte] using returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingRootExpand


section MatchingTargetExpand
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def targetNames : List String :=
  ["call", "index", "trace", "captured", "completed", "history", "target", "matcher", "cursor", "tail"]
def targetLater : Atom := a "PremiseTargetMatch"
  [v "call", v "index", v "trace", v "captured", v "completed", v "history", v "target", v "matcher", v "next", v "tail"]
def targetAccepted : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseDeliver"
      [a "PremiseResult" [a "PremiseGoal" [v "context", v "premise", v "initial"],
        a "PremiseAnswer" [v "assignment", a "PremiseChildEvent"
          [v "premise-index", v "quantifiers", v "index", v "child-bound", v "source", v "target",
           v "trace", v "target-trace", v "captured", v "completed", v "history"]]], v "tail"],
      a "LCons" [v "later", .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]
def targetAnswerBody : Atom :=
  a "let" [v "next", a "+" [v "cursor", number 1],
    a "let" [v "later", targetLater, a "if" [rootChecked,
      a "let" [v "child-bound", a "gslt:automata:append" [v "binders", v "bound"], targetAccepted], rootSkipped]]]
def targetRequestCode : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient",
    a "RulePremise" [v "premise-index", v "quantifiers", number 1], .symbol "LNil", v "depth", v "initial",
    v "target-schema", v "target"]
def targetPairs : List (Atom × Atom) :=
  [(v "ambient", a "gslt:automata:length" [v "bound"]),
   (v "depth", a "gslt:automata:length" [v "binders"]),
   (v "request", targetRequestCode),
   (v "advanced", a "gslt:rule:scope-matcher-tick" [v "request", v "matcher"])]
def targetAdvanced : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "PremiseTargetMatch" [v "call", v "index", v "trace", v "captured", v "completed", v "history",
      v "target", v "advanced", v "cursor", v "tail"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def targetStopBody : Atom :=
  a "if" [a "gslt:rule:scope-matcher-complete" [v "matcher"], emptyExpansion,
    a "let*" [.expression (targetPairs.map fun pair => .expression [pair.1, pair.2]), targetAdvanced]]
def targetAnswerCases : SpaceSemantics.Cases :=
  [(a "Some" [a "ScopedMatcherAnswer" [v "assignment", v "target-trace"]], targetAnswerBody),
   (.symbol "None", targetStopBody), (v "badAnswer", .symbol "None")]

theorem target_rows_one : nestedRows .target 1 =
    [(a "PremiseTargetMatch" (targetNames.map v), nestedBody .target 2), (v "badTask", .symbol "None")] := by decide +kernel
theorem target_rows_two : nestedRows .target 2 =
    [(a "PremiseStepCall" ((steppedNames 2).map v), nestedBody .target 3), (v "badCall", .symbol "None")] := by decide +kernel
theorem target_rows_three : nestedRows .target 3 =
    [(a "PremiseContext" ((steppedNames 3).map v), nestedBody .target 4), (v "badContext", .symbol "None")] := by decide +kernel
theorem target_rows_four : nestedRows .target 4 =
    [(a "ScopedMatcherState" (matcherNames.map v), nestedBody .target 5), (v "badMatcher", .symbol "None")] := by decide +kernel
theorem target_row_shape : nestedBody .target 5 = caseData (a "gslt:rule:row-at" [v "cursor", v "answers"]) targetAnswerCases := by
  decide +kernel

def targetValues {environment : Environment} {outer : Goal} (frame : TargetMatchFrame environment outer) : List Atom :=
  [encoded (stepCallTerm frame.call), number frame.index, encoded (traceTerm frame.trace), assignmentValue frame.captured,
   assignmentValue frame.completed, encoded (eventsTerm frame.history), patternValue frame.target,
   matcherValue frame.state, number frame.cursor, encoded (continuationTerm frame.tail)]
theorem target_shape {environment : Environment} {outer : Goal} (frame : TargetMatchFrame environment outer) :
    encoded (taskTerm (.targetMatch frame)) = a "PremiseTargetMatch" (targetValues frame) := rfl

theorem append_encoded_returns {α : Type} (runtime : Program) (lower : LowerOperations runtime)
    (element : α → Term) (caller : Subst) (state : State) (left right : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (encodeList element left), encoded (encodeList element right)]) :
    PureReturns runtime caller state (a "gslt:automata:append" [one, two]) state
      (encoded (encodeList element (left ++ right))) := by
  have returned := lower.append caller state (left.map element) (right.map element) one two (by
    simpa only [termListValue, encodeList_map, Function.id_comp] using captured)
  rw [← List.map_append, termListValue, encodeList_map] at returned
  simpa only [Function.id_comp] using returned

theorem target_match_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (frame : TargetMatchFrame environment outer)
    (covers : ∀ answer, frame.state.answers[frame.cursor]? = some answer →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames answer.assignment, name ∈ footprint) :
    PureReturns runtime [] state (a Helper.target.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)), encoded (taskTerm (.targetMatch frame))]) state
      (encoded (encodeOption expansionTerm (some (expandTargetMatch environment outer frame)))) := by
  let free := environment.free.entriesOn footprint
  let inputs := [encoded (environmentTerm environment free), encoded (taskTerm (.targetMatch frame))]
  let caller := callEnvironment .target inputs
  let snapshot := fields caller snapshotNames (snapshotValues environment free)
  let framed := fields snapshot targetNames (targetValues frame)
  let called := fields framed (steppedNames 2) (callValues frame.call)
  let context := fields called (steppedNames 3) (contextValues frame.call.context)
  let machine := fields context matcherNames (matcherValues frame.state)
  let selected (answer : GeneralScopedMatchMachine.Answer) :=
    ("target-trace", encoded (traceTerm answer.trace)) :: ("assignment", assignmentValue answer.assignment) :: machine
  let next (answer : GeneralScopedMatchMachine.Answer) := ("next", number (frame.cursor + 1)) :: selected answer
  let later (answer : GeneralScopedMatchMachine.Answer) :=
    ("later", encoded (taskTerm (.targetMatch {frame with cursor := frame.cursor + 1}))) :: next answer
  let child (answer : GeneralScopedMatchMachine.Answer) :=
    ("child-bound", boundValue (frame.call.binders ++ frame.call.context.bound)) :: later answer
  let ambient := ("ambient", number frame.call.context.bound.length) :: machine
  let depth := ("depth", number frame.call.binders.length) :: ambient
  let requested := ("request", requestValue (targetRequest frame.call frame.target)) :: depth
  let advanced := ("advanced", matcherValue (GeneralScopedMatchMachine.tick (targetRequest frame.call frame.target) frame.state)) :: requested
  have wire : encoded (encodeOption expansionTerm (some (expandTargetMatch environment outer frame))) =
      match frame.state.answers[frame.cursor]? with
      | some answer => if checkTypedAssignment environment frame.call.context answer.assignment
          then applySubst (child answer) targetAccepted else applySubst (later answer) rootSkipped
      | none => if GeneralScopedMatchMachine.complete frame.state then applySubst machine emptyExpansion
          else applySubst advanced targetAdvanced := by
    simp only [expandTargetMatch]
    split
    · rename_i answer found
      simp only [found]
      split_ifs with checked
      · simp [targetAccepted, child, later, next, selected, machine, context, called, framed, fields, matcherNames,
          matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, applySubst,
          applySubst.applySubstList, Subst.lookup, expansionTerm, taskTerm, resultTerm, goalTerm, eventTerm,
          encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · simp [rootSkipped, later, next, selected, applySubst, applySubst.applySubstList, Subst.lookup,
          expansionTerm, encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · rename_i found
      simp only [found]
      split_ifs with finished
      · simp [emptyExpansion, applySubst, applySubst.applySubstList, expansionTerm,
          encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · simp [targetAdvanced, advanced, requested, depth, ambient, machine, context, called, framed,
          fields, matcherNames, matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues,
          applySubst, applySubst.applySubstList, Subst.lookup, expansionTerm, taskTerm, targetRequest,
          encodeOption, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  rw [wire]
  apply helper_call runtime agreement .target [] state inputs inputs _ rfl (by simp [inputs])
  apply nested_branch_returns runtime .target 0 (by decide) caller snapshot state
    (encoded (environmentTerm environment free)) (nestedBody .target 1)
  · change PureReturns runtime caller state (v "snapshot") state _
    simpa [caller, inputs, callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime caller state "snapshot"
  · exact snapshot_selected .target inputs environment free
  · apply nested_branch_returns runtime .target 1 (by decide) snapshot framed state
      (encoded (taskTerm (.targetMatch frame))) (nestedBody .target 2)
    · change PureReturns runtime snapshot state (v "task") state _
      simpa [snapshot, caller, inputs, fields, snapshotNames, snapshotValues,
        callEnvironment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime snapshot state "task"
    · rw [target_rows_one, target_shape]
      apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
      intro name member
      simp only [targetNames, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [snapshot, caller, inputs, fields, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
    · apply nested_branch_returns runtime .target 2 (by decide) framed called state (encoded (stepCallTerm frame.call)) (nestedBody .target 3)
      · change PureReturns runtime framed state (v "call") state _
        simpa [framed, fields, targetNames, targetValues, applySubst, Subst.lookup] using variable_returns runtime framed state "call"
      · rw [target_rows_two, call_shape]
        apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
        intro name member
        simp only [steppedNames, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [framed, snapshot, caller, inputs, fields, targetNames, targetValues, snapshotNames, snapshotValues,
            callEnvironment, Helper.names, Subst.lookup]
      · apply nested_branch_returns runtime .target 3 (by decide) called context state (encoded (contextTerm frame.call.context)) (nestedBody .target 4)
        · change PureReturns runtime called state (v "context") state _
          simpa [called, fields, steppedNames, callValues, applySubst, Subst.lookup] using variable_returns runtime called state "context"
        · rw [target_rows_three, context_shape]
          apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
          intro name member
          simp only [steppedNames, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [called, framed, snapshot, caller, inputs, fields, steppedNames, callValues, targetNames, targetValues,
              snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
        · apply nested_branch_returns runtime .target 4 (by decide) context machine state (matcherValue frame.state) (nestedBody .target 5)
          · change PureReturns runtime context state (v "matcher") state _
            simpa [context, called, framed, fields, steppedNames, contextValues, callValues, targetNames, targetValues,
              applySubst, Subst.lookup] using variable_returns runtime context state "matcher"
          · rw [target_rows_four, matcher_shape]
            apply select_fields_first _ _ _ _ _ _ (by decide) (by decide) rfl
            intro name member
            simp only [matcherNames, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl <;>
              simp [context, called, framed, snapshot, caller, inputs, fields, steppedNames, contextValues, callValues,
                targetNames, targetValues, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
          · rw [target_row_shape]
            have row := row_encoded_returns runtime lower answerTerm machine state frame.cursor frame.state.answers
              (v "cursor") (v "answers") (by
                simp [machine, context, called, framed, fields, matcherNames, matcherValues, steppedNames,
                  contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup])
            cases found : frame.state.answers[frame.cursor]? with
            | some answer =>
                apply branch_returns runtime machine (selected answer) state _
                  (a "Some" [encoded (answerTerm answer)]) targetAnswerCases targetAnswerBody
                · simpa only [found, encodeOption, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using row
                · simp [targetAnswerCases, answerTerm, RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
                    encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected, machine,
                    context, called, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues, steppedNames,
                    contextValues, callValues, targetNames, targetValues, snapshotNames, snapshotValues, callEnvironment,
                    Helper.names, Subst.lookup]
                · unfold targetAnswerBody
                  apply named_let_returns runtime (selected answer) state "next" _ _ _ _
                  · simp [selected, machine, context, called, framed, snapshot, caller, inputs, fields, matcherNames,
                      matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, snapshotNames,
                      snapshotValues, callEnvironment, Helper.names, Subst.lookup]
                  · apply add_returns runtime agreement (selected answer) state frame.cursor 1
                    · simpa [selected, machine, context, called, framed, fields, matcherNames, matcherValues, steppedNames,
                        contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup] using
                        variable_returns runtime (selected answer) state "cursor"
                    · exact grounded_returns runtime (selected answer) state _
                  · change PureReturns runtime (next answer) state (a "let" [v "later", targetLater,
                      a "if" [rootChecked, a "let" [v "child-bound", a "gslt:automata:append" [v "binders", v "bound"], targetAccepted], rootSkipped]]) state _
                    apply named_let_returns runtime (next answer) state "later" _ _ _ _
                    · simp [next, selected, machine, context, called, framed, snapshot, caller, inputs, fields, matcherNames,
                        matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, snapshotNames,
                        snapshotValues, callEnvironment, Helper.names, Subst.lookup]
                    · have returned := PureData.template_return runtime (next answer) state targetLater (by
                        unfold targetLater
                        frame_template runtime agreement)
                      simpa [targetLater, next, selected, machine, context, called, framed, fields, matcherNames, matcherValues,
                        steppedNames, contextValues, callValues, targetNames, targetValues, applySubst, applySubst.applySubstList,
                        Subst.lookup, taskTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
                    · change PureReturns runtime (later answer) state (a "if" [rootChecked,
                        a "let" [v "child-bound", a "gslt:automata:append" [v "binders", v "bound"], targetAccepted], rootSkipped]) state _
                      have tested := lower.assignment (later answer) state environment.language free frame.call.context.bound
                        frame.call.context.rule frame.call.context.spec answer.assignment
                        (v "declarations") (v "free") (v "bound") (v "rule") (v "spec") (v "assignment") (by
                          simp [later, next, selected, machine, context, called, framed, snapshot, fields, matcherNames,
                            matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues,
                            snapshotNames, snapshotValues, applySubst, Subst.lookup])
                      have same := ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
                        frame.call.context.bound frame.call.context.rule frame.call.context.spec answer.assignment footprint (covers answer found)
                      rw [same] at tested
                      change PureReturns runtime (later answer) state rootChecked state
                        (Effects.boolean (checkTypedAssignment environment frame.call.context answer.assignment)) at tested
                      apply bool_if_returns runtime (later answer) state rootChecked _ _ rootSkipped _ tested
                      cases checked : checkTypedAssignment environment frame.call.context answer.assignment with
                      | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          have returned := PureData.template_return runtime (later answer) state rootSkipped (by
                            unfold rootSkipped
                            frame_template runtime agreement)
                          simpa only [found, checked, Bool.false_eq_true, ↓reduceIte] using returned
                      | true =>
                          simp only [↓reduceIte]
                          apply named_let_returns runtime (later answer) state "child-bound" _ _ _ _
                          · simp [later, next, selected, machine, context, called, framed, snapshot, caller, inputs,
                              fields, matcherNames, matcherValues, steppedNames, contextValues, callValues, targetNames,
                              targetValues, snapshotNames, snapshotValues, callEnvironment, Helper.names, Subst.lookup]
                          · apply append_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm
                              (later answer) state frame.call.binders frame.call.context.bound
                            simp [later, next, selected, machine, context, called, framed, fields, matcherNames, matcherValues,
                              steppedNames, contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup]
                          · change PureReturns runtime (child answer) state targetAccepted state _
                            have returned := PureData.template_return runtime (child answer) state targetAccepted (by
                              unfold targetAccepted
                              frame_template runtime agreement)
                            simpa only [found, checked, ↓reduceIte] using returned
            | none =>
                apply branch_returns runtime machine machine state _ (.symbol "None") targetAnswerCases targetStopBody
                · simpa only [found, encodeOption, encoded, CettaWireAtom.encode] using row
                · simp [targetAnswerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · unfold targetStopBody
                  have tested := lower.complete machine state frame.state (v "matcher") (by
                    simp [machine, context, called, framed, fields, matcherNames, matcherValues, steppedNames,
                      contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup])
                  apply bool_if_returns runtime machine state _ _ _ _ _ tested
                  cases finished : GeneralScopedMatchMachine.complete frame.state with
                  | true =>
                      simp only [↓reduceIte]
                      have returned := PureData.template_return runtime machine state emptyExpansion (by
                        unfold emptyExpansion
                        frame_template runtime agreement)
                      simpa only [found, finished, ↓reduceIte] using returned
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      apply PureData.let_bindings_return (final := advanced) (pairs := targetPairs)
                      · unfold targetPairs
                        apply PureData.BindingsReturn.cons (bound := ambient)
                        · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm machine state frame.call.context.bound
                          simp [machine, context, called, framed, fields, matcherNames, matcherValues, steppedNames,
                            contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup]
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, ambient, machine,
                            context, called, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues, steppedNames,
                            contextValues, callValues, targetNames, targetValues, snapshotNames, snapshotValues, callEnvironment,
                            Helper.names, Subst.lookup]
                        · apply PureData.BindingsReturn.cons (bound := depth)
                          · apply length_encoded_returns runtime lower InferenceCettaWire.AuthoredRule.typeTerm ambient state frame.call.binders
                            simp [ambient, machine, context, called, framed, fields, matcherNames, matcherValues, steppedNames,
                              contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup]
                          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, depth, ambient, machine,
                              context, called, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues, steppedNames,
                              contextValues, callValues, targetNames, targetValues, snapshotNames, snapshotValues, callEnvironment,
                              Helper.names, Subst.lookup]
                          · apply PureData.BindingsReturn.cons (bound := requested) (value := requestValue (targetRequest frame.call frame.target))
                            · have returned := PureData.template_return runtime depth state targetRequestCode (by
                                unfold targetRequestCode
                                frame_template runtime agreement)
                              simpa [targetRequestCode, depth, ambient, machine, context, called, framed, fields, matcherNames,
                                matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, applySubst,
                                applySubst.applySubstList, Subst.lookup, targetRequest, requestValue,
                                RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, GeneralPremise.Context.site,
                                InferenceCettaWire.AuthoredRule.siteTerm, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
                            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, requested, depth, ambient,
                                machine, context, called, framed, snapshot, caller, inputs, fields, matcherNames, matcherValues,
                                steppedNames, contextValues, callValues, targetNames, targetValues, snapshotNames, snapshotValues,
                                callEnvironment, Helper.names, Subst.lookup]
                            · apply PureData.BindingsReturn.cons (bound := advanced)
                              · apply lower.tick requested state (targetRequest frame.call frame.target) frame.state
                                simp [requested, depth, ambient, machine, context, called, framed, fields, matcherNames,
                                  matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, applySubst, Subst.lookup]
                              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, advanced, requested, depth,
                                  ambient, machine, context, called, framed, snapshot, caller, inputs, fields, matcherNames,
                                  matcherValues, steppedNames, contextValues, callValues, targetNames, targetValues, snapshotNames,
                                  snapshotValues, callEnvironment, Helper.names, Subst.lookup]
                              · exact PureData.BindingsReturn.nil advanced state
                      · have returned := PureData.template_return runtime advanced state targetAdvanced (by
                          unfold targetAdvanced
                          frame_template runtime agreement)
                        simpa only [found, finished, Bool.false_eq_true, ↓reduceIte] using returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingTargetExpand


section MatchingReachable
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem root_reachable_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (frame : RootMatchFrame environment outer)
    (covered : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state (a Helper.root.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)), encoded (taskTerm (.rootMatch frame))]) state
      (encoded (encodeOption expansionTerm (some (expandRootMatch environment outer frame)))) := by
  apply root_match_expanded_returns runtime agreement lower state environment footprint outer frame
  intro answer found name occurs
  have within := GeneralScopedMatchMachine.matcher_answer_free_within (rootRequest frame) frame.state frame.reachable answer
    (List.mem_of_getElem? found) footprint (by intro entry member; cases member) covered
  rcases List.mem_flatMap.mp occurs with ⟨entry, member, occurs⟩
  exact within entry member name occurs

theorem target_reachable_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (frame : TargetMatchFrame environment outer)
    (before : assignmentFreeWithin footprint frame.call.initial)
    (covered : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state (a Helper.target.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)), encoded (taskTerm (.targetMatch frame))]) state
      (encoded (encodeOption expansionTerm (some (expandTargetMatch environment outer frame)))) := by
  apply target_match_expanded_returns runtime agreement lower state environment footprint outer frame
  intro answer found name occurs
  have within := GeneralScopedMatchMachine.matcher_answer_free_within (targetRequest frame.call frame.target) frame.state frame.reachable answer
    (List.mem_of_getElem? found) footprint before covered
  rcases List.mem_flatMap.mp occurs with ⟨entry, member, occurs⟩
  exact within entry member name occurs

theorem frame_captured_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (helper : Helper)
    (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw runtime agreement helper index
    omega
  · cases helper <;> decide
  · have emptyFunction : applySubst [] = (id : Atom → Atom) :=
      funext Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil
    rw [emptyFunction, List.map_id]
    exact captured.symm
  · exact returned

theorem frame_captured_completed_iff (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (helper : Helper)
    (caller : Subst) (state after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer)
    (answers input output : List Atom) :
    (∃ fuel, run runtime fuel {state, control := .evaluate caller (a helper.head arguments)} =
      .complete after answers input output) ↔
      after = state ∧ answers = [answer] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime caller state state _ _
    (frame_captured_returns runtime agreement helper caller state arguments values answer length captured returned)
    after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingReachable


section MatchingFootprint
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem root_body_delivered_within_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (index : Nat)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type sourcePattern)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured : Assignment)
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left sourcePattern trace captured)
    (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
    (completed : Assignment) (history : List Event)
    (valid : PremisesHold environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured completed history)
    (tail : Continuation environment (.root bound type sourcePattern index) outer)
    (stored : assignmentFreeWithin footprint completed) :
    PureReturns runtime [] state (a Helper.body.head
      [encoded (environmentTerm environment (environment.free.entriesOn footprint)),
       encoded (resultTerm (.premises completed history valid)),
       encoded (continuationTerm (.rootBody bound type sourcePattern index rule spec declared specified admitted sorted
         trace captured matched capturedTyped tail))]) state
      (encoded (encodeOption expansionTerm (some (delivered environment outer (.premises completed history valid)
        (.rootBody bound type sourcePattern index rule spec declared specified admitted sorted
          trace captured matched capturedTyped tail))))) := by
  apply root_body_delivered_returns runtime agreement lower state environment footprint outer bound type sourcePattern
    index rule spec declared specified admitted sorted trace captured matched capturedTyped completed history valid tail
  intro target success
  exact ScopedReflectiveExecution.selected_reduct_free_within footprint environment.reflection
    rule spec admitted bound.length completed target stored success


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingFootprint


section MatchingAssemblySource
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Assembly

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)

abbrev program : Program := RuleExecutionProgram.scopedMachineProgram

def retainedDeclaration : Atom → Bool
  | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => ownedHeads head
  | _ => false

theorem retained_equations :
    sourceProgram.equations.filter (fun equation => ownedHeads equation.head) =
      program.equations.filter (fun equation => ownedHeads equation.head) := by
  rfl

theorem retained_declarations :
    sourceProgram.declarations.filter retainedDeclaration =
      program.declarations.filter retainedDeclaration := by
  rfl

theorem source_without_initializers : program.initializers = [] := by rfl

theorem source_equation_count : program.equations.length = 224 := RuleExecutionProgram.scoped_machine_equation_count


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Assembly
end MatchingAssemblySource


section MatchingAssemblyAgreement
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Assembly

open SpaceSemantics (Program)
open Eval

theorem frame_owned_agreement : ProgramAgreementOn ownedHeads sourceProgram program := by
  apply programAgreementOn_of_retained_rows
  · exact retained_equations
  · exact retained_declarations

theorem frame_owned_agreement_in_extension (target : Program)
    (preserves : ProgramAgreementOn ownedHeads program target) :
    ProgramAgreementOn ownedHeads sourceProgram target where
  dispatch head supported :=
    (frame_owned_agreement.dispatch head supported).trans (preserves.dispatch head supported)
  demand head index supported :=
    (frame_owned_agreement.demand head index supported).trans (preserves.demand head index supported)
  bodies head values supported :=
    (frame_owned_agreement.bodies head values supported).trans (preserves.bodies head values supported)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Assembly
end MatchingAssemblyAgreement


section MatchingMechanical
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem frame_retained_equations :
    sourceProgram.equations.filter (fun equation => ownedHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => ownedHeads equation.head) := by
  rfl

theorem frame_retained_declarations :
    sourceProgram.declarations.filter (retainedCallDeclaration ownedHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration ownedHeads) := by
  rfl

theorem frame_agreement : ProgramAgreementOn ownedHeads sourceProgram RuleExecutionProgram.scopedMachineProgram :=
  programAgreementOn_of_retained_rows _ _ _ frame_retained_equations frame_retained_declarations

theorem row_returns (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, termListValue values]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?)) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.row_returns caller state index values one two captured

theorem length_returns (caller : Subst) (state : State) (values : List Term) (input : Atom)
    (captured : applySubst caller input = termListValue values) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:length" [input]) state (number values.length) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.length_returns caller state values input captured

theorem append_returns (caller : Subst) (state : State) (left right : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [termListValue left, termListValue right]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:automata:append" [one, two]) state (termListValue (left ++ right)) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.append_returns caller state left right one two captured

theorem start_returns (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom)
    (captured : applySubst caller input = requestValue request) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (matcherValue (GeneralScopedMatchMachine.start request)) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.start_returns caller state request input captured

theorem tick_returns (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [requestValue request, matcherValue machine]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (matcherValue (GeneralScopedMatchMachine.tick request machine)) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.tick_returns caller state request machine one two captured

theorem complete_returns (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom)
    (captured : applySubst caller input = matcherValue machine) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) :=
  RuleInstantiationExecution.GeneralExecution.Mechanical.complete_returns caller state machine input captured


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical
end MatchingMechanical


section MatchingTrajectory
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def frameCall (environment : Environment) (free : List (String × TypeExpr)) {outer : Goal} :
    Task environment outer → Option Atom
  | .rootMatch frame => some (a Helper.root.head
      [encoded (environmentTerm environment free), encoded (taskTerm (.rootMatch frame))])
  | .targetMatch frame => some (a Helper.target.head
      [encoded (environmentTerm environment free), encoded (taskTerm (.targetMatch frame))])
  | .deliver result continuation =>
      match continuation with
      | .rootBody _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => some (a Helper.body.head
          [encoded (environmentTerm environment free), encoded (resultTerm result),
           encoded (continuationTerm continuation)])
      | .stepped _ _ => some (a Helper.stepped.head
          [encoded (environmentTerm environment free), encoded (resultTerm result),
           encoded (continuationTerm continuation)])
      | _ => none
  | _ => none

theorem frame_expanded_within_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (task : Task environment outer) (code : Atom)
    (supported : frameCall environment (environment.free.entriesOn footprint) task = some code)
    (within : GeneralPremise.Execution.taskFreeWithin footprint task) :
    PureReturns runtime [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment outer task)))) := by
  cases task with
  | evaluate goal continuation => cases supported
  | query request matcher cursor continuation => cases supported
  | scanChildren bound type sourcePattern limit cursor continuation => cases supported
  | rootMatch frame =>
      cases Option.some.inj supported
      exact root_reachable_expanded_returns runtime agreement lower state environment footprint outer frame within.1
  | targetMatch frame =>
      cases Option.some.inj supported
      exact target_reachable_expanded_returns runtime agreement lower state environment footprint outer frame
        within.1.2.1 within.2.2.2.1
  | deliver result continuation =>
      cases continuation with
      | done goal => cases supported
      | nextPremise context premise premises initial continuation => cases supported
      | prepend context premise premises initial middle event valid continuation => cases supported
      | quantifier context collection parameter body initial kind elements read continuation => cases supported
      | element context parameter body index element elements initial typed continuation => cases supported
      | prependElement context parameter body index element elements initial middle event typed valid continuation =>
          cases supported
      | searchedRoot bound type sourcePattern index limit earlier continuation => cases supported
      | rootBody bound type sourcePattern index rule spec declared specified admitted sorted trace captured
          matched typed continuation =>
          cases result with
          | premises completed history valid =>
              cases Option.some.inj supported
              exact root_body_delivered_within_returns runtime agreement lower state environment footprint outer
                bound type sourcePattern index rule spec declared specified admitted sorted trace captured
                matched typed completed history valid continuation within.1.2
      | stepped call continuation =>
          cases Option.some.inj supported
          exact stepped_delivered_returns runtime agreement lower state environment
            (environment.free.entriesOn footprint) outer call result continuation

theorem root_run_frame_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (index fuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) fuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns runtime [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.root bound type sourcePattern index) task)))) := by
  apply frame_expanded_within_returns runtime agreement lower state environment
    (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider) _ task code supported
  exact (GeneralPremise.Execution.root_run_finite_free_within environment bound type sourcePattern index fuel
    (Query.DynamicOutputsFreeWithin.of_unregistered _ environment finiteProvider)).1 task member

theorem root_run_frame_expanded_in_assembly_returns (lower : LowerOperations Assembly.program)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (index fuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) fuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns Assembly.program [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.root bound type sourcePattern index) task)))) :=
  root_run_frame_expanded_returns Assembly.program Assembly.frame_owned_agreement lower state environment finiteProvider bound type
    sourcePattern index fuel task code member supported

theorem steps_run_frame_expanded_returns (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (limit fuel : Nat)
    (task : Task environment (.steps bound type sourcePattern limit)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.steps bound type sourcePattern limit) fuel
      (start environment (.steps bound type sourcePattern limit))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns runtime [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.steps bound type sourcePattern limit) task)))) := by
  apply frame_expanded_within_returns runtime agreement lower state environment
    (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider) _ task code supported
  exact (GeneralPremise.Execution.steps_run_finite_free_within environment bound type sourcePattern limit fuel
    (Query.DynamicOutputsFreeWithin.of_unregistered _ environment finiteProvider)).1 task member

theorem root_run_frame_completed_iff (runtime : Program)
    (agreement : ProgramAgreementOn ownedHeads sourceProgram runtime) (lower : LowerOperations runtime)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (index prefixFuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) prefixFuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel {state, control := .evaluate [] code} = .complete after answers input output) ↔
      after = state ∧
      answers = [encoded (encodeOption expansionTerm
        (some (expand environment (.root bound type sourcePattern index) task)))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state code _
    (root_run_frame_expanded_returns runtime agreement lower state environment finiteProvider bound type sourcePattern index prefixFuel
      task code member supported) after answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames
end MatchingTrajectory


section MatchingConsumer
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Consumer

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

theorem lower_operations_of_checkers
    (assignment : ∀ (caller : Subst) (state : State) (language : LanguageDef)
      (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec)
      (assignment : Assignment) (one two three four five six : Atom),
      [one, two, three, four, five, six].map (applySubst caller) =
        [declarationsValue language, freeValue free, boundValue bound, ruleValue rule, specValue spec, assignmentValue assignment] →
      PureReturns RuleExecutionProgram.scopedMachineProgram caller state
        (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
        (Effects.boolean (ConditionalEquationExecution.checkAssignment language (FreeTypeContext.ofList free) bound rule spec assignment)))
    (sorted : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
      (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) (one two three four five : Atom),
      [one, two, three, four, five].map (applySubst caller) =
        [declarationsValue language, freeValue free, boundValue bound, typeValue type, patternValue pattern] →
      PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:open-well-sorted" [one, two, three, four, five]) state
        (Effects.boolean (checkOpenPatternWellSorted language (FreeTypeContext.ofList free) bound type pattern)))
    (selection : ∀ (caller : Subst) (state : State) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (one two : Atom),
      [one, two].map (applySubst caller) = [reflectionValue profile, ruleValue rule] →
      PureReturns RuleExecutionProgram.scopedMachineProgram caller state
        (a "gslt:premise:substitution-presentation" [one, two]) state (selectionValue profile rule))
    (reduct : ∀ (caller : Subst) (state : State) (profile : Reflection.ReflectionProfile)
      (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) (one two three four five : Atom),
      [one, two, three, four, five].map (applySubst caller) =
        [selectionValue profile rule, ruleValue rule, specValue spec, number ambient, assignmentValue assignment] →
      PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-reduct" [one, two, three, four, five]) state
        (patternOptionValue (reductWith? (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment))) :
    LowerOperations RuleExecutionProgram.scopedMachineProgram where
  row := Mechanical.row_returns
  length := Mechanical.length_returns
  append := Mechanical.append_returns
  start := Mechanical.start_returns
  tick := Mechanical.tick_returns
  complete := Mechanical.complete_returns
  assignment := assignment
  sorted := sorted
  selection := selection
  reduct := reduct

theorem frame_expanded_returns (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (state : State) (environment : Environment) (footprint : List String) (outer : Goal)
    (task : Task environment outer) (code : Atom)
    (supported : frameCall environment (environment.free.entriesOn footprint) task = some code)
    (within : GeneralPremise.Execution.taskFreeWithin footprint task) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment outer task)))) :=
  frame_expanded_within_returns RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement lower state environment
    footprint outer task code supported within

theorem root_run_frame_returns (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (index fuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) fuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.root bound type sourcePattern index) task)))) :=
  root_run_frame_expanded_returns RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement lower state environment finiteProvider bound type
    sourcePattern index fuel task code member supported

theorem steps_run_frame_returns (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (bound : List TypeExpr) (type : TypeExpr)
    (sourcePattern : Pattern) (limit fuel : Nat)
    (task : Task environment (.steps bound type sourcePattern limit)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.steps bound type sourcePattern limit) fuel
      (start environment (.steps bound type sourcePattern limit))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.steps bound type sourcePattern limit) task)))) :=
  steps_run_frame_expanded_returns RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement lower state environment finiteProvider bound type
    sourcePattern limit fuel task code member supported

theorem frame_captured_within_returns (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (helper : Helper) (caller : Subst) (state : State) (environment : Environment)
    (footprint : List String) (outer : Goal) (task : Task environment outer) (arguments values : List Atom)
    (supported : frameCall environment (environment.free.entriesOn footprint) task = some (a helper.head values))
    (within : GeneralPremise.Execution.taskFreeWithin footprint task)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a helper.head arguments) state
      (encoded (encodeOption expansionTerm (some (expand environment outer task)))) :=
  frame_captured_returns RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement helper caller state arguments values _
    length captured (frame_expanded_returns lower state environment footprint outer task _ supported within)

theorem frame_captured_within_completed_iff (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (helper : Helper) (caller : Subst) (state after : State) (environment : Environment)
    (footprint : List String) (outer : Goal) (task : Task environment outer) (arguments values : List Atom)
    (supported : frameCall environment (environment.free.entriesOn footprint) task = some (a helper.head values))
    (within : GeneralPremise.Execution.taskFreeWithin footprint task)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a helper.head arguments)} =
      .complete after answers input output) ↔
      after = state ∧
      answers = [encoded (encodeOption expansionTerm (some (expand environment outer task)))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedMachineProgram caller state state _ _
    (frame_captured_within_returns lower helper caller state environment footprint outer task arguments values
      supported within length captured) after answers input output

theorem root_run_frame_captured_completed_iff (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (helper : Helper) (caller : Subst) (state after : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (index prefixFuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (arguments values : List Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) prefixFuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task =
        some (a helper.head values))
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a helper.head arguments)} =
      .complete after answers input output) ↔
      after = state ∧
      answers = [encoded (encodeOption expansionTerm
        (some (expand environment (.root bound type sourcePattern index) task)))] ∧ input = [] ∧ output = [] :=
  frame_captured_completed_iff RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement helper caller state after arguments values _
    length captured (root_run_frame_returns lower state environment finiteProvider bound type sourcePattern index prefixFuel task _
      member supported) answers input output

theorem steps_run_frame_captured_completed_iff (lower : LowerOperations RuleExecutionProgram.scopedMachineProgram)
    (helper : Helper) (caller : Subst) (state after : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (limit prefixFuel : Nat)
    (task : Task environment (.steps bound type sourcePattern limit)) (arguments values : List Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.steps bound type sourcePattern limit) prefixFuel
      (start environment (.steps bound type sourcePattern limit))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task =
        some (a helper.head values))
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run RuleExecutionProgram.scopedMachineProgram fuel {state, control := .evaluate caller (a helper.head arguments)} =
      .complete after answers input output) ↔
      after = state ∧
      answers = [encoded (encodeOption expansionTerm
        (some (expand environment (.steps bound type sourcePattern limit) task)))] ∧ input = [] ∧ output = [] :=
  frame_captured_completed_iff RuleExecutionProgram.scopedMachineProgram Mechanical.frame_agreement helper caller state after arguments values _
    length captured (steps_run_frame_returns lower state environment finiteProvider bound type sourcePattern limit prefixFuel task _
      member supported) answers input output


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Consumer
end MatchingConsumer


section MatchingTypedPrepared
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AssembledLower

open SpaceSemantics (Program)
open Eval

private def MatchingTypedPrepared_preparedTail : Program where
  equations := premiseRuntimeProgram.equations.drop RuleExecutionProgram.program.equations.length
  declarations := premiseRuntimeProgram.declarations.drop RuleExecutionProgram.program.declarations.length
  initializers := premiseRuntimeProgram.initializers.drop RuleExecutionProgram.program.initializers.length
  facts := premiseRuntimeProgram.facts.drop RuleExecutionProgram.program.facts.length
  layout := premiseRuntimeProgram.layout.drop RuleExecutionProgram.program.layout.length

theorem base_append_prepared : RuleExecutionProgram.program.append MatchingTypedPrepared_preparedTail = premiseRuntimeProgram := by rfl

private def MatchingTypedPrepared_preparedHeads : List String :=
  ["gslt:premise:type-context-lookup", "gslt:premise:check-assignment",
    "gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:machine-deliver",
    "gslt:premise:machine-evaluate", "gslt:premise:machine-expand", "gslt:premise:constructor-declarations",
    "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:signature-candidates",
    "gslt:premise:signature", "gslt:premise:check-values", "gslt:premise:check-row", "gslt:premise:ground-at",
    "gslt:premise:ground-list-at", "gslt:premise:reflective-rules", "gslt:premise:reflective-presentations",
    "gslt:premise:presentation-named", "gslt:premise:substitution-presentation"]

def basePreparedHead (head : String) : Bool := head != "eval" && !(MatchingTypedPrepared_preparedHeads.contains head)

theorem base_prepared_closed : ProgramClosed basePreparedHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !basePreparedHead equation.head || codeWithin basePreparedHead equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem base_prepared_agreement :
    ProgramAgreementOn basePreparedHead RuleExecutionProgram.program premiseRuntimeProgram := by
  rw [← base_append_prepared]
  apply appended_program_agreement
  · intro equation member
    have checked : MatchingTypedPrepared_preparedTail.equations.all (fun equation => !basePreparedHead equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases allowed : basePreparedHead equation.head with
    | false => rfl
    | true => simp [allowed] at row
  · intro name types member
    have checked : MatchingTypedPrepared_preparedTail.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !basePreparedHead head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases allowed : basePreparedHead name with
    | false => rfl
    | true => simp [allowed] at row


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AssembledLower
end MatchingTypedPrepared


section MatchingCheckers
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval

private def MatchingCheckers_operationArities : List (String × Nat) :=
  [("gslt:premise:check-assignment", 6), ("gslt:premise:open-well-sorted", 5),
    ("gslt:premise:substitution-presentation", 2), ("gslt:rule:scope-reduct", 5)]

private theorem MatchingCheckers_raw_at (head : String) (arity index : Nat)
    (member : (head, arity) ∈ MatchingCheckers_operationArities) (bound : index < arity) :
    argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true := by
  have checked : MatchingCheckers_operationArities.all (fun operation =>
      (List.range operation.2).all (argumentIsRaw RuleExecutionProgram.scopedMachineProgram operation.1)) = true := by
    decide +kernel
  have row := List.all_eq_true.mp checked (head, arity) member
  exact List.all_eq_true.mp row index (List.mem_range.mpr bound)

private theorem MatchingCheckers_raw_arguments (head : String) (arity : Nat)
    (member : (head, arity) ∈ MatchingCheckers_operationArities) (arguments : List Atom)
    (length : arguments.length = arity) :
    ∀ index argument, arguments[index]? = some argument →
      argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true ∨ passiveArgument argument = true := by
  intro index argument picked
  exact Or.inl (MatchingCheckers_raw_at head arity index member (by
    have bound := (List.getElem?_eq_some_iff.mp picked).1
    simpa only [length] using bound))

private theorem MatchingCheckers_ordinary_dispatch (head : String) (arity : Nat)
    (member : (head, arity) ∈ MatchingCheckers_operationArities) :
    (ioHead head || StdLib.known head || RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == head)) = true := by
  have checked : MatchingCheckers_operationArities.all (fun operation =>
      ioHead operation.1 || StdLib.known operation.1 ||
        RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == operation.1)) = true := by decide +kernel
  exact List.all_eq_true.mp checked (head, arity) member

private theorem MatchingCheckers_selection_representation (selection : Option ReflectivePresentationDecl) :
    ScopedInstantiationExecution.operationValue selection =
      encoded (encodeOption InferenceCettaWire.AuthoredRule.reflectivePresentationTerm selection) := by
  cases selection <;> rfl

private theorem MatchingCheckers_pattern_option_representation (result : Option Pattern) :
    encoded (MatchAutomataBindingExecution.patternOptionTerm result) = patternOptionValue result := by
  cases result <;> rfl

theorem assignment_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (assignment : Assignment) (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [declarationsValue language, freeValue free, boundValue bound, ruleValue rule,
        specValue spec, assignmentValue assignment]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (FreeTypeContext.ofList free) bound rule spec assignment)) := by
  let capturedCaller : Subst :=
    [("one", declarationsValue language), ("two", freeValue free), ("three", boundValue bound),
      ("four", ruleValue rule), ("five", specValue spec), ("six", assignmentValue assignment)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five", v "six"].map
      (applySubst capturedCaller) =
      [declarationsValue language, freeValue free, boundValue bound, ruleValue rule,
        specValue spec, assignmentValue assignment] := by
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
    (MatchingCheckers_ordinary_dispatch _ 6 (by simp [MatchingCheckers_operationArities])) (by decide)
    (MatchingCheckers_raw_arguments _ 6 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (MatchingCheckers_raw_arguments _ 6 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem sorted_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [declarationsValue language, freeValue free, boundValue bound, typeValue type, patternValue pattern]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:premise:open-well-sorted" [one, two, three, four, five]) state
      (Effects.boolean (checkOpenPatternWellSorted language (FreeTypeContext.ofList free) bound type pattern)) := by
  let capturedCaller : Subst :=
    [("one", declarationsValue language), ("two", freeValue free), ("three", boundValue bound),
      ("four", typeValue type), ("five", patternValue pattern)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five"].map
      (applySubst capturedCaller) =
      [declarationsValue language, freeValue free, boundValue bound, typeValue type, patternValue pattern] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := DeclarationTyping.check_open_pattern_captured_returns capturedCaller state language
    free bound type pattern (v "one") (v "two") (v "three") (v "four") (v "five") capturedNames
  have prepared := path_of_closed_agreement AssembledLower.base_prepared_closed
    AssembledLower.base_prepared_agreement
    ⟨by
      change codeWithin AssembledLower.basePreparedHead
        (a "gslt:premise:open-well-sorted" [v "one", v "two", v "three", v "four", v "five"]) = true
      decide +kernel, rfl⟩ source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state
    "gslt:premise:open-well-sorted" [v "one", v "two", v "three", v "four", v "five"]
    [one, two, three, four, five] _
    (MatchingCheckers_ordinary_dispatch _ 5 (by simp [MatchingCheckers_operationArities])) (by decide)
    (MatchingCheckers_raw_arguments _ 5 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (MatchingCheckers_raw_arguments _ 5 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem selection_returns (caller : Subst) (state : State)
    (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [reflectionValue profile, ruleValue rule]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:premise:substitution-presentation" [one, two]) state (selectionValue profile rule) := by
  let capturedCaller : Subst := [("one", reflectionValue profile), ("two", ruleValue rule)]
  have capturedNames : [v "one", v "two"].map (applySubst capturedCaller) =
      [reflectionValue profile, ruleValue rule] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := substitution_presentation_captured_returns capturedCaller state profile rule
    (v "one") (v "two") capturedNames
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state
    "gslt:premise:substitution-presentation" [v "one", v "two"] [one, two] _
    (MatchingCheckers_ordinary_dispatch _ 2 (by simp [MatchingCheckers_operationArities])) (by decide)
    (MatchingCheckers_raw_arguments _ 2 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (MatchingCheckers_raw_arguments _ 2 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem reduct_returns (caller : Subst) (state : State)
    (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [selectionValue profile rule, ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:rule:scope-reduct" [one, two, three, four, five]) state
      (patternOptionValue (reductWith? (ScopedReflectiveExecution.binderOperation profile rule)
        rule spec ambient assignment)) := by
  let capturedCaller : Subst :=
    [("one", selectionValue profile rule), ("two", ruleValue rule), ("three", specValue spec),
      ("four", number ambient), ("five", assignmentValue assignment)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five"].map
      (applySubst capturedCaller) =
      [selectionValue profile rule, ruleValue rule, specValue spec, number ambient, assignmentValue assignment] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := ScopedInstantiationExecution.reduct_profile_captured_returns capturedCaller state profile
    rule spec ambient assignment [v "one", v "two", v "three", v "four", v "five"]
    (by simpa only [MatchingCheckers_selection_representation] using capturedNames)
  have actual := path_of_closed_agreement ScopedInstantiationExecution.runtime_closed
    ScopedInstantiationExecution.scoped_machine_agreement
    ⟨by
      change codeWithin ScopedInstantiationExecution.executionHeads
        (a "gslt:rule:scope-reduct" [v "one", v "two", v "three", v "four", v "five"]) = true
      decide +kernel, rfl⟩ source
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state
    "gslt:rule:scope-reduct" [v "one", v "two", v "three", v "four", v "five"]
    [one, two, three, four, five] _
    (MatchingCheckers_ordinary_dispatch _ 5 (by simp [MatchingCheckers_operationArities])) (by decide)
    (MatchingCheckers_raw_arguments _ 5 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (MatchingCheckers_raw_arguments _ 5 (by simp [MatchingCheckers_operationArities]) _ rfl)
    (capturedNames.trans captured.symm) (by simpa only [MatchingCheckers_pattern_option_representation] using actual)

theorem operations : LowerOperations RuleExecutionProgram.scopedMachineProgram :=
  Consumer.lower_operations_of_checkers assignment_returns sorted_returns selection_returns reduct_returns


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers
end MatchingCheckers

section MatchingNativeEndpoints
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Native
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralPremise.Execution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval

theorem frame_expanded_returns (state : State) (environment : Environment)
    (footprint : List String) (outer : Goal) (task : Task environment outer) (code : Atom)
    (supported : frameCall environment (environment.free.entriesOn footprint) task = some code)
    (within : GeneralPremise.Execution.taskFreeWithin footprint task) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment outer task)))) :=
  Consumer.frame_expanded_returns Checkers.operations state environment footprint outer task code supported within

theorem root_run_frame_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (index fuel : Nat)
    (task : Task environment (.root bound type sourcePattern index)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.root bound type sourcePattern index) fuel
      (start environment (.root bound type sourcePattern index))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.root bound type sourcePattern index) task)))) :=
  Consumer.root_run_frame_returns Checkers.operations state environment finiteProvider bound type sourcePattern index fuel
    task code member supported

theorem steps_run_frame_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (bound : List TypeExpr) (type : TypeExpr) (sourcePattern : Pattern) (limit fuel : Nat)
    (task : Task environment (.steps bound type sourcePattern limit)) (code : Atom)
    (member : task ∈ (GeneralPremise.Execution.run environment (.steps bound type sourcePattern limit) fuel
      (start environment (.steps bound type sourcePattern limit))).agenda)
    (supported : frameCall environment
      (environment.free.entriesOn (sourcePattern.freeFvarNames ++ providerFreeNames environment.provider)) task = some code) :
    PureReturns RuleExecutionProgram.scopedMachineProgram [] state code state
      (encoded (encodeOption expansionTerm (some (expand environment (.steps bound type sourcePattern limit) task)))) :=
  Consumer.steps_run_frame_returns Checkers.operations state environment finiteProvider bound type sourcePattern limit fuel
    task code member supported
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.MatcherFrames.Native
end MatchingNativeEndpoints
