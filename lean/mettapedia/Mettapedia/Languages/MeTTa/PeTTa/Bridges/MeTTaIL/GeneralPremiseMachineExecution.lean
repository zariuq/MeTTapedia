import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Environment
import Mettapedia.Languages.MeTTa.PeTTa.CodeSupportAlgebra

/-! Reflective rule selection and transport for the original premise operations. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval Effects
open scoped ProgramQuotation

private def extendedPreparedReflectionSelection : Program := RuleExecutionProgram.premiseReflectionSelectionProgram

private def extendedPreviousProgram : Program := Base.runtime

private def extendedRuntime : Program := extendedPreviousProgram.append extendedPreparedReflectionSelection


def premiseRuntimeProgram : Program := extendedRuntime

def premiseExecutionHeads (head : String) : Bool :=
  (["+", "-", "<", "==", ">=", "Binding", "ContextualValue", "FVar", "FiniteCollection", "ForAll", "GrammarTypingV1", "GrammarTypingWrappedV1", "LCons", "LNil", "None", "OccurrenceAssignment", "PApp", "PCollection", "PLam", "PMultiLam", "PSubst", "PremiseAnswer", "PremiseCollectionProjection", "PremiseContext", "PremiseDeliver", "PremiseDone", "PremiseElement", "PremiseEvaluate", "PremiseExpansion", "PremiseGoal", "PremiseNext", "PremisePrepend", "PremisePrependElement", "PremiseProvider", "PremiseProviderRow", "PremiseQuantifiedAssignment", "PremiseQuantifiedEvent", "PremiseQuantifier", "PremiseReflection", "PremiseResult", "PremiseScanChildren", "PremiseSearchedRoot", "PremiseSignature", "PremiseSpecification", "PremisesAnswer", "PremisesGoal", "QuantifiedAnswer", "QuantifiedElement", "QuantifiedGoal", "RNone", "RecoveryAssignment", "ReflectivePresentation", "ReflectiveRule", "RootAnswer", "RootGoal", "RuleBindingSpec", "RuleDependency", "ScopedRewriteRuleV1", "Some", "StepsAnswer", "StepsGoal", "TArrow", "TBase", "TCollection", "TMultiBinder", "TermAbstraction", "TermMultiAbstraction", "TermSimple", "TypeBinding", "Var", "case", "gslt:automata:append", "gslt:automata:binding", "gslt:automata:length", "gslt:premise:canonical-binders", "gslt:premise:canonical-binders-list", "gslt:premise:check-assignment", "gslt:premise:check-row", "gslt:premise:check-values", "gslt:premise:constructor-declarations", "gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:ground-at", "gslt:premise:ground-list-at", "gslt:premise:machine-deliver", "gslt:premise:machine-evaluate", "gslt:premise:machine-expand", "gslt:premise:object-pattern", "gslt:premise:object-patterns", "gslt:premise:open-well-sorted", "gslt:premise:parameter-representation", "gslt:premise:parameter-type", "gslt:premise:presentation-named", "gslt:premise:reflective-presentations", "gslt:premise:reflective-rules", "gslt:premise:scope-bind", "gslt:premise:scope-collection", "gslt:premise:scope-local-value", "gslt:premise:scope-remove", "gslt:premise:scope-restore", "gslt:premise:signature", "gslt:premise:signature-candidates", "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:substitution-presentation", "gslt:premise:type-arguments", "gslt:premise:type-collection-declarations", "gslt:premise:type-constructors", "gslt:premise:type-context-lookup", "gslt:premise:type-elements", "gslt:premise:type-extend-count", "gslt:premise:type-has", "gslt:rule:lift-bvars", "gslt:rule:lift-bvars-list", "gslt:rule:row-at", "gslt:rule:scope-assignment", "gslt:rule:scope-index", "gslt:rule:scope-instantiate-value", "gslt:rule:scope-metadata-dependencies", "gslt:rule:scope-metadata-dependency-rows", "gslt:rule:scope-substitute", "gslt:rule:scope-substitute-list", "gslt:rule:scope-well-scoped", "gslt:rule:scope-well-scoped-list", "if", "let", "let*"]).contains head

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AssembledLower
open Eval
private local instance equationEq : DecidableEq SpaceSemantics.Equation := by
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

theorem premise_retained_equations :
    premiseRuntimeProgram.equations.filter (fun equation => premiseExecutionHeads equation.head) =
      RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => premiseExecutionHeads equation.head) := by
  decide +kernel

theorem premise_retained_declarations :
    premiseRuntimeProgram.declarations.filter (retainedCallDeclaration premiseExecutionHeads) =
      RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration premiseExecutionHeads) := by decide +kernel

theorem premise_agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ premise_retained_equations premise_retained_declarations

#print axioms premise_retained_equations
#print axioms premise_retained_declarations
#print axioms premise_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.AssembledLower

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval Effects
open scoped ProgramQuotation

private theorem program_closed_of_all (allowed : String → Bool) (program : Program)
    (binding : allowed "let" = true)
    (checked : program.equations.all (fun equation =>
      !allowed equation.head || codeWithin allowed equation.body) = true) :
    ProgramClosed allowed program := by
  constructor
  · exact binding
  · intro equation member supported
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem equations_checked_append (check : Equation → Bool) (first second : Program)
    (left : first.equations.all check = true) (right : second.equations.all check = true) :
    (first.append second).equations.all check = true := by
  simp only [Program.append, List.all_append, left, right, Bool.true_and]

private theorem premise_base_checked : RuleExecutionProgram.program.equations.all (fun equation =>
    !premiseExecutionHeads equation.head || codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_assignment_checked : RuleExecutionProgram.premiseAssignmentProgram.equations.all
    (fun equation => !premiseExecutionHeads equation.head ||
      codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_administration_checked : RuleExecutionProgram.premiseAdministrationProgram.equations.all
    (fun equation => !premiseExecutionHeads equation.head ||
      codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_environment_checked : RuleExecutionProgram.premiseEnvironmentProgram.equations.all
    (fun equation => !premiseExecutionHeads equation.head ||
      codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_ground_checked : RuleExecutionProgram.premiseGroundProgram.equations.all
    (fun equation => !premiseExecutionHeads equation.head ||
      codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_reflection_checked : RuleExecutionProgram.premiseReflectionSelectionProgram.equations.all
    (fun equation => !premiseExecutionHeads equation.head ||
      codeWithin premiseExecutionHeads equation.body) = true := by
  rfl

private theorem premise_equations_checked : premiseRuntimeProgram.equations.all (fun equation =>
    !premiseExecutionHeads equation.head || codeWithin premiseExecutionHeads equation.body) = true := by
  have administration := equations_checked_append _
    RuleExecutionProgram.premiseAssignmentProgram RuleExecutionProgram.premiseAdministrationProgram
    premise_assignment_checked premise_administration_checked
  have environment := equations_checked_append _
    (RuleExecutionProgram.premiseAssignmentProgram.append RuleExecutionProgram.premiseAdministrationProgram)
    RuleExecutionProgram.premiseEnvironmentProgram administration premise_environment_checked
  have ground := equations_checked_append _
    ((RuleExecutionProgram.premiseAssignmentProgram.append
      RuleExecutionProgram.premiseAdministrationProgram).append RuleExecutionProgram.premiseEnvironmentProgram)
    RuleExecutionProgram.premiseGroundProgram environment premise_ground_checked
  have previous := equations_checked_append _ RuleExecutionProgram.program
    (((RuleExecutionProgram.premiseAssignmentProgram.append
      RuleExecutionProgram.premiseAdministrationProgram).append
      RuleExecutionProgram.premiseEnvironmentProgram).append RuleExecutionProgram.premiseGroundProgram)
    premise_base_checked ground
  exact equations_checked_append _
    (RuleExecutionProgram.program.append
      (((RuleExecutionProgram.premiseAssignmentProgram.append
        RuleExecutionProgram.premiseAdministrationProgram).append
        RuleExecutionProgram.premiseEnvironmentProgram).append RuleExecutionProgram.premiseGroundProgram))
    RuleExecutionProgram.premiseReflectionSelectionProgram previous
    premise_reflection_checked

theorem premise_runtime_closed : ProgramClosed premiseExecutionHeads premiseRuntimeProgram :=
  program_closed_of_all premiseExecutionHeads premiseRuntimeProgram rfl premise_equations_checked

theorem premise_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram target)
    {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin premiseExecutionHeads code = true)
    (returned : PureReturns premiseRuntimeProgram caller state code state answer) :
    PureReturns target caller state code state answer :=
  path_of_closed_agreement premise_runtime_closed agreement ⟨supported, rfl⟩ returned

#print axioms premise_runtime_closed
#print axioms premise_returns_in_extension

private def extendedPreviousHeads (head : String) : Bool :=
  premiseExecutionHeads head && !(["gslt:premise:reflective-rules", "gslt:premise:reflective-presentations",
    "gslt:premise:presentation-named", "gslt:premise:substitution-presentation"].contains head)

private theorem program_closed_restrict (allowed further : String → Bool) (program : Program)
    (closed : ProgramClosed allowed program) (binding : further "let" = true)
    (checked : program.equations.all (fun equation =>
      !allowed equation.head || codeWithin further equation.body) = true) :
    ProgramClosed (fun head => allowed head && further head) program := by
  constructor
  · simp only [closed.binding, binding, Bool.true_and]
  · intro equation member supported
    have original := (Bool.and_eq_true_iff.mp supported).1
    have first := closed.bodies equation member original
    have row := List.all_eq_true.mp checked equation member
    have second : codeWithin further equation.body = true := by
      simpa only [original, Bool.not_true, Bool.false_or] using row
    rw [codeWithin_and, first, second]
    rfl

private def reflectionFreshHeads (head : String) : Bool :=
  !(["gslt:premise:reflective-rules", "gslt:premise:reflective-presentations",
    "gslt:premise:presentation-named", "gslt:premise:substitution-presentation"].contains head)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem extendedPrevious_fresh_checked : extendedPreviousProgram.equations.all (fun equation =>
    !premiseExecutionHeads equation.head || codeWithin reflectionFreshHeads equation.body) = true := by
  change (RuleExecutionProgram.program.equations ++
    (((RuleExecutionProgram.premiseAssignmentProgram.equations ++
      RuleExecutionProgram.premiseAdministrationProgram.equations) ++
      RuleExecutionProgram.premiseEnvironmentProgram.equations) ++
      RuleExecutionProgram.premiseGroundProgram.equations)).all
      (fun equation => !premiseExecutionHeads equation.head ||
        codeWithin reflectionFreshHeads equation.body) = true
  simp only [List.all_append, Bool.and_eq_true_iff]
  repeat' apply And.intro
  all_goals rfl

private theorem extendedPrevious_closed : ProgramClosed extendedPreviousHeads extendedPreviousProgram := by
  have wide : ProgramClosed premiseExecutionHeads extendedPreviousProgram := by
    constructor
    · exact premise_runtime_closed.binding
    · intro equation member supported
      apply premise_runtime_closed.bodies equation _ supported
      change equation ∈ extendedPreviousProgram.equations ++ extendedPreparedReflectionSelection.equations
      exact List.mem_append_left _ member
  exact program_closed_restrict premiseExecutionHeads reflectionFreshHeads extendedPreviousProgram wide rfl
    extendedPrevious_fresh_checked

private theorem extendedPrevious_agreement : ProgramAgreementOn extendedPreviousHeads extendedPreviousProgram premiseRuntimeProgram := by
  apply appended_program_agreement
  · intro equation member
    have checked : extendedPreparedReflectionSelection.equations.all (fun equation =>
        !extendedPreviousHeads equation.head) = true := by rfl
    have row := List.all_eq_true.mp checked equation member
    cases selected : extendedPreviousHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : extendedPreparedReflectionSelection.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !extendedPreviousHeads head
        | _ => true) = true := by rfl
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : extendedPreviousHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem premise_previous_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin extendedPreviousHeads code = true)
    (returned : PureReturns extendedPreviousProgram caller state code state answer) :
    PureReturns premiseRuntimeProgram caller state code state answer :=
  path_of_closed_agreement extendedPrevious_closed extendedPrevious_agreement ⟨supported, rfl⟩ returned

#print axioms extendedPrevious_closed
#print axioms extendedPrevious_agreement
#print axioms premise_previous_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval

private abbrev reflectionRuntime : Program := premiseRuntimeProgram
private abbrev reflectionA (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev reflectionV (name : String) : Atom := .var name
private abbrev reflectionEncoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev reflectionStringValue (name : String) : Atom := reflectionEncoded (.string name)
private abbrev reflectionNumber (value : Nat) : Atom := reflectionEncoded (.natural value)
private abbrev reflectionPatternValue (pattern : Pattern) : Atom := reflectionEncoded (InferenceCettaWire.encodePattern pattern)
private abbrev reflectionRuleValue (rule : RewriteRule) : Atom := reflectionEncoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
private abbrev reflectionTypesValue (types : List (String × TypeExpr)) : Atom :=
  reflectionEncoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm types)
private abbrev reflectionCollectionValue (kind : CollType) : Atom := reflectionEncoded (InferenceCettaWire.encodeCollectionType kind)
private def reflectionEquations (head : String) : List SpaceSemantics.Equation := reflectionRuntime.equations.filter (fun equation => equation.head == head)
private def reflectionCaseData (expression : Atom) (rows : SpaceSemantics.Cases) : Atom :=
  reflectionA "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]
private inductive reflectionEnvHelper where | reflectiveRules | reflectivePresentations | presentationNamed | substitutionPresentation
private def reflectionEnvHelper.head : reflectionEnvHelper → String
  | .reflectiveRules => "gslt:premise:reflective-rules"
  | .reflectivePresentations => "gslt:premise:reflective-presentations"
  | .presentationNamed => "gslt:premise:presentation-named"
  | .substitutionPresentation => "gslt:premise:substitution-presentation"
private def reflectionEnvHelper.names : reflectionEnvHelper → List String
  | .reflectiveRules | .reflectivePresentations => ["requested", "declarations"]
  | .presentationNamed => ["presentations", "requested"]
  | .substitutionPresentation => ["profile", "rule"]
private theorem reflectionCaptured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem reflectionBool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns reflectionRuntime caller state condition state (Effects.boolean value))
    (returned : PureReturns reflectionRuntime caller state (if value then yes else no) state answer) :
    PureReturns reflectionRuntime caller state (reflectionA "if" [condition, yes, no]) state answer := by
  apply if_returns reflectionRuntime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem reflectionBranch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns reflectionRuntime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns reflectionRuntime selected state body state answer) :
    PureReturns reflectionRuntime caller state
      (reflectionA "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns reflectionRuntime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private def reflectionEnvEquation (helper : reflectionEnvHelper) : SpaceSemantics.Equation :=
  (reflectionEquations helper.head)[0]'(by cases helper <;> decide +kernel)
private def reflectionEnvCaptured (helper : reflectionEnvHelper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

set_option maxRecDepth 4096 in
private theorem reflectionEnv_clause (helper : reflectionEnvHelper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses reflectionRuntime helper.head values =
      [.evaluate (reflectionEnvCaptured helper values) (reflectionEnvEquation helper).body] :=
  PureData.named_equation_clause reflectionRuntime helper.head (reflectionEnvEquation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> rfl)
    (by cases helper <;> decide) length

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem reflectionEnv_raw (helper : reflectionEnvHelper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw reflectionRuntime helper.head index = true := by
  cases helper <;> simp only [reflectionEnvHelper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> first | omega | rfl

private theorem reflectionEnv_call (helper : reflectionEnvHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns reflectionRuntime (reflectionEnvCaptured helper values) state (reflectionEnvEquation helper).body state answer) :
    PureReturns reflectionRuntime caller state (reflectionA helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return reflectionRuntime caller (reflectionEnvCaptured helper values) state state
    helper.head arguments (reflectionEnvEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> rfl)
  · intro index bounded
    apply reflectionEnv_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact reflectionEnv_clause helper values length
  · exact returned

private theorem reflectionEnv_capture (helper : reflectionEnvHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns reflectionRuntime [] state (reflectionA helper.head values) state answer) :
    PureReturns reflectionRuntime caller state (reflectionA helper.head arguments) state answer := by
  apply PureData.raw_capture_returns reflectionRuntime [] caller state state helper.head values arguments answer
    (by cases helper <;> rfl) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact reflectionEnv_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem reflectionEnv_string_equal_returns (caller : Subst) (state : State)
    (left right one two : String)
    (first : applySubst caller (reflectionV one) = reflectionStringValue left)
    (second : applySubst caller (reflectionV two) = reflectionStringValue right) :
    PureReturns reflectionRuntime caller state (reflectionA "==" [reflectionV one, reflectionV two]) state
      (Effects.boolean (decide (left = right))) := by
  have tested := CettaWireAtom.equality_captured_returns reflectionRuntime caller state
    (.string left) (.string right) one two first second
  have same : Term.string left = Term.string right ↔ left = right := by simp
  simpa only [same] using tested

private def reflectionMachineDataHeads : List String := ["Some", "LCons", "ReflectiveRule", "ReflectivePresentation"]

private theorem reflectionMachine_data_template (head : String) (arguments : List Atom)
    (supported : head ∈ reflectionMachineDataHeads)
    (children : ∀ child ∈ arguments, PureData.Template reflectionRuntime child) :
    PureData.Template reflectionRuntime (reflectionA head arguments) := by
  have checked : reflectionMachineDataHeads.all (fun name => decide
      ((ioHead name || StdLib.known name || reflectionRuntime.equations.any (·.head == name)) = false ∧
        name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])) = true := by
    rfl
  have row := List.all_eq_true.mp checked head supported
  rw [decide_eq_true_eq] at row
  exact .constructor head arguments row.1 row.2 children

local macro "machine_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply reflectionMachine_data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def reflectionAssignmentRuleCaller (rule : RewriteRule) (caller : Subst) : Subst :=
  [("bindings", reflectionEncoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)),
    ("right", reflectionPatternValue rule.right), ("left", reflectionPatternValue rule.left),
    ("premises", reflectionEncoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)),
    ("types", reflectionTypesValue rule.typeContext), ("ruleName", reflectionStringValue rule.name)] ++ caller




attribute [local simp] reflectionA reflectionV reflectionEncoded reflectionNumber reflectionPatternValue

private abbrev reflectionReflectiveRulesValue (declarations : List ReflectiveRuleDecl) : Atom :=
  reflectionEncoded (encodeList reflectiveRuleTerm declarations)
private def reflectionReflectiveRulesConsData : Atom :=
  reflectionA "LCons" [reflectionA "ReflectiveRule" [reflectionV "name", reflectionV "rewrite", reflectionV "matching", reflectionV "substitution"], reflectionV "filtered"]
private def reflectionReflectiveRulesIncludedBody : Atom :=
  reflectionA "let" [reflectionV "filtered", reflectionA "gslt:premise:reflective-rules" [reflectionV "requested", reflectionV "rest"], reflectionReflectiveRulesConsData]
private def reflectionReflectiveRulesConsBody : Atom :=
  reflectionA "if" [reflectionA "==" [reflectionV "rewrite", reflectionV "requested"], reflectionReflectiveRulesIncludedBody,
    reflectionA "gslt:premise:reflective-rules" [reflectionV "requested", reflectionV "rest"]]
private def reflectionReflectiveRulesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (reflectionA "LCons" [reflectionA "ReflectiveRule" [reflectionV "name", reflectionV "rewrite", reflectionV "matching", reflectionV "substitution"], reflectionV "rest"], reflectionReflectiveRulesConsBody),
    (reflectionV "bad", .symbol "LNil")]
private theorem reflectionReflectiveRules_shape : (reflectionEnvEquation .reflectiveRules).body =
    reflectionCaseData (reflectionV "declarations") reflectionReflectiveRulesCases := by rfl

/-- Filtering preserves physical declaration order, multiplicity and metadata. -/
theorem reflective_rules_returns (state : State) (requested : String) (declarations : List ReflectiveRuleDecl) :
    PureReturns reflectionRuntime [] state (reflectionA "gslt:premise:reflective-rules" [reflectionStringValue requested, reflectionReflectiveRulesValue declarations]) state
      (reflectionReflectiveRulesValue (declarations.filter fun declaration => declaration.rewriteRule == requested)) := by
  induction declarations with
  | nil =>
      let caller := reflectionEnvCaptured .reflectiveRules [reflectionStringValue requested, reflectionReflectiveRulesValue []]
      apply reflectionEnv_call .reflectiveRules [] state _ _ _ rfl (reflectionCaptured_closed _)
      rw [reflectionReflectiveRules_shape]
      apply reflectionBranch_returns caller caller state _ (.symbol "LNil") reflectionReflectiveRulesCases (.symbol "LNil") _
      · simpa [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup,
          reflectionReflectiveRulesValue, encodeList, CettaWireAtom.encode] using variable_returns reflectionRuntime caller state "declarations"
      · simp [reflectionReflectiveRulesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns reflectionRuntime caller state "LNil"
  | cons declaration declarations ih =>
      let caller := reflectionEnvCaptured .reflectiveRules [reflectionStringValue requested, reflectionReflectiveRulesValue (declaration :: declarations)]
      let selected := [("rest", reflectionReflectiveRulesValue declarations), ("substitution", reflectionStringValue declaration.substitutionPresentation), ("matching", reflectionStringValue declaration.matchingPresentation), ("rewrite", reflectionStringValue declaration.rewriteRule), ("name", reflectionStringValue declaration.name)] ++ caller
      let filtered := ("filtered", reflectionReflectiveRulesValue (declarations.filter fun declaration => declaration.rewriteRule == requested)) :: selected
      apply reflectionEnv_call .reflectiveRules [] state _ _ _ rfl (reflectionCaptured_closed _)
      rw [reflectionReflectiveRules_shape]
      apply reflectionBranch_returns caller selected state _ (reflectionReflectiveRulesValue (declaration :: declarations))
        reflectionReflectiveRulesCases reflectionReflectiveRulesConsBody _
      · simpa [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup] using
          variable_returns reflectionRuntime caller state "declarations"
      · simp [reflectionReflectiveRulesCases, reflectionReflectiveRulesValue, reflectiveRuleTerm, reflectionStringValue, encodeList,
          selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have tested := reflectionEnv_string_equal_returns selected state declaration.rewriteRule requested "rewrite" "requested"
          (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
        unfold reflectionReflectiveRulesConsBody
        apply reflectionBool_if_returns selected state _ (decide (declaration.rewriteRule = requested)) _ _ _ tested
        by_cases same : declaration.rewriteRule = requested
        · simp only [same, decide_true, ↓reduceIte, List.filter_cons]
          unfold reflectionReflectiveRulesIncludedBody
          apply let_returns reflectionRuntime selected filtered state state state (reflectionV "filtered")
            (reflectionA "gslt:premise:reflective-rules" [reflectionV "requested", reflectionV "rest"]) reflectionReflectiveRulesConsData
            (reflectionReflectiveRulesValue (declarations.filter fun declaration => declaration.rewriteRule == requested)) _
          · exact reflectionEnv_capture .reflectiveRules selected state _ _ _ rfl
              (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup]) ih
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              filtered, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup]
          · have templated : PureData.Template reflectionRuntime reflectionReflectiveRulesConsData := by
              unfold reflectionReflectiveRulesConsData
              machine_template
            simpa [reflectionReflectiveRulesConsData, reflectionReflectiveRulesValue, reflectiveRuleTerm, encodeList,
              filtered, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, applySubst.applySubstList,
              Subst.lookup, reflectionStringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return reflectionRuntime filtered state _ templated
        · have excluded : (declaration.rewriteRule == requested) = false := by simp [same]
          simp only [same, decide_false, List.filter_cons, excluded]
          exact reflectionEnv_capture .reflectiveRules selected state _ _ _ rfl
            (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup]) ih

theorem reflective_rules_captured_returns (caller : Subst) (state : State) (requested : String)
    (declarations : List ReflectiveRuleDecl) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [reflectionStringValue requested, reflectionReflectiveRulesValue declarations]) :
    PureReturns reflectionRuntime caller state (reflectionA "gslt:premise:reflective-rules" [one, two]) state
      (reflectionReflectiveRulesValue (declarations.filter fun declaration => declaration.rewriteRule == requested)) :=
  reflectionEnv_capture .reflectiveRules caller state _ _ _ rfl captured (reflective_rules_returns state requested declarations)

#print axioms reflective_rules_returns
#print axioms reflective_rules_captured_returns

private abbrev reflectionReflectivePresentationsValue (declarations : List ReflectivePresentationDecl) : Atom :=
  reflectionEncoded (encodeList InferenceCettaWire.AuthoredRule.reflectivePresentationTerm declarations)
private def reflectionReflectivePresentationsConsData : Atom :=
  reflectionA "LCons" [reflectionA "ReflectivePresentation" [reflectionV "name", reflectionV "processSort", reflectionV "nameSort", reflectionV "quote", reflectionV "drop", reflectionV "kind", reflectionV "unit", reflectionV "equation"], reflectionV "filtered"]
private def reflectionReflectivePresentationsIncludedBody : Atom :=
  reflectionA "let" [reflectionV "filtered", reflectionA "gslt:premise:reflective-presentations" [reflectionV "requested", reflectionV "rest"], reflectionReflectivePresentationsConsData]
private def reflectionReflectivePresentationsConsBody : Atom :=
  reflectionA "if" [reflectionA "==" [reflectionV "name", reflectionV "requested"], reflectionReflectivePresentationsIncludedBody,
    reflectionA "gslt:premise:reflective-presentations" [reflectionV "requested", reflectionV "rest"]]
private def reflectionReflectivePresentationsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (reflectionA "LCons" [reflectionA "ReflectivePresentation" [reflectionV "name", reflectionV "processSort", reflectionV "nameSort", reflectionV "quote", reflectionV "drop", reflectionV "kind", reflectionV "unit", reflectionV "equation"], reflectionV "rest"], reflectionReflectivePresentationsConsBody),
    (reflectionV "bad", .symbol "LNil")]
private theorem reflectionReflectivePresentations_shape : (reflectionEnvEquation .reflectivePresentations).body =
    reflectionCaseData (reflectionV "declarations") reflectionReflectivePresentationsCases := by rfl

/-- Filtering preserves physical declaration order, multiplicity and metadata. -/
theorem reflective_presentations_returns (state : State) (requested : String) (declarations : List ReflectivePresentationDecl) :
    PureReturns reflectionRuntime [] state (reflectionA "gslt:premise:reflective-presentations" [reflectionStringValue requested, reflectionReflectivePresentationsValue declarations]) state
      (reflectionReflectivePresentationsValue (declarations.filter fun declaration => declaration.name == requested)) := by
  induction declarations with
  | nil =>
      let caller := reflectionEnvCaptured .reflectivePresentations [reflectionStringValue requested, reflectionReflectivePresentationsValue []]
      apply reflectionEnv_call .reflectivePresentations [] state _ _ _ rfl (reflectionCaptured_closed _)
      rw [reflectionReflectivePresentations_shape]
      apply reflectionBranch_returns caller caller state _ (.symbol "LNil") reflectionReflectivePresentationsCases (.symbol "LNil") _
      · simpa [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup,
          reflectionReflectivePresentationsValue, encodeList, CettaWireAtom.encode] using variable_returns reflectionRuntime caller state "declarations"
      · simp [reflectionReflectivePresentationsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns reflectionRuntime caller state "LNil"
  | cons declaration declarations ih =>
      let caller := reflectionEnvCaptured .reflectivePresentations [reflectionStringValue requested, reflectionReflectivePresentationsValue (declaration :: declarations)]
      let selected := [("rest", reflectionReflectivePresentationsValue declarations), ("equation", reflectionStringValue declaration.quoteDropEquation), ("unit", reflectionStringValue declaration.parallelUnitConstructor), ("kind", reflectionCollectionValue declaration.parallelCollection), ("drop", reflectionStringValue declaration.dropConstructor), ("quote", reflectionStringValue declaration.quoteConstructor), ("nameSort", reflectionStringValue declaration.nameSort), ("processSort", reflectionStringValue declaration.processSort), ("name", reflectionStringValue declaration.name)] ++ caller
      let filtered := ("filtered", reflectionReflectivePresentationsValue (declarations.filter fun declaration => declaration.name == requested)) :: selected
      apply reflectionEnv_call .reflectivePresentations [] state _ _ _ rfl (reflectionCaptured_closed _)
      rw [reflectionReflectivePresentations_shape]
      apply reflectionBranch_returns caller selected state _ (reflectionReflectivePresentationsValue (declaration :: declarations))
        reflectionReflectivePresentationsCases reflectionReflectivePresentationsConsBody _
      · simpa [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup] using
          variable_returns reflectionRuntime caller state "declarations"
      · simp [reflectionReflectivePresentationsCases, reflectionReflectivePresentationsValue, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm, reflectionStringValue, reflectionCollectionValue, encodeList,
          selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have tested := reflectionEnv_string_equal_returns selected state declaration.name requested "name" "requested"
          (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
        unfold reflectionReflectivePresentationsConsBody
        apply reflectionBool_if_returns selected state _ (decide (declaration.name = requested)) _ _ _ tested
        by_cases same : declaration.name = requested
        · simp only [same, decide_true, ↓reduceIte, List.filter_cons]
          unfold reflectionReflectivePresentationsIncludedBody
          apply let_returns reflectionRuntime selected filtered state state state (reflectionV "filtered")
            (reflectionA "gslt:premise:reflective-presentations" [reflectionV "requested", reflectionV "rest"]) reflectionReflectivePresentationsConsData
            (reflectionReflectivePresentationsValue (declarations.filter fun declaration => declaration.name == requested)) _
          · exact reflectionEnv_capture .reflectivePresentations selected state _ _ _ rfl
              (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup]) ih
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              filtered, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup]
          · have templated : PureData.Template reflectionRuntime reflectionReflectivePresentationsConsData := by
              unfold reflectionReflectivePresentationsConsData
              machine_template
            simpa [reflectionReflectivePresentationsConsData, reflectionReflectivePresentationsValue, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm, encodeList,
              filtered, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, applySubst.applySubstList,
              Subst.lookup, reflectionStringValue, reflectionCollectionValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return reflectionRuntime filtered state _ templated
        · have excluded : (declaration.name == requested) = false := by simp [same]
          simp only [same, decide_false, List.filter_cons, excluded]
          exact reflectionEnv_capture .reflectivePresentations selected state _ _ _ rfl
            (by simp [selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup]) ih

theorem reflective_presentations_captured_returns (caller : Subst) (state : State) (requested : String)
    (declarations : List ReflectivePresentationDecl) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [reflectionStringValue requested, reflectionReflectivePresentationsValue declarations]) :
    PureReturns reflectionRuntime caller state (reflectionA "gslt:premise:reflective-presentations" [one, two]) state
      (reflectionReflectivePresentationsValue (declarations.filter fun declaration => declaration.name == requested)) :=
  reflectionEnv_capture .reflectivePresentations caller state _ _ _ rfl captured (reflective_presentations_returns state requested declarations)

#print axioms reflective_presentations_returns
#print axioms reflective_presentations_captured_returns

private abbrev reflectionPresentationOptionValue (declaration : Option ReflectivePresentationDecl) : Atom :=
  reflectionEncoded (encodeOption InferenceCettaWire.AuthoredRule.reflectivePresentationTerm declaration)
private def reflectionPresentationSomeData : Atom :=
  reflectionA "Some" [reflectionA "ReflectivePresentation" [reflectionV "name", reflectionV "processSort", reflectionV "nameSort", reflectionV "quote", reflectionV "drop",
    reflectionV "kind", reflectionV "unit", reflectionV "equation"]]
private def reflectionPresentationNamedCases : SpaceSemantics.Cases :=
  [(reflectionA "LCons" [reflectionA "ReflectivePresentation" [reflectionV "name", reflectionV "processSort", reflectionV "nameSort", reflectionV "quote", reflectionV "drop",
      reflectionV "kind", reflectionV "unit", reflectionV "equation"], .symbol "LNil"], reflectionPresentationSomeData),
    (reflectionV "unavailable", .symbol "None")]
private theorem reflectionPresentation_named_shape : (reflectionEnvEquation .presentationNamed).body =
    reflectionCaseData (reflectionA "gslt:premise:reflective-presentations" [reflectionV "requested", reflectionV "presentations"])
      reflectionPresentationNamedCases := by rfl

/-- Presentation names select a unique physical declaration, including all
eight fields used by its original reflective operation. -/
theorem presentation_named_returns (state : State) (profile : Reflection.ReflectionProfile) (requested : String) :
    PureReturns reflectionRuntime [] state
      (reflectionA "gslt:premise:presentation-named" [reflectionReflectivePresentationsValue profile.presentations, reflectionStringValue requested]) state
      (reflectionPresentationOptionValue (ReflectiveSubstitution.presentationNamed? profile requested)) := by
  let caller := reflectionEnvCaptured .presentationNamed [reflectionReflectivePresentationsValue profile.presentations, reflectionStringValue requested]
  apply reflectionEnv_call .presentationNamed [] state _ _ _ rfl (reflectionCaptured_closed _)
  rw [reflectionPresentation_named_shape]
  have computed := reflective_presentations_captured_returns caller state requested profile.presentations
    (reflectionV "requested") (reflectionV "presentations") (by
      simp [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
  cases found : profile.presentations.filter (fun declaration => declaration.name == requested) with
  | nil =>
      let unavailable := ("unavailable", reflectionReflectivePresentationsValue []) :: caller
      apply reflectionBranch_returns caller unavailable state _ (reflectionReflectivePresentationsValue []) reflectionPresentationNamedCases (.symbol "None") _
      · simpa only [found] using computed
      · simp [reflectionPresentationNamedCases, unavailable, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup,
          reflectionReflectivePresentationsValue, encodeList, CettaWireAtom.encode, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · simpa [ReflectiveSubstitution.presentationNamed?, found, reflectionPresentationOptionValue, encodeOption, CettaWireAtom.encode] using
          symbol_returns reflectionRuntime unavailable state "None"
  | cons declaration declarations =>
      cases declarations with
      | nil =>
          let selected := [("equation", reflectionStringValue declaration.quoteDropEquation),
            ("unit", reflectionStringValue declaration.parallelUnitConstructor),
            ("kind", reflectionCollectionValue declaration.parallelCollection), ("drop", reflectionStringValue declaration.dropConstructor),
            ("quote", reflectionStringValue declaration.quoteConstructor), ("nameSort", reflectionStringValue declaration.nameSort),
            ("processSort", reflectionStringValue declaration.processSort), ("name", reflectionStringValue declaration.name)] ++ caller
          apply reflectionBranch_returns caller selected state _ (reflectionReflectivePresentationsValue [declaration])
            reflectionPresentationNamedCases reflectionPresentationSomeData _
          · simpa only [found] using computed
          · simp [reflectionPresentationNamedCases, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup,
              reflectionReflectivePresentationsValue, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm, reflectionCollectionValue, reflectionStringValue, encodeList,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
          · have templated : PureData.Template reflectionRuntime reflectionPresentationSomeData := by
              unfold reflectionPresentationSomeData
              machine_template
            simpa [reflectionPresentationSomeData, ReflectiveSubstitution.presentationNamed?, found, reflectionPresentationOptionValue,
              encodeOption, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm, selected, caller, reflectionEnvCaptured, reflectionEnvHelper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, reflectionCollectionValue, reflectionStringValue,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return reflectionRuntime selected state _ templated
      | cons next declarations =>
          let unavailable := ("unavailable", reflectionReflectivePresentationsValue (declaration :: next :: declarations)) :: caller
          apply reflectionBranch_returns caller unavailable state _ (reflectionReflectivePresentationsValue (declaration :: next :: declarations))
            reflectionPresentationNamedCases (.symbol "None") _
          · simpa only [found] using computed
          · simp [reflectionPresentationNamedCases, unavailable, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup,
              reflectionReflectivePresentationsValue, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom]
          · simpa [ReflectiveSubstitution.presentationNamed?, found, reflectionPresentationOptionValue, encodeOption, CettaWireAtom.encode] using
              symbol_returns reflectionRuntime unavailable state "None"

theorem presentation_named_captured_returns (caller : Subst) (state : State)
    (profile : Reflection.ReflectionProfile) (requested : String) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [reflectionReflectivePresentationsValue profile.presentations, reflectionStringValue requested]) :
    PureReturns reflectionRuntime caller state (reflectionA "gslt:premise:presentation-named" [one, two]) state
      (reflectionPresentationOptionValue (ReflectiveSubstitution.presentationNamed? profile requested)) :=
  reflectionEnv_capture .presentationNamed caller state _ _ _ rfl captured (presentation_named_returns state profile requested)

#print axioms presentation_named_returns
#print axioms presentation_named_captured_returns

private def reflectionSubstitutionSelectedCases : SpaceSemantics.Cases :=
  [(reflectionA "LCons" [reflectionA "ReflectiveRule" [reflectionV "name", reflectionV "rewrite", reflectionV "matching", reflectionV "substitution"], .symbol "LNil"],
    reflectionA "gslt:premise:presentation-named" [reflectionV "presentations", reflectionV "substitution"]),
    (reflectionV "unavailable", .symbol "None")]
private def reflectionSubstitutionRuleBody : Atom :=
  reflectionCaseData (reflectionA "gslt:premise:reflective-rules" [reflectionV "ruleName", reflectionV "declarations"]) reflectionSubstitutionSelectedCases
private def reflectionSubstitutionRuleCases : SpaceSemantics.Cases :=
  [(reflectionA "ScopedRewriteRuleV1" [reflectionV "ruleName", reflectionV "types", reflectionV "premises", reflectionV "left", reflectionV "right", reflectionV "bindings"],
    reflectionSubstitutionRuleBody), (reflectionV "badRule", .symbol "None")]
private def reflectionSubstitutionProfileBody : Atom := reflectionCaseData (reflectionV "rule") reflectionSubstitutionRuleCases
private def reflectionSubstitutionProfileCases : SpaceSemantics.Cases :=
  [(reflectionA "PremiseReflection" [reflectionV "presentations", reflectionV "declarations"], reflectionSubstitutionProfileBody),
    (reflectionV "badProfile", .symbol "None")]
private theorem reflectionSubstitution_presentation_shape : (reflectionEnvEquation .substitutionPresentation).body =
    reflectionCaseData (reflectionV "profile") reflectionSubstitutionProfileCases := by rfl

/-- The selected binder operation descriptor is the original rule-local,
duplicate-sensitive reflective selection. Missing selection remains None. -/
theorem substitution_presentation_returns (state : State) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) :
    PureReturns reflectionRuntime [] state
      (reflectionA "gslt:premise:substitution-presentation" [reflectionEncoded (reflectionTerm profile), reflectionRuleValue rule]) state
      (reflectionPresentationOptionValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule)) := by
  let caller := reflectionEnvCaptured .substitutionPresentation [reflectionEncoded (reflectionTerm profile), reflectionRuleValue rule]
  let parsed := [("declarations", reflectionReflectiveRulesValue profile.rules),
    ("presentations", reflectionReflectivePresentationsValue profile.presentations)] ++ caller
  let contextual := reflectionAssignmentRuleCaller rule parsed
  apply reflectionEnv_call .substitutionPresentation [] state _ _ _ rfl (reflectionCaptured_closed _)
  rw [reflectionSubstitution_presentation_shape]
  apply reflectionBranch_returns caller parsed state _ (reflectionEncoded (reflectionTerm profile))
    reflectionSubstitutionProfileCases reflectionSubstitutionProfileBody _
  · simpa [caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup] using
      variable_returns reflectionRuntime caller state "profile"
  · simp [reflectionSubstitutionProfileCases, reflectionTerm, reflectionReflectiveRulesValue, reflectionReflectivePresentationsValue,
      parsed, caller, reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
  · unfold reflectionSubstitutionProfileBody
    apply reflectionBranch_returns parsed contextual state _ (reflectionRuleValue rule) reflectionSubstitutionRuleCases reflectionSubstitutionRuleBody _
    · simpa [parsed, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup] using
        variable_returns reflectionRuntime parsed state "rule"
    · simp [reflectionSubstitutionRuleCases, contextual, reflectionAssignmentRuleCaller, parsed, caller, reflectionEnvCaptured, reflectionEnvHelper.names,
        reflectionRuleValue, InferenceCettaWire.AuthoredRule.rewriteTerm, InferenceCettaWire.encodeList, reflectionTypesValue,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold reflectionSubstitutionRuleBody
      have computed := reflective_rules_captured_returns contextual state rule.name profile.rules
        (reflectionV "ruleName") (reflectionV "declarations") (by
          simp [contextual, reflectionAssignmentRuleCaller, parsed, caller, reflectionEnvCaptured, reflectionEnvHelper.names, applySubst, Subst.lookup])
      cases found : profile.rules.filter (fun declaration => declaration.rewriteRule == rule.name) with
      | nil =>
          let unavailable := ("unavailable", reflectionReflectiveRulesValue []) :: contextual
          apply reflectionBranch_returns contextual unavailable state _ (reflectionReflectiveRulesValue [])
            reflectionSubstitutionSelectedCases (.symbol "None") _
          · simpa only [found] using computed
          · simp [reflectionSubstitutionSelectedCases, unavailable, contextual, reflectionAssignmentRuleCaller, parsed, caller,
              reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup, reflectionReflectiveRulesValue, encodeList, CettaWireAtom.encode,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · simpa [ReflectiveSubstitution.substitutionPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
              found, reflectionPresentationOptionValue, encodeOption, CettaWireAtom.encode] using
              symbol_returns reflectionRuntime unavailable state "None"
      | cons declaration declarations =>
          cases declarations with
          | nil =>
              let selected := [("substitution", reflectionStringValue declaration.substitutionPresentation),
                ("matching", reflectionStringValue declaration.matchingPresentation), ("rewrite", reflectionStringValue declaration.rewriteRule),
                ("name", reflectionStringValue declaration.name)] ++ contextual
              apply reflectionBranch_returns contextual selected state _ (reflectionReflectiveRulesValue [declaration]) reflectionSubstitutionSelectedCases
                (reflectionA "gslt:premise:presentation-named" [reflectionV "presentations", reflectionV "substitution"]) _
              · simpa only [found] using computed
              · simp [reflectionSubstitutionSelectedCases, selected, contextual, reflectionAssignmentRuleCaller, parsed, caller, reflectionEnvCaptured,
                  reflectionEnvHelper.names, Subst.lookup, reflectionReflectiveRulesValue, reflectiveRuleTerm, reflectionStringValue, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
              · simpa only [ReflectiveSubstitution.substitutionPresentationForRule?,
                  ReflectiveSubstitution.reflectiveRuleForRule?, found] using
                  presentation_named_captured_returns selected state profile declaration.substitutionPresentation
                    (reflectionV "presentations") (reflectionV "substitution") (by
                      simp [selected, contextual, reflectionAssignmentRuleCaller, parsed, caller, reflectionEnvCaptured,
                        reflectionEnvHelper.names, applySubst, Subst.lookup])
          | cons next declarations =>
              let unavailable := ("unavailable", reflectionReflectiveRulesValue (declaration :: next :: declarations)) :: contextual
              apply reflectionBranch_returns contextual unavailable state _ (reflectionReflectiveRulesValue (declaration :: next :: declarations))
                reflectionSubstitutionSelectedCases (.symbol "None") _
              · simpa only [found] using computed
              · simp [reflectionSubstitutionSelectedCases, unavailable, contextual, reflectionAssignmentRuleCaller, parsed, caller,
                  reflectionEnvCaptured, reflectionEnvHelper.names, Subst.lookup, reflectionReflectiveRulesValue, reflectiveRuleTerm, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
              · simpa [ReflectiveSubstitution.substitutionPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
                  found, reflectionPresentationOptionValue, encodeOption, CettaWireAtom.encode] using
                  symbol_returns reflectionRuntime unavailable state "None"

theorem substitution_presentation_captured_returns (caller : Subst) (state : State)
    (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [reflectionEncoded (reflectionTerm profile), reflectionRuleValue rule]) :
    PureReturns reflectionRuntime caller state (reflectionA "gslt:premise:substitution-presentation" [one, two]) state
      (reflectionPresentationOptionValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule)) :=
  reflectionEnv_capture .substitutionPresentation caller state _ _ _ rfl captured
    (substitution_presentation_returns state profile rule)

#print axioms substitution_presentation_returns
#print axioms substitution_presentation_captured_returns


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise

theorem environmentTerm_binding_shape (environment : Environment) (free : List (String × TypeExpr)) :
    environmentTerm environment free = .application "PremiseEnvironment"
      [DeclarationTyping.declarationsTerm environment.language.terms,
       encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites,
       encodeList specificationTerm environment.specifications, providerTerm environment.provider,
       reflectionTerm environment.reflection, DeclarationTyping.freeContextTerm free] := rfl

#print axioms environmentTerm_binding_shape

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution
