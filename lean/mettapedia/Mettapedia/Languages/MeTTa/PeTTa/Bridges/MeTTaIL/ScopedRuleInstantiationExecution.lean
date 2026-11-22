import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation
import Mettapedia.Tools.KernelReflexivity

/-!
# Scoped RHS and source-selected reflective substitution execution

The authored operations realize the existing contextual assignments and
source-selected binder operation. They preserve occurrence metadata, dependency
arguments and opaque inserted values. Captured call and completed-observation
laws transport these operations to larger programs with ordered row agreement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedReflectiveBinderOperationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open Mettapedia.OSLF.MeTTaIL Syntax
open scoped ProgramQuotation

def sourceProgram : Program := RuleExecutionProgram.scopedReflectionProgram

def runtime : Program := RuleExecutionProgram.program.append sourceProgram

theorem runtime_eq_append : runtime = RuleExecutionProgram.program.append sourceProgram := rfl

/-- The reflective operations, loaded over the rule execution program, own their prefix. -/
private def library : BridgeKit.Library :=
  ⟨RuleExecutionProgram.program, sourceProgram,
    ["gslt:rule:scope-reflective-"]⟩

/-- The base defines and calls no owned operation, and the source defines and declares only owned
operations. -/
private theorem library_checked : library.check = true := by decide +kernel

private theorem registered_of_source {head : String}
    (found : sourceProgram.equations.any (·.head == head) = true) :
    runtime.equations.any (·.head == head) = true := by
  simp only [runtime, SpaceSemantics.Program.append, List.any_append, found, Bool.or_true]

private theorem raw_of_source {head : String} {index : Nat}
    (raw : argumentIsRaw sourceProgram head index = true) : argumentIsRaw runtime head index = true := by
  unfold argumentIsRaw at raw ⊢
  by_cases native : StdLib.known head
  · simpa only [native, ↓reduceIte] using raw
  · simp only [native, Bool.false_eq_true, ↓reduceIte] at raw ⊢
    simp only [runtime, SpaceSemantics.Program.append, List.any_append, raw, Bool.or_true]

theorem retained_program_agreement (allowed : String → Bool)
    (freshEquations : ∀ equation ∈ sourceProgram.equations, allowed equation.head = false)
    (freshDeclarations : ∀ name types,
      .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] ∈
        sourceProgram.declarations → allowed name = false) :
    ProgramAgreementOn allowed RuleExecutionProgram.program runtime :=
  appended_program_agreement allowed RuleExecutionProgram.program sourceProgram freshEquations freshDeclarations

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev textValue (value : String) : Atom := encoded (.string value)
private abbrev declarationValue (declaration : ReflectivePresentationDecl) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.reflectivePresentationTerm declaration)

attribute [local simp] Effects.boolean encoded number patternValue patternsValue textValue declarationValue

private inductive Helper where
  | normalize | normalizeList | normalizeFinish | replacement
  | binderHead | binderHeadList | binderHeadJoin | binderHeadFold | binderHeadApply
  | leaves | leavesList | append | exposedDrop | resolveFinish | resolve | resolveList
  | receive | substitute | substituteList | substituteApply | substituteUnary | operation
private def Helper.head : Helper → String
  | .normalize => "gslt:rule:scope-reflective-normalize"
  | .normalizeList => "gslt:rule:scope-reflective-normalize-list"
  | .normalizeFinish => "gslt:rule:scope-reflective-normalize-finish"
  | .replacement => "gslt:rule:scope-reflective-replacement"
  | .binderHead => "gslt:rule:scope-reflective-binder-head"
  | .binderHeadList => "gslt:rule:scope-reflective-binder-head-list"
  | .binderHeadJoin => "gslt:rule:scope-reflective-binder-head-join"
  | .binderHeadFold => "gslt:rule:scope-reflective-binder-head-fold"
  | .binderHeadApply => "gslt:rule:scope-reflective-binder-head-apply"
  | .leaves => "gslt:rule:scope-reflective-leaves"
  | .leavesList => "gslt:rule:scope-reflective-leaves-list"
  | .append => "gslt:rule:scope-reflective-append"
  | .exposedDrop => "gslt:rule:scope-reflective-exposed-drop"
  | .resolveFinish => "gslt:rule:scope-reflective-resolve-finish"
  | .resolve => "gslt:rule:scope-reflective-resolve"
  | .resolveList => "gslt:rule:scope-reflective-resolve-list"
  | .receive => "gslt:rule:scope-reflective-receive"
  | .substitute => "gslt:rule:scope-reflective-substitute-at"
  | .substituteList => "gslt:rule:scope-reflective-substitute-list-at"
  | .substituteApply => "gslt:rule:scope-reflective-substitute-apply"
  | .substituteUnary => "gslt:rule:scope-reflective-substitute-unary"
  | .operation => "gslt:rule:scope-reflective-binder-operation"
private def Helper.names : Helper → List String
  | .normalize => ["quote", "drop", "pattern"]
  | .normalizeList => ["quote", "drop", "patterns"]
  | .normalizeFinish => ["quote", "drop", "head", "children"]
  | .replacement => ["quote", "drop", "replacement"]
  | .binderHead => ["quote", "drop", "parallel-kind", "parallel-unit", "pattern"]
  | .binderHeadList => ["quote", "drop", "parallel-kind", "parallel-unit", "patterns"]
  | .binderHeadJoin => ["left", "right"]
  | .binderHeadFold => ["heads"]
  | .binderHeadApply => ["quote", "drop", "parallel-unit", "constructor", "heads"]
  | .leaves => ["parallel-kind", "parallel-unit", "pattern"]
  | .leavesList => ["parallel-kind", "parallel-unit", "patterns"]
  | .append => ["left", "right"]
  | .exposedDrop => ["drop", "parallel-kind", "parallel-unit", "pattern"]
  | .resolveFinish => ["quote", "drop", "parallel-kind", "parallel-unit", "head", "children"]
  | .resolve => ["quote", "drop", "parallel-kind", "parallel-unit", "pattern"]
  | .resolveList => ["quote", "drop", "parallel-kind", "parallel-unit", "patterns"]
  | .receive => ["quote", "head", "name"]
  | .substitute => ["quote", "drop", "parallel-kind", "parallel-unit", "inside", "depth", "replacement", "pattern"]
  | .substituteList => ["quote", "drop", "parallel-kind", "parallel-unit", "inside", "depth", "replacement", "patterns"]
  | .substituteApply => ["quote", "drop", "parallel-kind", "parallel-unit", "inside", "depth", "replacement", "head", "children"]
  | .substituteUnary => ["quote", "drop", "parallel-kind", "parallel-unit", "inside", "depth", "replacement", "head", "payload"]
  | .operation => ["declaration", "replacement", "body"]
private def reflectiveHeads : List String :=
  [.normalize, .normalizeList, .normalizeFinish, .replacement, .binderHead, .binderHeadList,
   .binderHeadJoin, .binderHeadFold, .binderHeadApply, .leaves, .leavesList, .append, .exposedDrop,
   .resolveFinish, .resolve, .resolveList, .receive, .substitute, .substituteList,
   .substituteApply, .substituteUnary, .operation].map Helper.head
private def retainedHead (head : String) : Bool := head != "eval" && !reflectiveHeads.contains head
private theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !retainedHead equation.head || codeWithin retainedHead equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row
private theorem retained_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.program runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : sourceProgram.equations.all (fun equation => !retainedHead equation.head) = true := by
      decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : retainedHead equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : sourceProgram.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !retainedHead head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : retainedHead name with
    | false => rfl
    | true => simp [selected] at row
private theorem retained_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns runtime caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

private theorem helper_owned (helper : Helper) : library.owns helper.head = true := by
  cases helper <;> decide +kernel
private def equations (head : String) : List SpaceSemantics.Equation := sourceProgram.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : SpaceSemantics.Equation := (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by
      exact (BridgeKit.Library.owned_equations library_checked (helper_owned helper)).trans
        (by cases helper <;> kernel_reflexivity)) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw sourceProgram helper.head index) = true := by
    cases helper <;> decide +kernel
  exact raw_of_source (List.all_eq_true.mp checked index (List.mem_range.mpr bounded))

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (environment helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (registered_of_source (by cases helper <;> decide +kernel))
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (by simp only [registered_of_source (head := helper.head) (by cases helper <;> decide +kernel), Bool.or_true])
    _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · simpa only [captured_closed] using captured.symm

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom)
    (fresh : Subst.lookup caller name = none)
    (returned : PureReturns runtime caller state expression state value)
    (continuation : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer returned _ continuation
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem constructor_variables (head : String) (names : List String)
    (inert : (ioHead head || StdLib.known head || runtime.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureData.Template runtime (a head (names.map v)) := by
  apply PureData.Template.constructor head _ inert ordinary
  intro argument member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact .captured name

private theorem strings_equal_returns (caller : Subst) (state : State) (left right : String)
    (first second : String)
    (capturedFirst : applySubst caller (v first) = textValue left)
    (capturedSecond : applySubst caller (v second) = textValue right) :
    PureReturns runtime caller state (a "==" [v first, v second]) state
      (Effects.boolean (left == right)) := by
  have same : decide (left = right) = (left == right) := by
    by_cases equal : left = right <;> simp [equal]
  simpa only [Term.string.injEq, same] using
    CettaWireAtom.equality_captured_returns runtime caller state (.string left) (.string right)
      first second capturedFirst capturedSecond

private def normalizeRow0 : Atom :=
  v "pattern"

private def normalizeRow1 : Atom :=
  v "pattern"

private def normalizeRow2 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-normalize-list" [v "quote", v "drop", v "children"], a "gslt:rule:scope-reflective-normalize-finish" [v "quote", v "drop", v "head", v "values"]]

private def normalizeRow3 : Atom :=
  a "let" [v "value", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "body"], a "PLam" [v "binder", v "value"]]

private def normalizeRow4 : Atom :=
  a "let" [v "value", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "body"], a "PMultiLam" [v "arity", v "binders", v "value"]]

private def normalizeRow5 : Atom :=
  a "let*" [.expression [.expression [v "value", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "body"]], .expression [v "replacement-value", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "replacement"]]], a "PSubst" [v "value", v "replacement-value"]]

private def normalizeRow6 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-normalize-list" [v "quote", v "drop", v "elements"], a "PCollection" [v "kind", v "values", v "rest"]]

private def normalizeRows : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], normalizeRow0),
   (a "FVar" [v "name"], normalizeRow1),
   (a "PApp" [v "head", v "children"], normalizeRow2),
   (a "PLam" [v "binder", v "body"], normalizeRow3),
   (a "PMultiLam" [v "arity", v "binders", v "body"], normalizeRow4),
   (a "PSubst" [v "body", v "replacement"], normalizeRow5),
   (a "PCollection" [v "kind", v "elements", v "rest"], normalizeRow6)]

private def normalizeBody : Atom :=
  a "case" [v "pattern", .expression (normalizeRows.map fun row => .expression [row.1, row.2])]

private def normalizeListRow0 : Atom :=
  .symbol "LNil"

private def normalizeListRow1 : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "pattern"]], .expression [v "tail", a "gslt:rule:scope-reflective-normalize-list" [v "quote", v "drop", v "rest"]]], a "LCons" [v "head", v "tail"]]

private def normalizeListRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", normalizeListRow0),
   (a "LCons" [v "pattern", v "rest"], normalizeListRow1)]

private def normalizeListBody : Atom :=
  a "case" [v "patterns", .expression (normalizeListRows.map fun row => .expression [row.1, row.2])]

private def normalizeFinishBody : Atom :=
  a "if" [a "==" [v "head", v "quote"], a "case" [v "children", .expression [.expression [a "LCons" [a "PApp" [v "inner-head", a "LCons" [v "name", .symbol "LNil"]], .symbol "LNil"], a "if" [a "==" [v "inner-head", v "drop"], v "name", a "PApp" [v "head", v "children"]]], .expression [v "ordinary", a "PApp" [v "head", v "children"]]]], a "PApp" [v "head", v "children"]]

private def replacementRow0 : Atom :=
  a "if" [a "==" [v "head", v "quote"], a "let" [v "value", a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "payload"], a "PApp" [v "head", a "LCons" [v "value", .symbol "LNil"]]], a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "replacement"]]

private def replacementRow1 : Atom :=
  a "gslt:rule:scope-reflective-normalize" [v "quote", v "drop", v "replacement"]

private def replacementRows : SpaceSemantics.Cases :=
  [(a "PApp" [v "head", a "LCons" [v "payload", .symbol "LNil"]], replacementRow0),
   (v "ordinary", replacementRow1)]

private def replacementBody : Atom :=
  a "case" [v "replacement", .expression (replacementRows.map fun row => .expression [row.1, row.2])]

private def collectionRestRows : SpaceSemantics.Cases :=
  [(.symbol "RNone",
     a "let" [v "heads", a "gslt:rule:scope-reflective-binder-head-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "elements"],
       a "gslt:rule:scope-reflective-binder-head-fold" [v "heads"]]),
   (v "open", .symbol "BinderOpaque")]

private def binderHeadRows : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], a "BinderIndex" [v "index"]),
   (a "PApp" [v "head", v "children"],
     a "let" [v "heads", a "gslt:rule:scope-reflective-binder-head-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "children"],
       a "gslt:rule:scope-reflective-binder-head-apply" [v "quote", v "drop", v "parallel-unit", v "head", v "heads"]]),
   (a "PCollection" [v "collection", v "elements", v "rest"],
     a "if" [a "==" [v "collection", v "parallel-kind"],
       a "case" [v "rest", .expression (collectionRestRows.map fun row => .expression [row.1, row.2])],
       .symbol "BinderOpaque"]),
   (v "other", .symbol "BinderOpaque")]

private def binderHeadBody : Atom :=
  a "case" [v "pattern", .expression (binderHeadRows.map fun row => .expression [row.1, row.2])]

private def binderHeadListRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "pattern", v "rest"],
     a "let*" [.expression [.expression [v "head", a "gslt:rule:scope-reflective-binder-head" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]], .expression [v "tail", a "gslt:rule:scope-reflective-binder-head-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"]]], a "LCons" [v "head", v "tail"]])]

private def binderHeadListBody : Atom :=
  a "case" [v "patterns", .expression (binderHeadListRows.map fun row => .expression [row.1, row.2])]

private def joinInnerRows : SpaceSemantics.Cases :=
  [(.symbol "BinderUnit", v "left"),
   (v "other", .symbol "BinderOpaque")]

private def joinRows : SpaceSemantics.Cases :=
  [(.symbol "BinderUnit", v "right"),
   (v "present", a "case" [v "right", .expression (joinInnerRows.map fun row => .expression [row.1, row.2])])]

private def binderHeadJoinBody : Atom :=
  a "case" [v "left", .expression (joinRows.map fun row => .expression [row.1, row.2])]

private def foldRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "BinderUnit"),
   (a "LCons" [v "head", v "rest"],
     a "let" [v "tail", a "gslt:rule:scope-reflective-binder-head-fold" [v "rest"],
       a "gslt:rule:scope-reflective-binder-head-join" [v "head", v "tail"]])]

private def binderHeadFoldBody : Atom :=
  a "case" [v "heads", .expression (foldRows.map fun row => .expression [row.1, row.2])]

private def applyRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "if" [a "==" [v "constructor", v "parallel-unit"], .symbol "BinderUnit", .symbol "BinderOpaque"]),
   (a "LCons" [a "BinderDrop" [v "name"], .symbol "LNil"],
     a "if" [a "==" [v "constructor", v "quote"], v "name",
       a "if" [a "==" [v "constructor", v "drop"], a "BinderDrop" [a "BinderDrop" [v "name"]], .symbol "BinderOpaque"]]),
   (a "LCons" [v "argument", .symbol "LNil"],
     a "if" [a "==" [v "constructor", v "drop"], a "BinderDrop" [v "argument"], .symbol "BinderOpaque"]),
   (v "many", .symbol "BinderOpaque")]

private def binderHeadApplyBody : Atom :=
  a "case" [v "heads", .expression (applyRows.map fun row => .expression [row.1, row.2])]

private def leavesUnitRow : Atom :=
  a "if" [a "==" [v "head", v "parallel-unit"], .symbol "LNil", a "LCons" [v "pattern", .symbol "LNil"]]

private def leavesApplyRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", leavesUnitRow),
   (v "many", a "LCons" [v "pattern", .symbol "LNil"])]

private def leavesRestRows : SpaceSemantics.Cases :=
  [(.symbol "RNone", a "gslt:rule:scope-reflective-leaves-list" [v "parallel-kind", v "parallel-unit", v "elements"]),
   (v "open", a "LCons" [v "pattern", .symbol "LNil"])]

private def leavesCollectionRow : Atom :=
  a "if" [a "==" [v "collection", v "parallel-kind"],
    a "case" [v "rest", .expression (leavesRestRows.map fun row => .expression [row.1, row.2])],
    a "LCons" [v "pattern", .symbol "LNil"]]

private def leavesRows : SpaceSemantics.Cases :=
  [(a "PApp" [v "head", v "children"],
     a "case" [v "children", .expression (leavesApplyRows.map fun row => .expression [row.1, row.2])]),
   (a "PCollection" [v "collection", v "elements", v "rest"], leavesCollectionRow),
   (v "other", a "LCons" [v "pattern", .symbol "LNil"])]

private def leavesBody : Atom :=
  a "case" [v "pattern", .expression (leavesRows.map fun row => .expression [row.1, row.2])]

private def leavesListRow1 : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:rule:scope-reflective-leaves" [v "parallel-kind", v "parallel-unit", v "pattern"]], .expression [v "tail", a "gslt:rule:scope-reflective-leaves-list" [v "parallel-kind", v "parallel-unit", v "rest"]]], a "gslt:rule:scope-reflective-append" [v "head", v "tail"]]

private def leavesListRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "pattern", v "rest"], leavesListRow1)]

private def leavesListBody : Atom :=
  a "case" [v "patterns", .expression (leavesListRows.map fun row => .expression [row.1, row.2])]

private def appendRow1 : Atom :=
  a "let" [v "tail", a "gslt:rule:scope-reflective-append" [v "rest", v "right"], a "LCons" [v "item", v "tail"]]

private def appendRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", v "right"),
   (a "LCons" [v "item", v "rest"], appendRow1)]

private def appendBody : Atom :=
  a "case" [v "left", .expression (appendRows.map fun row => .expression [row.1, row.2])]

private def exposedRows : SpaceSemantics.Cases :=
  [(a "LCons" [a "PApp" [v "head", a "LCons" [v "name", .symbol "LNil"]], .symbol "LNil"],
     a "if" [a "==" [v "head", v "drop"], a "Some" [v "name"], .symbol "None"]),
   (v "other", .symbol "None")]

private def exposedDropBody : Atom :=
  a "let" [v "leaves", a "gslt:rule:scope-reflective-leaves" [v "parallel-kind", v "parallel-unit", v "pattern"],
    a "case" [v "leaves", .expression (exposedRows.map fun row => .expression [row.1, row.2])]]

private def exposedNameRows : SpaceSemantics.Cases :=
  [(a "Some" [v "name"], v "name"),
   (v "none", a "PApp" [v "head", v "children"])]

private def resolveFinishRow0 : Atom :=
  a "if" [a "==" [v "head", v "quote"],
    a "let" [v "exposed", a "gslt:rule:scope-reflective-exposed-drop" [v "drop", v "parallel-kind", v "parallel-unit", v "payload"],
      a "case" [v "exposed", .expression (exposedNameRows.map fun row => .expression [row.1, row.2])]],
    a "PApp" [v "head", v "children"]]

private def resolveFinishRows : SpaceSemantics.Cases :=
  [(a "LCons" [v "payload", .symbol "LNil"], resolveFinishRow0),
   (v "other", a "PApp" [v "head", v "children"])]

private def resolveFinishBody : Atom :=
  a "case" [v "children", .expression (resolveFinishRows.map fun row => .expression [row.1, row.2])]

private def resolveRow0 : Atom :=
  v "pattern"

private def resolveRow1 : Atom :=
  v "pattern"

private def resolveRow2 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-resolve-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "children"], a "gslt:rule:scope-reflective-resolve-finish" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "head", v "values"]]

private def resolveRow3 : Atom :=
  a "let" [v "value", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"], a "PLam" [v "binder", v "value"]]

private def resolveRow4 : Atom :=
  a "let" [v "value", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"], a "PMultiLam" [v "arity", v "binders", v "value"]]

private def resolveRow5 : Atom :=
  a "let*" [.expression [.expression [v "value", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]], .expression [v "replacement-value", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "replacement"]]], a "PSubst" [v "value", v "replacement-value"]]

private def resolveRow6 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-resolve-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "elements"], a "PCollection" [v "kind", v "values", v "rest"]]

private def resolveRows : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], resolveRow0),
   (a "FVar" [v "name"], resolveRow1),
   (a "PApp" [v "head", v "children"], resolveRow2),
   (a "PLam" [v "binder", v "body"], resolveRow3),
   (a "PMultiLam" [v "arity", v "binders", v "body"], resolveRow4),
   (a "PSubst" [v "body", v "replacement"], resolveRow5),
   (a "PCollection" [v "kind", v "elements", v "rest"], resolveRow6)]

private def resolveBody : Atom :=
  a "case" [v "pattern", .expression (resolveRows.map fun row => .expression [row.1, row.2])]

private def resolveListRow0 : Atom :=
  .symbol "LNil"

private def resolveListRow1 : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]], .expression [v "tail", a "gslt:rule:scope-reflective-resolve-list" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"]]], a "LCons" [v "head", v "tail"]]

private def resolveListRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", resolveListRow0),
   (a "LCons" [v "pattern", v "rest"], resolveListRow1)]

private def resolveListBody : Atom :=
  a "case" [v "patterns", .expression (resolveListRows.map fun row => .expression [row.1, row.2])]

private def receiveRows : SpaceSemantics.Cases :=
  [(a "PApp" [v "inner-head", a "LCons" [v "process", .symbol "LNil"]],
    a "if" [a "==" [v "inner-head", v "quote"], v "process", a "PApp" [v "head", a "LCons" [v "name", .symbol "LNil"]]]),
   (v "ordinary", a "PApp" [v "head", a "LCons" [v "name", .symbol "LNil"]])]

private def receiveBody : Atom :=
  a "case" [v "name", .expression (receiveRows.map fun row => .expression [row.1, row.2])]

private def substituteRow0 : Atom :=
  a "gslt:rule:instantiate-bvar-at" [v "depth", v "replacement", v "pattern"]

private def substituteRow1 : Atom :=
  v "pattern"

private def substituteRow2 : Atom :=
  a "gslt:rule:scope-reflective-substitute-apply" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "head", v "children"]

private def substituteRow3 : Atom :=
  a "let*" [.expression [.expression [v "next", a "+" [v "depth", number 1]], .expression [v "value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]]], a "PLam" [v "binder", v "value"]]

private def substituteRow4 : Atom :=
  a "let*" [.expression [.expression [v "next", a "+" [v "depth", v "arity"]], .expression [v "value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]]], a "PMultiLam" [v "arity", v "binders", v "value"]]

private def substituteRow5 : Atom :=
  a "let*" [.expression [.expression [v "next", a "+" [v "depth", number 1]], .expression [v "value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]], .expression [v "replacement-value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "nested-replacement"]]], a "PSubst" [v "value", v "replacement-value"]]

private def substituteRow6 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-substitute-list-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "elements"], a "PCollection" [v "kind", v "values", v "rest"]]

private def substituteRows : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], substituteRow0),
   (a "FVar" [v "name"], substituteRow1),
   (a "PApp" [v "head", v "children"], substituteRow2),
   (a "PLam" [v "binder", v "body"], substituteRow3),
   (a "PMultiLam" [v "arity", v "binders", v "body"], substituteRow4),
   (a "PSubst" [v "body", v "nested-replacement"], substituteRow5),
   (a "PCollection" [v "kind", v "elements", v "rest"], substituteRow6)]

private def substituteBody : Atom :=
  a "case" [v "pattern", .expression (substituteRows.map fun row => .expression [row.1, row.2])]

private def substituteListRow0 : Atom :=
  .symbol "LNil"

private def substituteListRow1 : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "pattern"]], .expression [v "tail", a "gslt:rule:scope-reflective-substitute-list-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "rest"]]], a "LCons" [v "head", v "tail"]]

private def substituteListRows : SpaceSemantics.Cases :=
  [(.symbol "LNil", substituteListRow0),
   (a "LCons" [v "pattern", v "rest"], substituteListRow1)]

private def substituteListBody : Atom :=
  a "case" [v "patterns", .expression (substituteListRows.map fun row => .expression [row.1, row.2])]

private def substituteApplyRow0 : Atom :=
  a "gslt:rule:scope-reflective-substitute-unary" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "head", v "payload"]

private def substituteApplyRow1 : Atom :=
  a "let" [v "values", a "gslt:rule:scope-reflective-substitute-list-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "children"], a "PApp" [v "head", v "values"]]

private def substituteApplyRows : SpaceSemantics.Cases :=
  [(a "LCons" [v "payload", .symbol "LNil"], substituteApplyRow0),
   (v "many", substituteApplyRow1)]

private def substituteApplyBody : Atom :=
  a "case" [v "children", .expression (substituteApplyRows.map fun row => .expression [row.1, row.2])]

private def substituteThrough : Atom :=
  a "let" [v "value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "payload"], a "PApp" [v "head", a "LCons" [v "value", .symbol "LNil"]]]

private def receiveHit : Atom :=
  a "let" [v "value", a "gslt:rule:instantiate-bvar-at" [v "depth", v "replacement", a "Var" [v "depth"]],
    a "gslt:rule:scope-reflective-receive" [v "quote", v "head", v "value"]]

private def binderRows : SpaceSemantics.Cases :=
  [(a "BinderIndex" [v "level"], a "if" [a "==" [v "level", v "depth"], receiveHit, substituteThrough]),
   (v "other", substituteThrough)]

private def substituteDrop : Atom :=
  a "let" [v "binder", a "gslt:rule:scope-reflective-binder-head" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "payload"],
    a "case" [v "binder", .expression (binderRows.map fun row => .expression [row.1, row.2])]]

private def insideRows : SpaceSemantics.Cases :=
  [(.symbol "Opaque", a "PApp" [v "head", a "LCons" [v "payload", .symbol "LNil"]]),
   (a "Enter" [v "value"],
     a "let" [v "entered", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind",
       v "parallel-unit", v "inside", v "depth", v "value", v "payload"],
       a "PApp" [v "head", a "LCons" [v "entered", .symbol "LNil"]]])]

private def substituteQuote : Atom :=
  a "case" [v "inside", .expression (insideRows.map fun row => .expression [row.1, row.2])]

private def substituteUnaryBody : Atom :=
  a "if" [a "==" [v "head", v "quote"], substituteQuote,
    a "if" [a "==" [v "head", v "drop"], substituteDrop, substituteThrough]]

private def scopeRows : SpaceSemantics.Cases :=
  [(.symbol "QuoteClosed", .symbol "Opaque"),
   (a "QuoteReaching" [.symbol "QuoteApply"], a "Enter" [v "normalized"]),
   (a "QuoteReaching" [a "QuoteFreeze" [v "spelling"]], a "Enter" [v "spelling"]),
   (a "QuoteReaching" [a "QuoteClosure" [v "context"]],
     a "Enter" [a "PApp" [v "context", a "LCons" [v "normalized", .symbol "LNil"]]])]

private def scopeCase : Atom :=
  a "case" [v "scope", .expression (scopeRows.map fun row => .expression [row.1, row.2])]

private def operationRow0 : Atom :=
  a "let*" [.expression [.expression [v "normalized", a "gslt:rule:scope-reflective-replacement" [v "quote", v "drop", v "replacement"]], .expression [v "resolved", a "gslt:rule:scope-reflective-resolve" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]], .expression [v "inside", scopeCase], .expression [v "value", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", number 0, v "normalized", v "resolved"]]], a "Some" [v "value"]]

private def operationRow1 : Atom :=
  .symbol "None"

private def operationRows : SpaceSemantics.Cases :=
  [(a "ReflectivePresentation" [v "name", v "process-sort", v "name-sort", v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "quote-drop-equation", v "scope"], operationRow0),
   (v "invalid", operationRow1)]

private def operationBody : Atom :=
  a "case" [v "declaration", .expression (operationRows.map fun row => .expression [row.1, row.2])]

private def helperBody : Helper → Atom
  | .normalize => normalizeBody
  | .normalizeList => normalizeListBody
  | .normalizeFinish => normalizeFinishBody
  | .replacement => replacementBody
  | .binderHead => binderHeadBody
  | .binderHeadList => binderHeadListBody
  | .binderHeadJoin => binderHeadJoinBody
  | .binderHeadFold => binderHeadFoldBody
  | .binderHeadApply => binderHeadApplyBody
  | .leaves => leavesBody
  | .leavesList => leavesListBody
  | .append => appendBody
  | .exposedDrop => exposedDropBody
  | .resolveFinish => resolveFinishBody
  | .resolve => resolveBody
  | .resolveList => resolveListBody
  | .receive => receiveBody
  | .substitute => substituteBody
  | .substituteList => substituteListBody
  | .substituteApply => substituteApplyBody
  | .substituteUnary => substituteUnaryBody
  | .operation => operationBody

private theorem source_body (helper : Helper) : (equation helper).body = helperBody helper := by
  cases helper <;> decide +kernel

private theorem helper_case (helper : Helper) (state : State) (values : List Atom)
    (name : String) (value : Atom) (rows : SpaceSemantics.Cases) (selected : Subst) (body answer : Atom)
    (length : values.length = helper.names.length)
    (shape : helperBody helper = a "case" [v name, .expression (rows.map fun row => .expression [row.1, row.2])])
    (captured : applySubst (environment helper values) (v name) = value)
    (matched : SpaceSemantics.selectCase (environment helper values) value rows = some (selected, body))
    (returned : PureReturns runtime selected state body state answer) :
    PureReturns runtime [] state (a helper.head values) state answer := by
  apply helper_call helper [] state values values answer length (captured_closed _)
  rw [source_body, shape]
  apply branch_returns _ selected state _ value rows body answer _ matched returned
  simpa only [captured] using variable_returns runtime (environment helper values) state name

private theorem data_constructor (head : String) (names : List String)
    (constructor : head ∈ ["LCons", "PApp", "PLam", "PMultiLam", "PSubst", "PCollection", "Some", "Enter"]) :
    PureData.Template runtime (a head (names.map v)) := by
  apply constructor_variables head names
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
    rcases constructor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (decide +kernel)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
    rcases constructor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem normalize_list_map (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    ReflectiveSubstitution.normalizeReflectiveList declaration patterns =
      patterns.map (ReflectiveSubstitution.normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [ReflectiveSubstitution.normalizeReflectiveList, ih]

private def finishRows : SpaceSemantics.Cases :=
  [(a "LCons" [a "PApp" [v "inner-head", a "LCons" [v "name", .symbol "LNil"]], .symbol "LNil"],
    a "if" [a "==" [v "inner-head", v "drop"], v "name", a "PApp" [v "head", v "children"]]),
   (v "ordinary", a "PApp" [v "head", v "children"])]
private theorem normalize_finish_shape : normalizeFinishBody =
    a "if" [a "==" [v "head", v "quote"],
      a "case" [v "children", .expression (finishRows.map fun row => .expression [row.1, row.2])],
      a "PApp" [v "head", v "children"]] := rfl

private theorem finish_application_returns (caller : Subst) (state : State)
    (constructor : String) (children : List Pattern) (headName : String := "head") (childrenName : String := "children")
    (headCaptured : applySubst caller (v headName) = textValue constructor)
    (childrenCaptured : applySubst caller (v childrenName) = patternsValue children) :
    PureReturns runtime caller state (a "PApp" [v headName, v childrenName]) state
      (patternValue (.apply constructor children)) := by
  have same : applySubst caller (a "PApp" [v headName, v childrenName]) =
      patternValue (.apply constructor children) := by
    change a "PApp" [applySubst caller (v headName), applySubst caller (v childrenName)] = _
    rw [headCaptured, childrenCaptured]
    simp [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  simpa only [same] using
    PureData.template_return runtime caller state (a "PApp" [v headName, v childrenName])
      (data_constructor "PApp" [headName, childrenName] (by decide))

private theorem finish_nonunary_result (declaration : ReflectivePresentationDecl)
    (constructor : String) (children : List Pattern)
    (nonunary : ¬∃ inner name, children = [.apply inner [name]]) :
    ReflectiveSubstitution.finishNormalizeReflectiveApply declaration constructor children = .apply constructor children := by
  cases children with
  | nil => simp [ReflectiveSubstitution.finishNormalizeReflectiveApply]
  | cons first tail =>
      cases tail with
      | cons second rest => cases first <;> simp [ReflectiveSubstitution.finishNormalizeReflectiveApply]
      | nil =>
          cases first with
          | apply head arguments =>
              cases arguments with
              | nil => simp [ReflectiveSubstitution.finishNormalizeReflectiveApply]
              | cons payload tail =>
                  cases tail with
                  | nil => exact False.elim (nonunary ⟨head, payload, rfl⟩)
                  | cons second rest => simp [ReflectiveSubstitution.finishNormalizeReflectiveApply]
          | bvar _ | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
              simp [ReflectiveSubstitution.finishNormalizeReflectiveApply]

private theorem normalize_finish_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (children : List Pattern) :
    PureReturns runtime [] state
      (a Helper.normalizeFinish.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue constructor, patternsValue children]) state
      (patternValue (ReflectiveSubstitution.finishNormalizeReflectiveApply declaration constructor children)) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    textValue constructor, patternsValue children]
  let caller := environment .normalizeFinish values
  apply helper_call .normalizeFinish [] state values values _ rfl (captured_closed _)
  rw [source_body]
  change PureReturns runtime caller state normalizeFinishBody state _
  rw [normalize_finish_shape]
  apply bool_if_returns caller state _ (constructor == declaration.quoteConstructor) _ _ _
  · apply strings_equal_returns caller state constructor declaration.quoteConstructor "head" "quote"
    · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · by_cases quoted : constructor == declaration.quoteConstructor
    · simp only [quoted, ite_true]
      by_cases shaped : ∃ innerHead name, children = [.apply innerHead [name]]
      · obtain ⟨innerHead, name, shape⟩ := shaped
        subst children
        simp only [ReflectiveSubstitution.finishNormalizeReflectiveApply, quoted, ite_true]
        let selected := ("name", patternValue name) :: ("inner-head", textValue innerHead) :: caller
        apply branch_returns caller selected state _ (patternsValue [.apply innerHead [name]]) finishRows
          (a "if" [a "==" [v "inner-head", v "drop"], v "name", a "PApp" [v "head", v "children"]]) _
        · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns runtime caller state "children"
        · simp [finishRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply bool_if_returns selected state _ (innerHead == declaration.dropConstructor) _ _ _
          · apply strings_equal_returns selected state innerHead declaration.dropConstructor "inner-head" "drop"
            · simp [selected, applySubst, Subst.lookup]
            · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · by_cases dropped : innerHead == declaration.dropConstructor
            · simpa [dropped, selected, applySubst, Subst.lookup] using
                variable_returns runtime selected state "name"
            · simp only [dropped, Bool.false_eq_true, ite_false]
              apply finish_application_returns
              · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
              · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · rw [finish_nonunary_result declaration constructor children shaped]
        let selected := ("ordinary", patternsValue children) :: caller
        apply branch_returns caller selected state _ (patternsValue children) finishRows (a "PApp" [v "head", v "children"]) _
        · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns runtime caller state "children"
        · cases children with
          | nil => simp [finishRows, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
          | cons first tail =>
              cases tail with
              | cons second rest =>
                  cases first <;> simp [finishRows, InferenceCettaWire.encodePatterns,
                    InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
                    environment, Helper.names, Subst.lookup]
              | nil =>
                  cases first with
                  | apply head arguments =>
                      cases arguments with
                      | nil => simp [finishRows, InferenceCettaWire.encodePatterns,
                          InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
                          environment, Helper.names, Subst.lookup]
                      | cons payload rest =>
                          cases rest with
                          | nil => exact False.elim (shaped ⟨head, payload, rfl⟩)
                          | cons second rest => simp [finishRows, InferenceCettaWire.encodePatterns,
                              InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                              SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
                              environment, Helper.names, Subst.lookup]
                  | bvar _ | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
                      simp [finishRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
                        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                        selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply finish_application_returns
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · simp only [ReflectiveSubstitution.finishNormalizeReflectiveApply, quoted, Bool.false_eq_true, ite_false]
      apply finish_application_returns
      · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]

private theorem normalize_list_returns_from_elements (state : State)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a Helper.normalize.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.normalizeReflective declaration pattern))) :
    PureReturns runtime [] state
      (a Helper.normalizeList.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, patternsValue patterns]) state
      (patternsValue (patterns.map (ReflectiveSubstitution.normalizeReflective declaration))) := by
  induction patterns with
  | nil =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternsValue []]
      apply helper_case .normalizeList state values "patterns" (.symbol "LNil") normalizeListRows
        (environment .normalizeList values) normalizeListRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [normalizeListRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [normalizeListRow0, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime _ state "LNil"
  | cons pattern patterns ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternsValue (pattern :: patterns)]
      let caller := environment .normalizeList values
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headValue := patternValue (ReflectiveSubstitution.normalizeReflective declaration pattern)
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue (patterns.map (ReflectiveSubstitution.normalizeReflective declaration))
      let final := ("tail", tailValue) :: headBound
      have headReturned := helper_capture .normalize selected state
        [v "quote", v "drop", v "pattern"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternValue pattern]
        headValue rfl (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have tailReturned := helper_capture .normalizeList headBound state
        [v "quote", v "drop", v "rest"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternsValue patterns]
        tailValue rfl (by simp [headBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply helper_case .normalizeList state values "patterns" (patternsValue (pattern :: patterns))
        normalizeListRows selected normalizeListRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeListRows, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, environment, Helper.names, Subst.lookup]
      · unfold normalizeListRow1
        apply PureData.let_bindings_return (pairs :=
          [(v "head", a Helper.normalize.head [v "quote", v "drop", v "pattern"]),
           (v "tail", a Helper.normalizeList.head [v "quote", v "drop", v "rest"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              headBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) tailReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, headBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [List.map_cons, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            final, headBound, headValue, tailValue] using
            PureData.template_return runtime final state (a "LCons" [v "head", v "tail"])
              (data_constructor "LCons" ["head", "tail"] (by decide))

theorem normalize_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns runtime [] state
      (a Helper.normalize.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.normalizeReflective declaration pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.bvar index)]
      let caller := environment .normalize values
      let selected := ("index", number index) :: caller
      apply helper_case .normalize state values "pattern" (patternValue (.bvar index))
        normalizeRows selected normalizeRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [normalizeRow0, ReflectiveSubstitution.normalizeReflective, selected, caller, values,
          environment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime selected state "pattern"
  | hfvar name =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.fvar name)]
      let caller := environment .normalize values
      let selected := ("name", textValue name) :: caller
      apply helper_case .normalize state values "pattern" (patternValue (.fvar name))
        normalizeRows selected normalizeRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [normalizeRow1, ReflectiveSubstitution.normalizeReflective, selected, caller, values,
          environment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime selected state "pattern"
  | happly head children ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.apply head children)]
      let caller := environment .normalize values
      let selected := ("children", patternsValue children) :: ("head", textValue head) :: caller
      let childrenResult := children.map (ReflectiveSubstitution.normalizeReflective declaration)
      let final := ("values", patternsValue childrenResult) :: selected
      simp only [ReflectiveSubstitution.normalizeReflective, normalize_list_map]
      apply helper_case .normalize state values "pattern" (patternValue (.apply head children))
        normalizeRows selected normalizeRow2 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold normalizeRow2
        apply named_let_returns selected state "values" _ (patternsValue childrenResult) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .normalizeList selected state _ _ _ rfl _
            (normalize_list_returns_from_elements state declaration children ih)
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · apply helper_capture .normalizeFinish final state _ _ _ rfl _
            (normalize_finish_returns state declaration head childrenResult)
          simp [final, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  | hlambda binder body ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.lambda binder body)]
      let caller := environment .normalize values
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let result := ReflectiveSubstitution.normalizeReflective declaration body
      let final := ("value", patternValue result) :: selected
      simp only [ReflectiveSubstitution.normalizeReflective]
      apply helper_case .normalize state values "pattern" (patternValue (.lambda binder body))
        normalizeRows selected normalizeRow3 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold normalizeRow3
        apply named_let_returns selected state "value" _ (patternValue result) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .normalize selected state _ _ _ rfl _ ih
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, result] using
            PureData.template_return runtime final state (a "PLam" [v "binder", v "value"])
              (data_constructor "PLam" ["binder", "value"] (by decide))
  | hmultiLambda arity binders body ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.multiLambda arity binders body)]
      let caller := environment .normalize values
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let result := ReflectiveSubstitution.normalizeReflective declaration body
      let final := ("value", patternValue result) :: selected
      simp only [ReflectiveSubstitution.normalizeReflective]
      apply helper_case .normalize state values "pattern" (patternValue (.multiLambda arity binders body))
        normalizeRows selected normalizeRow4 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold normalizeRow4
        apply named_let_returns selected state "value" _ (patternValue result) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .normalize selected state _ _ _ rfl _ ih
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, result] using
            PureData.template_return runtime final state (a "PMultiLam" [v "arity", v "binders", v "value"])
              (data_constructor "PMultiLam" ["arity", "binders", "value"] (by decide))
  | hsubst body replacement ihBody ihReplacement =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.subst body replacement)]
      let caller := environment .normalize values
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      let bodyResult := ReflectiveSubstitution.normalizeReflective declaration body
      let replacementResult := ReflectiveSubstitution.normalizeReflective declaration replacement
      let bodyBound := ("value", patternValue bodyResult) :: selected
      let final := ("replacement-value", patternValue replacementResult) :: bodyBound
      have bodyReturned := helper_capture .normalize selected state [v "quote", v "drop", v "body"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternValue body]
        (patternValue bodyResult) rfl
        (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) ihBody
      have replacementReturned := helper_capture .normalize bodyBound state [v "quote", v "drop", v "replacement"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternValue replacement]
        (patternValue replacementResult) rfl
        (by simp [bodyBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) ihReplacement
      simp only [ReflectiveSubstitution.normalizeReflective]
      apply helper_case .normalize state values "pattern" (patternValue (.subst body replacement))
        normalizeRows selected normalizeRow5 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold normalizeRow5
        apply PureData.let_bindings_return (pairs :=
          [(v "value", a Helper.normalize.head [v "quote", v "drop", v "body"]),
           (v "replacement-value", a Helper.normalize.head [v "quote", v "drop", v "replacement"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := bodyBound) bodyReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              bodyBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) replacementReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, bodyBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, bodyBound, bodyResult, replacementResult] using
            PureData.template_return runtime final state (a "PSubst" [v "value", v "replacement-value"])
              (data_constructor "PSubst" ["value", "replacement-value"] (by decide))
  | hcollection kind elements rest ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        patternValue (.collection kind elements rest)]
      let caller := environment .normalize values
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      let results := elements.map (ReflectiveSubstitution.normalizeReflective declaration)
      let final := ("values", patternsValue results) :: selected
      simp only [ReflectiveSubstitution.normalizeReflective, normalize_list_map]
      apply helper_case .normalize state values "pattern" (patternValue (.collection kind elements rest))
        normalizeRows selected normalizeRow6 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [normalizeRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold normalizeRow6
        apply named_let_returns selected state "values" _ (patternsValue results) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .normalizeList selected state _ _ _ rfl _
            (normalize_list_returns_from_elements state declaration elements ih)
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, results] using
            PureData.template_return runtime final state (a "PCollection" [v "kind", v "values", v "rest"])
              (data_constructor "PCollection" ["kind", "values", "rest"] (by decide))

/-! ## The binder head of a normalized name -/

private def headValue : ReflectiveSubstitution.BinderHead → Atom
  | .index level => a "BinderIndex" [number level]
  | .unit => .symbol "BinderUnit"
  | .drop name => a "BinderDrop" [headValue name]
  | .opaque => .symbol "BinderOpaque"

private def headsValue : List ReflectiveSubstitution.BinderHead → Atom
  | [] => .symbol "LNil"
  | head :: rest => a "LCons" [headValue head, headsValue rest]

private abbrev kindValue (declaration : ReflectivePresentationDecl) : Atom :=
  encoded (InferenceCettaWire.encodeCollectionType declaration.parallelCollection)

attribute [local simp] headsValue headValue kindValue

private theorem head_template (head : String) (names : List String)
    (constructor : head ∈ ["BinderIndex", "BinderDrop", "Var"]) :
    PureData.Template runtime (a head (names.map v)) := by
  apply constructor_variables head names
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
    rcases constructor with rfl | rfl | rfl <;> (decide +kernel)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
    rcases constructor with rfl | rfl | rfl <;> decide

private theorem join_inner_unit (selected : Subst) :
    SpaceSemantics.selectCase selected (headValue .unit) joinInnerRows = some (selected, v "left") := by
  simp [joinInnerRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]

private theorem join_returns (state : State) (left right : ReflectiveSubstitution.BinderHead) :
    PureReturns runtime [] state (a Helper.binderHeadJoin.head [headValue left, headValue right]) state
      (headValue (ReflectiveSubstitution.BinderHead.join left right)) := by
  let values := [headValue left, headValue right]
  let caller := environment .binderHeadJoin values
  by_cases unitLeft : left = .unit
  · subst unitLeft
    apply helper_case .binderHeadJoin state values "left" (headValue .unit) joinRows caller (v "right") _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [joinRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, caller]
    · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns runtime caller state "right"
  · let selected := ("present", headValue left) :: caller
    have rightSelected : PureReturns runtime selected state (v "right") state (headValue right) := by
      simpa [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns runtime selected state "right"
    apply helper_case .binderHeadJoin state values "left" (headValue left) joinRows selected
      (a "case" [v "right", .expression (joinInnerRows.map fun row => .expression [row.1, row.2])]) _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · cases left <;> simp_all [joinRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        matchAtom, selected, caller, values, environment,
        Helper.names, Subst.lookup]
    · by_cases unitRight : right = .unit
      · subst unitRight
        have leftReturned : PureReturns runtime selected state (v "left") state (headValue left) := by
          simpa [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns runtime selected state "left"
        simpa using branch_returns selected selected state (v "right") (headValue .unit) joinInnerRows
          (v "left") (headValue left) rightSelected (join_inner_unit selected) leftReturned
      · let other := ("other", headValue right) :: selected
        have otherMatched : SpaceSemantics.selectCase selected (headValue right) joinInnerRows =
            some (other, .symbol "BinderOpaque") := by
          cases right <;> simp_all [joinInnerRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            matchAtom, other, selected, caller, values, environment,
            Helper.names, Subst.lookup]
        rw [ReflectiveSubstitution.BinderHead.join_of_ne_unit unitLeft unitRight]
        exact branch_returns selected other state (v "right") (headValue right) joinInnerRows
          (.symbol "BinderOpaque") (.symbol "BinderOpaque") rightSelected otherMatched
          (symbol_returns runtime other state "BinderOpaque")

private theorem fold_returns (state : State) (heads : List ReflectiveSubstitution.BinderHead) :
    PureReturns runtime [] state (a Helper.binderHeadFold.head [headsValue heads]) state
      (headValue (heads.foldr ReflectiveSubstitution.BinderHead.join .unit)) := by
  induction heads with
  | nil =>
      let values := [headsValue []]
      apply helper_case .binderHeadFold state values "heads" (.symbol "LNil") foldRows
        (environment .binderHeadFold values) (.symbol "BinderUnit") _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [foldRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [CettaWireAtom.encode] using symbol_returns runtime _ state "BinderUnit"
  | cons head rest ih =>
      let values := [headsValue (head :: rest)]
      let caller := environment .binderHeadFold values
      let selected := ("rest", headsValue rest) :: ("head", headValue head) :: caller
      let tail := rest.foldr ReflectiveSubstitution.BinderHead.join .unit
      let final := ("tail", headValue tail) :: selected
      apply helper_case .binderHeadFold state values "heads" (headsValue (head :: rest)) foldRows
        selected (a "let" [v "tail", a Helper.binderHeadFold.head [v "rest"],
          a Helper.binderHeadJoin.head [v "head", v "tail"]]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [foldRows, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected,
          caller, values, environment, Helper.names, Helper.head, Subst.lookup]
      · simp only [List.foldr_cons]
        apply named_let_returns selected state "tail" _ (headValue tail) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · exact helper_capture .binderHeadFold selected state [v "rest"] [headsValue rest] _ rfl
            (by simp [selected, applySubst, Subst.lookup]) ih
        · exact helper_capture .binderHeadJoin final state [v "head", v "tail"]
            [headValue head, headValue tail] _ rfl
            (by simp [final, selected, applySubst, Subst.lookup]) (join_returns state head tail)

private theorem apply_nil_returns (state : State) (declaration : ReflectivePresentationDecl) (constructor : String) :
    PureReturns runtime [] state
      (a Helper.binderHeadApply.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue declaration.parallelUnitConstructor,
        textValue constructor, headsValue []]) state
      (headValue (ReflectiveSubstitution.BinderHead.apply declaration constructor [])) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    textValue declaration.parallelUnitConstructor, textValue constructor, headsValue []]
  let caller := environment .binderHeadApply values
  apply helper_case .binderHeadApply state values "heads" (headsValue []) applyRows caller
    (a "if" [a "==" [v "constructor", v "parallel-unit"], .symbol "BinderUnit", .symbol "BinderOpaque"]) _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · simp [applyRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, caller]
  · apply bool_if_returns caller state _ (constructor == declaration.parallelUnitConstructor) _ _ _
    · apply strings_equal_returns caller state constructor declaration.parallelUnitConstructor
        "constructor" "parallel-unit"
      · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · by_cases unitHead : constructor = declaration.parallelUnitConstructor
      · simpa [ReflectiveSubstitution.BinderHead.apply, ReflectiveSubstitution.BinderHead.rigid,
          unitHead] using symbol_returns runtime caller state "BinderUnit"
      · simpa [ReflectiveSubstitution.BinderHead.apply, ReflectiveSubstitution.BinderHead.rigid,
          unitHead] using symbol_returns runtime caller state "BinderOpaque"

private theorem apply_drop_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (name : ReflectiveSubstitution.BinderHead) :
    PureReturns runtime [] state
      (a Helper.binderHeadApply.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue declaration.parallelUnitConstructor,
        textValue constructor, headsValue [.drop name]]) state
      (headValue (ReflectiveSubstitution.BinderHead.apply declaration constructor [.drop name])) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    textValue declaration.parallelUnitConstructor, textValue constructor, headsValue [.drop name]]
  let caller := environment .binderHeadApply values
  let selected := ("name", headValue name) :: caller
  have nameBound : applySubst selected (v "name") = headValue name := by
    simp [selected, applySubst, Subst.lookup]
  apply helper_case .binderHeadApply state values "heads" (headsValue [.drop name]) applyRows selected
    (a "if" [a "==" [v "constructor", v "quote"], v "name",
      a "if" [a "==" [v "constructor", v "drop"], a "BinderDrop" [a "BinderDrop" [v "name"]],
        .symbol "BinderOpaque"]]) _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · simp [applyRows, CettaWireAtom.encode, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected,
      caller, values, environment, Helper.names, Subst.lookup]
  · apply bool_if_returns selected state _ (constructor == declaration.quoteConstructor) _ _ _
    · apply strings_equal_returns selected state constructor declaration.quoteConstructor
        "constructor" "quote"
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · by_cases quoted : constructor = declaration.quoteConstructor
      · simpa [ReflectiveSubstitution.BinderHead.apply, quoted, nameBound] using
          variable_returns runtime selected state "name"
      · simp only [quoted, beq_iff_eq, if_false]
        apply bool_if_returns selected state _ (constructor == declaration.dropConstructor) _ _ _
        · apply strings_equal_returns selected state constructor declaration.dropConstructor
            "constructor" "drop"
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · by_cases dropped : constructor = declaration.dropConstructor
          · have nested : PureData.Template runtime (a "BinderDrop" [a "BinderDrop" [v "name"]]) := by
              apply PureData.Template.constructor "BinderDrop" _ (by decide +kernel) (by decide)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              subst member
              exact head_template "BinderDrop" ["name"] (by decide)
            have dropNotQuote : declaration.dropConstructor ≠ declaration.quoteConstructor :=
              dropped ▸ quoted
            simpa [ReflectiveSubstitution.BinderHead.apply, ReflectiveSubstitution.BinderHead.rigid, quoted, dropped, dropNotQuote, applySubst,
              applySubst.applySubstList, selected, Subst.lookup] using
              PureData.template_return runtime selected state _ nested
          · simpa [ReflectiveSubstitution.BinderHead.apply, ReflectiveSubstitution.BinderHead.rigid,
              quoted, dropped] using symbol_returns runtime selected state "BinderOpaque"

private theorem apply_single_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (argument : ReflectiveSubstitution.BinderHead)
    (undropped : ∀ name, argument ≠ .drop name) :
    PureReturns runtime [] state
      (a Helper.binderHeadApply.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue declaration.parallelUnitConstructor,
        textValue constructor, headsValue [argument]]) state
      (headValue (ReflectiveSubstitution.BinderHead.apply declaration constructor [argument])) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    textValue declaration.parallelUnitConstructor, textValue constructor, headsValue [argument]]
  let caller := environment .binderHeadApply values
  let selected := ("argument", headValue argument) :: caller
  have rigid : ReflectiveSubstitution.BinderHead.apply declaration constructor [argument] =
      ReflectiveSubstitution.BinderHead.rigid declaration constructor [argument] := by
    cases argument <;> first
      | exact absurd rfl (undropped _)
      | simp [ReflectiveSubstitution.BinderHead.apply]
  rw [rigid]
  apply helper_case .binderHeadApply state values "heads" (headsValue [argument]) applyRows selected
    (a "if" [a "==" [v "constructor", v "drop"], a "BinderDrop" [v "argument"], .symbol "BinderOpaque"]) _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · cases argument <;> first
      | exact absurd rfl (undropped _)
      | simp [applyRows, CettaWireAtom.encode, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected,
          caller, values, environment, Helper.names, Subst.lookup]
  · apply bool_if_returns selected state _ (constructor == declaration.dropConstructor) _ _ _
    · apply strings_equal_returns selected state constructor declaration.dropConstructor
        "constructor" "drop"
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · by_cases dropped : constructor = declaration.dropConstructor
      · simpa [ReflectiveSubstitution.BinderHead.rigid, dropped, applySubst, applySubst.applySubstList,
          selected, Subst.lookup] using
          PureData.template_return runtime selected state (a "BinderDrop" [v "argument"])
            (head_template "BinderDrop" ["argument"] (by decide))
      · simpa [ReflectiveSubstitution.BinderHead.rigid, dropped] using
          symbol_returns runtime selected state "BinderOpaque"

private theorem apply_many_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (first second : ReflectiveSubstitution.BinderHead)
    (rest : List ReflectiveSubstitution.BinderHead) :
    PureReturns runtime [] state
      (a Helper.binderHeadApply.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue declaration.parallelUnitConstructor,
        textValue constructor, headsValue (first :: second :: rest)]) state
      (headValue (ReflectiveSubstitution.BinderHead.apply declaration constructor (first :: second :: rest))) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    textValue declaration.parallelUnitConstructor, textValue constructor, headsValue (first :: second :: rest)]
  let caller := environment .binderHeadApply values
  let selected := ("many", headsValue (first :: second :: rest)) :: caller
  have isOpaque : ReflectiveSubstitution.BinderHead.apply declaration constructor (first :: second :: rest) =
      .opaque := by
    cases first <;> simp [ReflectiveSubstitution.BinderHead.apply, ReflectiveSubstitution.BinderHead.rigid]
  rw [isOpaque]
  apply helper_case .binderHeadApply state values "heads" (headsValue (first :: second :: rest)) applyRows
    selected (.symbol "BinderOpaque") _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · cases first <;> simp [applyRows, CettaWireAtom.encode, 
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
  · exact symbol_returns runtime selected state "BinderOpaque"

private theorem apply_returns (state : State) (declaration : ReflectivePresentationDecl) (constructor : String)
    (heads : List ReflectiveSubstitution.BinderHead) :
    PureReturns runtime [] state
      (a Helper.binderHeadApply.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, textValue declaration.parallelUnitConstructor,
        textValue constructor, headsValue heads]) state
      (headValue (ReflectiveSubstitution.BinderHead.apply declaration constructor heads)) := by
  rcases heads with _ | ⟨argument, _ | ⟨second, rest⟩⟩
  · exact apply_nil_returns state declaration constructor
  · by_cases dropped : ∃ name, argument = .drop name
    · obtain ⟨name, rfl⟩ := dropped
      exact apply_drop_returns state declaration constructor name
    · exact apply_single_returns state declaration constructor argument
        (fun name same => dropped ⟨name, same⟩)
  · exact apply_many_returns state declaration constructor argument second rest

private theorem kind_equal (left right : CollType) :
    decide (InferenceCettaWire.encodeCollectionType left = InferenceCettaWire.encodeCollectionType right) =
      decide (left = right) := by
  cases left <;> cases right <;> simp [InferenceCettaWire.encodeCollectionType]

private theorem binder_head_list_returns_from_elements (state : State)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a Helper.binderHead.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (headValue (ReflectiveSubstitution.BinderHead.ofPattern declaration pattern))) :
    PureReturns runtime [] state
      (a Helper.binderHeadList.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue patterns]) state
      (headsValue (patterns.map (ReflectiveSubstitution.BinderHead.ofPattern declaration))) := by
  induction patterns with
  | nil =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue []]
      apply helper_case .binderHeadList state values "patterns" (.symbol "LNil") binderHeadListRows
        (environment .binderHeadList values) (.symbol "LNil") _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [binderHeadListRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa using symbol_returns runtime _ state "LNil"
  | cons pattern patterns ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue (pattern :: patterns)]
      let caller := environment .binderHeadList values
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let first := headValue (ReflectiveSubstitution.BinderHead.ofPattern declaration pattern)
      let firstBound := ("head", first) :: selected
      let restValue := headsValue (patterns.map (ReflectiveSubstitution.BinderHead.ofPattern declaration))
      let final := ("tail", restValue) :: firstBound
      have firstReturned := helper_capture .binderHead selected state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]
        first rfl (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have restReturned := helper_capture .binderHeadList firstBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue patterns]
        restValue rfl (by simp [firstBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply helper_case .binderHeadList state values "patterns" (patternsValue (pattern :: patterns))
        binderHeadListRows selected
        (a "let*" [.expression [.expression [v "head", a Helper.binderHead.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]],
          .expression [v "tail", a Helper.binderHeadList.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"]]],
          a "LCons" [v "head", v "tail"]]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [binderHeadListRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Helper.head, Subst.lookup]
      · apply PureData.let_bindings_return (pairs :=
          [(v "head", a Helper.binderHead.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]),
           (v "tail", a Helper.binderHeadList.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := firstBound) firstReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              firstBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) restReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, firstBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [List.map_cons, applySubst, applySubst.applySubstList, Subst.lookup,
            final, firstBound, first, restValue] using
            PureData.template_return runtime final state (a "LCons" [v "head", v "tail"])
              (data_constructor "LCons" ["head", "tail"] (by decide))

private theorem opaque_head_returns (state : State) (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) (selected : Subst)
    (matched : SpaceSemantics.selectCase (environment .binderHead
      [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern])
      (patternValue pattern) binderHeadRows = some (selected, .symbol "BinderOpaque"))
    (isOpaque : ReflectiveSubstitution.BinderHead.ofPattern declaration pattern = .opaque) :
    PureReturns runtime [] state
      (a Helper.binderHead.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (headValue (ReflectiveSubstitution.BinderHead.ofPattern declaration pattern)) := by
  rw [isOpaque]
  apply helper_case .binderHead state _ "pattern" (patternValue pattern) binderHeadRows selected
    (.symbol "BinderOpaque") _ rfl rfl
  · simp [environment, Helper.names, applySubst, Subst.lookup]
  · exact matched
  · exact symbol_returns runtime selected state "BinderOpaque"

theorem binder_head_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns runtime [] state
      (a Helper.binderHead.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (headValue (ReflectiveSubstitution.BinderHead.ofPattern declaration pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.bvar index)]
      let caller := environment .binderHead values
      let selected := ("index", number index) :: caller
      apply helper_case .binderHead state values "pattern" (patternValue (.bvar index))
        binderHeadRows selected (a "BinderIndex" [v "index"]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [ReflectiveSubstitution.BinderHead.ofPattern, applySubst, applySubst.applySubstList,
          Subst.lookup, selected] using
          PureData.template_return runtime selected state (a "BinderIndex" [v "index"])
            (head_template "BinderIndex" ["index"] (by decide))
  | hfvar name =>
      apply opaque_head_returns state declaration _ (("other", patternValue (.fvar name)) ::
        environment .binderHead [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.fvar name)])
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.BinderHead.ofPattern]
  | happly head children ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.apply head children)]
      let caller := environment .binderHead values
      let selected := ("children", patternsValue children) :: ("head", textValue head) :: caller
      let heads := children.map (ReflectiveSubstitution.BinderHead.ofPattern declaration)
      let final := ("heads", headsValue heads) :: selected
      simp only [ReflectiveSubstitution.BinderHead.ofPattern, ReflectiveSubstitution.BinderHead.ofList_eq_map]
      apply helper_case .binderHead state values "pattern" (patternValue (.apply head children))
        binderHeadRows selected
        (a "let" [v "heads", a Helper.binderHeadList.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "children"],
          a Helper.binderHeadApply.head [v "quote", v "drop", v "parallel-unit", v "head", v "heads"]]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Helper.head, Subst.lookup]
      · apply named_let_returns selected state "heads" _ (headsValue heads) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .binderHeadList selected state _ _ _ rfl _
            (binder_head_list_returns_from_elements state declaration children ih)
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · apply helper_capture .binderHeadApply final state _ _ _ rfl _
            (apply_returns state declaration head heads)
          simp [final, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  | hlambda binder body _ =>
      apply opaque_head_returns state declaration _ (("other", patternValue (.lambda binder body)) ::
        environment .binderHead [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.lambda binder body)])
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.BinderHead.ofPattern]
  | hmultiLambda arity binders body _ =>
      apply opaque_head_returns state declaration _ (("other", patternValue (.multiLambda arity binders body)) ::
        environment .binderHead [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor,
          patternValue (.multiLambda arity binders body)])
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.BinderHead.ofPattern]
  | hsubst body replacement _ _ =>
      apply opaque_head_returns state declaration _ (("other", patternValue (.subst body replacement)) ::
        environment .binderHead [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.subst body replacement)])
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.BinderHead.ofPattern]
  | hcollection kind elements rest ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue (.collection kind elements rest)]
      let caller := environment .binderHead values
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) ::
        ("collection", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      let heads := elements.map (ReflectiveSubstitution.BinderHead.ofPattern declaration)
      apply helper_case .binderHead state values "pattern" (patternValue (.collection kind elements rest))
        binderHeadRows selected
        (a "if" [a "==" [v "collection", v "parallel-kind"],
          a "case" [v "rest", .expression (collectionRestRows.map fun row => .expression [row.1, row.2])],
          .symbol "BinderOpaque"]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [binderHeadRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · apply bool_if_returns selected state _ (decide (kind = declaration.parallelCollection)) _ _ _
        · rw [← kind_equal]
          apply CettaWireAtom.equality_captured_returns runtime selected state
            (InferenceCettaWire.encodeCollectionType kind)
            (InferenceCettaWire.encodeCollectionType declaration.parallelCollection) "collection" "parallel-kind"
          · simp [selected, applySubst, Subst.lookup]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · by_cases parallel : kind = declaration.parallelCollection
          · rw [if_pos (decide_eq_true parallel)]
            have restReturned : PureReturns runtime selected state (v "rest") state
                (encoded (InferenceCettaWire.encodeRest rest)) := by
              simpa [selected, applySubst, Subst.lookup] using variable_returns runtime selected state "rest"
            cases rest with
            | none =>
                let final := ("heads", headsValue heads) :: selected
                have folded : PureReturns runtime selected state
                    (a "let" [v "heads", a Helper.binderHeadList.head [v "quote", v "drop", v "parallel-kind",
                        v "parallel-unit", v "elements"], a Helper.binderHeadFold.head [v "heads"]]) state
                    (headValue (heads.foldr ReflectiveSubstitution.BinderHead.join .unit)) := by
                  apply named_let_returns selected state "heads" _ (headsValue heads) _ _
                  · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
                  · apply helper_capture .binderHeadList selected state _ _ _ rfl _
                      (binder_head_list_returns_from_elements state declaration elements ih)
                    simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
                  · exact helper_capture .binderHeadFold final state [v "heads"] [headsValue heads] _ rfl
                      (by simp [final, applySubst, Subst.lookup]) (fold_returns state heads)
                have matched : SpaceSemantics.selectCase selected (encoded (InferenceCettaWire.encodeRest none))
                    collectionRestRows = some (selected, a "let" [v "heads", a Helper.binderHeadList.head
                      [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "elements"],
                      a Helper.binderHeadFold.head [v "heads"]]) := by
                  simp [collectionRestRows, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Helper.head]
                simpa [ReflectiveSubstitution.BinderHead.ofPattern, ReflectiveSubstitution.BinderHead.ofList_eq_map, parallel, heads] using
                  branch_returns selected selected state (v "rest") _ collectionRestRows _ _
                    restReturned matched folded
            | some restName =>
                let other := ("open", encoded (InferenceCettaWire.encodeRest (some restName))) :: selected
                have matched : SpaceSemantics.selectCase selected
                    (encoded (InferenceCettaWire.encodeRest (some restName))) collectionRestRows =
                      some (other, .symbol "BinderOpaque") := by
                  simp [collectionRestRows, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    matchAtom, other, selected, caller, values,
                    environment, Helper.names, Subst.lookup]
                simpa [ReflectiveSubstitution.BinderHead.ofPattern] using
                  branch_returns selected other state (v "rest") _ collectionRestRows _ _
                    restReturned matched (symbol_returns runtime other state "BinderOpaque")
          · have isOpaque : ReflectiveSubstitution.BinderHead.ofPattern declaration (.collection kind elements rest) = .opaque := by
              cases rest <;> simp [ReflectiveSubstitution.BinderHead.ofPattern, parallel]
            rw [isOpaque, if_neg (by simpa using parallel)]
            exact symbol_returns runtime selected state "BinderOpaque"

private theorem nonunary_selection (caller : Subst) (pattern : Pattern)
    (first second fallback : String) (yes no : Atom)
    (freshFallback : Subst.lookup caller fallback = none)
    (nonunary : ¬∃ head payload, pattern = .apply head [payload]) :
    SpaceSemantics.selectCase caller (patternValue pattern)
      [(a "PApp" [v first, a "LCons" [v second, .symbol "LNil"]], yes), (v fallback, no)] =
      some ((fallback, patternValue pattern) :: caller, no) := by
  cases pattern with
  | apply head children =>
      cases children with
      | nil => simp [InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          freshFallback]
      | cons payload rest =>
          cases rest with
          | nil => exact False.elim (nonunary ⟨head, payload, rfl⟩)
          | cons child rest => simp [InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              freshFallback]
  | bvar _ | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
      simp [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, freshFallback]

private theorem unary_template (headName payloadName : String) :
    PureData.Template runtime (a "PApp" [v headName, a "LCons" [v payloadName, .symbol "LNil"]]) := by
  apply PureData.Template.constructor "PApp" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .captured headName
  · apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .captured payloadName
    · exact .symbol "LNil"

private theorem unary_constructor_returns (caller : Subst) (state : State) (head payload : String)
    (constructor : String) (pattern : Pattern)
    (headCaptured : applySubst caller (v head) = textValue constructor)
    (payloadCaptured : applySubst caller (v payload) = patternValue pattern) :
    PureReturns runtime caller state (a "PApp" [v head, a "LCons" [v payload, .symbol "LNil"]]) state
      (patternValue (.apply constructor [pattern])) := by
  have same : applySubst caller (a "PApp" [v head, a "LCons" [v payload, .symbol "LNil"]]) =
      patternValue (.apply constructor [pattern]) := by
    change a "PApp" [applySubst caller (v head), a "LCons" [applySubst caller (v payload), .symbol "LNil"]] = _
    rw [headCaptured, payloadCaptured]
    simp [InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]
  simpa only [same] using PureData.template_return runtime caller state _ (unary_template head payload)

private theorem replacement_nonunary_result (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) (nonunary : ¬∃ head payload, pattern = .apply head [payload]) :
    ReflectiveSubstitution.normalizeReflectiveReplacement declaration pattern =
      ReflectiveSubstitution.normalizeReflective declaration pattern := by
  cases pattern <;> try rfl
  rename_i head children
  cases children with
  | nil => rfl
  | cons payload rest =>
      cases rest with
      | nil => exact False.elim (nonunary ⟨head, payload, rfl⟩)
      | cons child rest => rfl

private theorem receive_nonunary (declaration : ReflectivePresentationDecl) (constructor : String)
    (name : Pattern) (nonunary : ¬∃ quote process, name = .apply quote [process]) :
    ReflectiveSubstitution.receive declaration constructor name = .apply constructor [name] := by
  unfold ReflectiveSubstitution.receive
  split
  · rename_i quote process
    exact False.elim (nonunary ⟨quote, process, rfl⟩)
  · rfl

theorem replacement_returns (state : State) (declaration : ReflectivePresentationDecl) (replacement : Pattern) :
    PureReturns runtime [] state
      (a Helper.replacement.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, patternValue replacement]) state
      (patternValue (ReflectiveSubstitution.normalizeReflectiveReplacement declaration replacement)) := by
  by_cases unary : ∃ head payload, replacement = .apply head [payload]
  · obtain ⟨head, payload, rfl⟩ := unary
    let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
      patternValue (.apply head [payload])]
    let caller := environment .replacement values
    let selected := ("payload", patternValue payload) :: ("head", textValue head) :: caller
    let result := ReflectiveSubstitution.normalizeReflective declaration payload
    let final := ("value", patternValue result) :: selected
    apply helper_case .replacement state values "replacement" (patternValue (.apply head [payload]))
      replacementRows selected replacementRow0 _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [replacementRows, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        selected, caller, values, environment, Helper.names, Subst.lookup]
    · unfold replacementRow0
      apply bool_if_returns selected state _ (head == declaration.quoteConstructor) _ _ _
      · apply strings_equal_returns selected state head declaration.quoteConstructor "head" "quote"
        · simp [selected, applySubst, Subst.lookup]
        · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · unfold ReflectiveSubstitution.normalizeReflectiveReplacement
        by_cases quoted : head == declaration.quoteConstructor
        · simp only [quoted, ite_true]
          apply named_let_returns selected state "value" _ (patternValue result) _ _
          · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
          · apply helper_capture .normalize selected state _ _ _ rfl _ (normalize_returns state declaration payload)
            simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · apply unary_constructor_returns final state "head" "value" head result
            · simp [final, selected, applySubst, Subst.lookup]
            · simp [final, applySubst, Subst.lookup]
        · simp only [quoted, Bool.false_eq_true, ite_false]
          apply helper_capture .normalize selected state _ _ _ rfl _
            (normalize_returns state declaration (.apply head [payload]))
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternValue replacement]
    let caller := environment .replacement values
    let selected := ("ordinary", patternValue replacement) :: caller
    rw [replacement_nonunary_result declaration replacement unary]
    apply helper_case .replacement state values "replacement" (patternValue replacement)
      replacementRows selected replacementRow1 _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · apply nonunary_selection caller replacement "head" "payload" "ordinary" replacementRow0 replacementRow1
      · simp [caller, values, environment, Helper.names, Subst.lookup]
      · exact unary
    · unfold replacementRow1
      apply helper_capture .normalize selected state _ _ _ rfl _ (normalize_returns state declaration replacement)
      simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]

/-! ## Resolving quotations of drops -/

private def optionValue : Option Pattern → Atom
  | none => .symbol "None"
  | some name => a "Some" [patternValue name]

/-- What a bound index becomes when the binder at `level` is eliminated. -/
private abbrev eliminate (replacement : Pattern) (level index : Nat) : Pattern :=
  Substitution.instantiateBVarAt level replacement (.bvar index)

/-- The runtime spelling of what substitution does at a genuine quotation. -/
private def modeValue : Option Pattern → Atom
  | none => .symbol "Opaque"
  | some value => a "Enter" [patternValue value]

/-- Substitution in a resolved term at a mode: `none` keeps every genuine
quotation opaque; `some value` enters it, with `value` as the selected binder's
value inside. -/
private def substituteMode (declaration : ReflectivePresentationDecl) :
    Option Pattern → Pattern → Nat → Pattern → Pattern
  | none, replacement, depth, pattern =>
      ReflectiveSubstitution.substituteResolved declaration (eliminate replacement) depth pattern
  | some value, replacement, depth, pattern =>
      ReflectiveSubstitution.substituteViewed declaration (eliminate value) (eliminate replacement) depth pattern

section Mode

variable (declaration : ReflectivePresentationDecl) (mode : Option Pattern) (replacement : Pattern)

private theorem mode_bvar (depth index : Nat) :
    substituteMode declaration mode replacement depth (.bvar index) = eliminate replacement depth index := by
  cases mode <;> rfl

private theorem mode_fvar (depth : Nat) (name : String) :
    substituteMode declaration mode replacement depth (.fvar name) = .fvar name := by
  cases mode <;> rfl

private theorem mode_lambda (depth : Nat) (binder : Option String) (body : Pattern) :
    substituteMode declaration mode replacement depth (.lambda binder body) =
      .lambda binder (substituteMode declaration mode replacement (depth + 1) body) := by
  cases mode <;> rfl

private theorem mode_multiLambda (depth arity : Nat) (binders : List String) (body : Pattern) :
    substituteMode declaration mode replacement depth (.multiLambda arity binders body) =
      .multiLambda arity binders (substituteMode declaration mode replacement (depth + arity) body) := by
  cases mode <;> rfl

private theorem mode_subst (depth : Nat) (body value : Pattern) :
    substituteMode declaration mode replacement depth (.subst body value) =
      .subst (substituteMode declaration mode replacement (depth + 1) body)
        (substituteMode declaration mode replacement depth value) := by
  cases mode <;> rfl

private theorem mode_collection (depth : Nat) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    substituteMode declaration mode replacement depth (.collection kind elements rest) =
      .collection kind (elements.map (substituteMode declaration mode replacement depth)) rest := by
  cases mode <;>
    simp [substituteMode, ReflectiveSubstitution.substituteResolved, ReflectiveSubstitution.substituteViewed,
      ReflectiveSubstitution.substituteResolvedList_eq_map, ReflectiveSubstitution.substituteViewedList_eq_map]

private theorem mode_apply_of_ne_one (depth : Nat) (head : String) {children : List Pattern}
    (notOne : ¬∃ payload, children = [payload]) :
    substituteMode declaration mode replacement depth (.apply head children) =
      .apply head (children.map (substituteMode declaration mode replacement depth)) := by
  rcases children with _ | ⟨payload, _ | ⟨second, rest⟩⟩
  · cases mode <;> rfl
  · exact False.elim (notOne ⟨payload, rfl⟩)
  · cases mode <;>
      simp [substituteMode, ReflectiveSubstitution.substituteResolved, ReflectiveSubstitution.substituteViewed,
        ReflectiveSubstitution.substituteResolvedList_eq_map, ReflectiveSubstitution.substituteViewedList_eq_map]

private theorem mode_unary_of_ne (depth : Nat) {head : String} (payload : Pattern)
    (notQuote : head ≠ declaration.quoteConstructor) :
    substituteMode declaration mode replacement depth (.apply head [payload]) =
      if head = declaration.dropConstructor then
        if ReflectiveSubstitution.matchesBinder declaration depth payload then
          ReflectiveSubstitution.receive declaration head (eliminate replacement depth depth)
        else .apply head [substituteMode declaration mode replacement depth payload]
      else .apply head [substituteMode declaration mode replacement depth payload] := by
  cases mode <;>
    simp only [substituteMode, ReflectiveSubstitution.substituteResolved, ReflectiveSubstitution.substituteViewed,
      if_neg notQuote]

private theorem mode_quote_none (depth : Nat) (payload : Pattern) :
    substituteMode declaration none replacement depth (.apply declaration.quoteConstructor [payload]) =
      .apply declaration.quoteConstructor [payload] := by
  simp [substituteMode, ReflectiveSubstitution.substituteResolved]

private theorem mode_quote_some (depth : Nat) (value payload : Pattern) :
    substituteMode declaration (some value) replacement depth (.apply declaration.quoteConstructor [payload]) =
      .apply declaration.quoteConstructor [substituteMode declaration (some value) value depth payload] := by
  simp [substituteMode, ReflectiveSubstitution.substituteViewed]

end Mode

private theorem singleton_template (name : String) :
    PureData.Template runtime (a "LCons" [v name, .symbol "LNil"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .captured name
  · exact .symbol "LNil"

private theorem singleton_returns (caller : Subst) (state : State) (name : String) (pattern : Pattern)
    (captured : applySubst caller (v name) = patternValue pattern) :
    PureReturns runtime caller state (a "LCons" [v name, .symbol "LNil"]) state (patternsValue [pattern]) := by
  have same : applySubst caller (a "LCons" [v name, .symbol "LNil"]) = patternsValue [pattern] := by
    change a "LCons" [applySubst caller (v name), .symbol "LNil"] = _
    rw [captured]
    simp [InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  simpa only [same] using PureData.template_return runtime caller state _ (singleton_template name)

private theorem receive_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (name : Pattern) :
    PureReturns runtime [] state
      (a Helper.receive.head [textValue declaration.quoteConstructor, textValue constructor, patternValue name]) state
      (patternValue (ReflectiveSubstitution.receive declaration constructor name)) := by
  let values := [textValue declaration.quoteConstructor, textValue constructor, patternValue name]
  let caller := environment .receive values
  by_cases unary : ∃ quote process, name = .apply quote [process]
  · obtain ⟨quote, process, rfl⟩ := unary
    let bound := ("process", patternValue process) :: ("inner-head", textValue quote) :: caller
    apply helper_case .receive state values "name" (patternValue (.apply quote [process])) receiveRows bound
      (a "if" [a "==" [v "inner-head", v "quote"], v "process",
        a "PApp" [v "head", a "LCons" [v "name", .symbol "LNil"]]]) _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [receiveRows, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        bound, caller, values, environment, Helper.names, Subst.lookup]
    · apply bool_if_returns bound state _ (quote == declaration.quoteConstructor) _ _ _
      · apply strings_equal_returns bound state quote declaration.quoteConstructor "inner-head" "quote"
        · simp [bound, applySubst, Subst.lookup]
        · simp [bound, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · by_cases quoted : quote = declaration.quoteConstructor
        · have equal : (quote == declaration.quoteConstructor) = true := by simp [quoted]
          simp only [equal, ite_true, ReflectiveSubstitution.receive, if_pos quoted]
          simpa [bound, applySubst, Subst.lookup] using variable_returns runtime bound state "process"
        · have unequal : (quote == declaration.quoteConstructor) = false := by simp [quoted]
          simp only [unequal, Bool.false_eq_true, ite_false, ReflectiveSubstitution.receive, if_neg quoted]
          apply unary_constructor_returns bound state "head" "name" constructor (.apply quote [process])
          · simp [bound, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · simp [bound, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · rw [receive_nonunary declaration constructor name unary]
    let bound := ("ordinary", patternValue name) :: caller
    apply helper_case .receive state values "name" (patternValue name) receiveRows bound
      (a "PApp" [v "head", a "LCons" [v "name", .symbol "LNil"]]) _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · apply nonunary_selection caller name "inner-head" "process" "ordinary" _ _
      · simp [caller, values, environment, Helper.names, Subst.lookup]
      · exact unary
    · apply unary_constructor_returns bound state "head" "name" constructor name
      · simp [bound, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [bound, caller, values, environment, Helper.names, applySubst, Subst.lookup]

private theorem append_returns (state : State) (left right : List Pattern) :
    PureReturns runtime [] state (a Helper.append.head [patternsValue left, patternsValue right]) state
      (patternsValue (left ++ right)) := by
  induction left with
  | nil =>
      let values := [patternsValue [], patternsValue right]
      apply helper_case .append state values "left" (.symbol "LNil") appendRows
        (environment .append values) (v "right") _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [appendRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [values, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime (environment .append values) state "right"
  | cons item rest ih =>
      let values := [patternsValue (item :: rest), patternsValue right]
      let caller := environment .append values
      let selected := ("rest", patternsValue rest) :: ("item", patternValue item) :: caller
      let final := ("tail", patternsValue (rest ++ right)) :: selected
      apply helper_case .append state values "left" (patternsValue (item :: rest)) appendRows
        selected appendRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [appendRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold appendRow1
        apply named_let_returns selected state "tail" _ (patternsValue (rest ++ right)) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .append selected state _ _ _ rfl _ ih
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [List.cons_append, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup, final,
            selected] using
            PureData.template_return runtime final state (a "LCons" [v "item", v "tail"])
              (data_constructor "LCons" ["item", "tail"] (by decide))

private theorem leaves_list_returns_from_elements (state : State)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a Helper.leaves.head [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue pattern]) state
      (patternsValue (ReflectiveSubstitution.parallelLeaves declaration pattern))) :
    PureReturns runtime [] state
      (a Helper.leavesList.head [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternsValue patterns]) state
      (patternsValue (ReflectiveSubstitution.parallelLeavesList declaration patterns)) := by
  induction patterns with
  | nil =>
      let values := [kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue []]
      apply helper_case .leavesList state values "patterns" (.symbol "LNil") leavesListRows
        (environment .leavesList values) (.symbol "LNil") _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [leavesListRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [ReflectiveSubstitution.parallelLeavesList, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode] using symbol_returns runtime _ state "LNil"
  | cons pattern patterns ih =>
      let values := [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternsValue (pattern :: patterns)]
      let caller := environment .leavesList values
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let first := ReflectiveSubstitution.parallelLeaves declaration pattern
      let firstBound := ("head", patternsValue first) :: selected
      let restLeaves := ReflectiveSubstitution.parallelLeavesList declaration patterns
      let final := ("tail", patternsValue restLeaves) :: firstBound
      have firstReturned := helper_capture .leaves selected state
        [v "parallel-kind", v "parallel-unit", v "pattern"]
        [kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]
        (patternsValue first) rfl
        (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have restReturned := helper_capture .leavesList firstBound state
        [v "parallel-kind", v "parallel-unit", v "rest"]
        [kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue patterns]
        (patternsValue restLeaves) rfl
        (by simp [firstBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      have appended := helper_capture .append final state [v "head", v "tail"]
        [patternsValue first, patternsValue restLeaves] _ rfl
        (by simp [final, firstBound, applySubst, Subst.lookup]) (append_returns state first restLeaves)
      apply helper_case .leavesList state values "patterns" (patternsValue (pattern :: patterns))
        leavesListRows selected leavesListRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [leavesListRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold leavesListRow1
        simp only [ReflectiveSubstitution.parallelLeavesList]
        apply PureData.let_bindings_return (pairs :=
          [(v "head", a Helper.leaves.head [v "parallel-kind", v "parallel-unit", v "pattern"]),
           (v "tail", a Helper.leavesList.head [v "parallel-kind", v "parallel-unit", v "rest"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := firstBound) firstReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              firstBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) restReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, firstBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · exact appended

private theorem leaves_other_returns (state : State) (declaration : ReflectivePresentationDecl)
    (pattern : Pattern)
    (matched : SpaceSemantics.selectCase (environment .leaves [kindValue declaration,
        textValue declaration.parallelUnitConstructor, patternValue pattern])
      (patternValue pattern) leavesRows =
        some (("other", patternValue pattern) :: environment .leaves [kindValue declaration,
          textValue declaration.parallelUnitConstructor, patternValue pattern],
          a "LCons" [v "pattern", .symbol "LNil"]))
    (single : ReflectiveSubstitution.parallelLeaves declaration pattern = [pattern]) :
    PureReturns runtime [] state
      (a Helper.leaves.head [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue pattern]) state
      (patternsValue (ReflectiveSubstitution.parallelLeaves declaration pattern)) := by
  rw [single]
  apply helper_case .leaves state _ "pattern" (patternValue pattern) leavesRows _ _ _ rfl rfl
  · simp [environment, Helper.names, applySubst, Subst.lookup]
  · exact matched
  · apply singleton_returns
    simp [environment, Helper.names, applySubst, Subst.lookup]

private theorem leaves_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns runtime [] state
      (a Helper.leaves.head [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue pattern]) state
      (patternsValue (ReflectiveSubstitution.parallelLeaves declaration pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      apply leaves_other_returns
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.parallelLeaves]
  | hfvar name =>
      apply leaves_other_returns
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.parallelLeaves]
  | happly head children _ =>
      let values := [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue (.apply head children)]
      let caller := environment .leaves values
      let selected := ("children", patternsValue children) :: ("head", textValue head) :: caller
      apply helper_case .leaves state values "pattern" (patternValue (.apply head children)) leavesRows selected
        (a "case" [v "children", .expression (leavesApplyRows.map fun row => .expression [row.1, row.2])]) _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · have childrenReturned : PureReturns runtime selected state (v "children") state (patternsValue children) := by
          simpa [selected, applySubst, Subst.lookup] using variable_returns runtime selected state "children"
        cases children with
        | nil =>
            have matched : SpaceSemantics.selectCase selected (patternsValue []) leavesApplyRows =
                some (selected, leavesUnitRow) := by
              simp [leavesApplyRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            apply branch_returns selected selected state (v "children") _ leavesApplyRows _ _ childrenReturned matched
            unfold leavesUnitRow
            apply bool_if_returns selected state _ (head == declaration.parallelUnitConstructor) _ _ _
            · apply strings_equal_returns selected state head declaration.parallelUnitConstructor "head" "parallel-unit"
              · simp [selected, applySubst, Subst.lookup]
              · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
            · by_cases unit : head = declaration.parallelUnitConstructor
              · have equal : (head == declaration.parallelUnitConstructor) = true := by simp [unit]
                simp only [equal, ite_true, ReflectiveSubstitution.parallelLeaves, if_pos unit]
                simpa [InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
                  symbol_returns runtime selected state "LNil"
              · have unequal : (head == declaration.parallelUnitConstructor) = false := by simp [unit]
                simp only [unequal, Bool.false_eq_true, ite_false, ReflectiveSubstitution.parallelLeaves,
                  if_neg unit]
                exact singleton_returns selected state "pattern" (.apply head [])
                  (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        | cons first rest =>
            let many := ("many", patternsValue (first :: rest)) :: selected
            have matched : SpaceSemantics.selectCase selected (patternsValue (first :: rest)) leavesApplyRows =
                some (many, a "LCons" [v "pattern", .symbol "LNil"]) := by
              simp [leavesApplyRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, many, selected, caller, values,
                environment, Helper.names, Subst.lookup]
            simp only [ReflectiveSubstitution.parallelLeaves]
            exact branch_returns selected many state (v "children") _ leavesApplyRows _ _ childrenReturned matched
              (singleton_returns many state "pattern" (.apply head (first :: rest))
                (by simp [many, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]))
  | hlambda binder body _ =>
      apply leaves_other_returns
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.parallelLeaves]
  | hmultiLambda arity binders body _ =>
      apply leaves_other_returns
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.parallelLeaves]
  | hsubst body replacement _ _ =>
      apply leaves_other_returns
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, environment, Helper.names, Subst.lookup]
      · simp [ReflectiveSubstitution.parallelLeaves]
  | hcollection kind elements rest ih =>
      let values := [kindValue declaration, textValue declaration.parallelUnitConstructor,
        patternValue (.collection kind elements rest)]
      let caller := environment .leaves values
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) ::
        ("collection", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      apply helper_case .leaves state values "pattern" (patternValue (.collection kind elements rest))
        leavesRows selected leavesCollectionRow _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [leavesRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold leavesCollectionRow
        apply bool_if_returns selected state _ (decide (kind = declaration.parallelCollection)) _ _ _
        · rw [← kind_equal]
          apply CettaWireAtom.equality_captured_returns runtime selected state
            (InferenceCettaWire.encodeCollectionType kind)
            (InferenceCettaWire.encodeCollectionType declaration.parallelCollection) "collection" "parallel-kind"
          · simp [selected, applySubst, Subst.lookup]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · by_cases parallel : kind = declaration.parallelCollection
          · rw [if_pos (decide_eq_true parallel)]
            have restReturned : PureReturns runtime selected state (v "rest") state
                (encoded (InferenceCettaWire.encodeRest rest)) := by
              simpa [selected, applySubst, Subst.lookup] using variable_returns runtime selected state "rest"
            cases rest with
            | none =>
                have matched : SpaceSemantics.selectCase selected (encoded (InferenceCettaWire.encodeRest none))
                    leavesRestRows = some (selected, a Helper.leavesList.head
                      [v "parallel-kind", v "parallel-unit", v "elements"]) := by
                  simp [leavesRestRows, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Helper.head]
                simp only [ReflectiveSubstitution.parallelLeaves, if_pos parallel]
                exact branch_returns selected selected state (v "rest") _ leavesRestRows _ _ restReturned matched
                  (helper_capture .leavesList selected state _ _ _ rfl
                    (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                    (leaves_list_returns_from_elements state declaration elements ih))
            | some restName =>
                let other := ("open", encoded (InferenceCettaWire.encodeRest (some restName))) :: selected
                have matched : SpaceSemantics.selectCase selected
                    (encoded (InferenceCettaWire.encodeRest (some restName))) leavesRestRows =
                      some (other, a "LCons" [v "pattern", .symbol "LNil"]) := by
                  simp [leavesRestRows, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    matchAtom, other, selected, caller, values, environment, Helper.names, Subst.lookup]
                simp only [ReflectiveSubstitution.parallelLeaves]
                exact branch_returns selected other state (v "rest") _ leavesRestRows _ _ restReturned matched
                  (singleton_returns other state "pattern" _
                    (by simp [other, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]))
          · rw [if_neg (by simpa using parallel)]
            have single : ReflectiveSubstitution.parallelLeaves declaration (.collection kind elements rest) =
                [.collection kind elements rest] := by
              cases rest <;> simp [ReflectiveSubstitution.parallelLeaves, parallel]
            rw [single]
            exact singleton_returns selected state "pattern" _
              (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])

private theorem lookup_cons (key name : String) (value : Atom) (rest : Subst) :
    Subst.lookup ((key, value) :: rest) name = if key = name then some value else Subst.lookup rest name := by
  unfold Subst.lookup
  by_cases same : key = name
  · simp [same]
  · have different : (key == name) = false := beq_false_of_ne same
    simp [List.find?, different, same]

private theorem exposed_case_returns (caller : Subst) (state : State)
    (declaration : ReflectivePresentationDecl) (pattern : Pattern)
    (freshHead : Subst.lookup caller "head" = none) (freshName : Subst.lookup caller "name" = none)
    (freshOther : Subst.lookup caller "other" = none)
    (dropCaptured : applySubst caller (v "drop") = textValue declaration.dropConstructor)
    (leavesCaptured : applySubst caller (v "leaves") =
      patternsValue (ReflectiveSubstitution.parallelLeaves declaration pattern)) :
    PureReturns runtime caller state
      (a "case" [v "leaves", .expression (exposedRows.map fun row => .expression [row.1, row.2])]) state
      (optionValue (ReflectiveSubstitution.exposedDrop? declaration pattern)) := by
  unfold ReflectiveSubstitution.exposedDrop?
  generalize ReflectiveSubstitution.parallelLeaves declaration pattern = leaves at leavesCaptured ⊢
  have leavesReturned : PureReturns runtime caller state (v "leaves") state (patternsValue leaves) := by
    simpa only [leavesCaptured] using variable_returns runtime caller state "leaves"
  split
  next constructor name =>
    let selected := ("name", patternValue name) :: ("head", textValue constructor) :: caller
    apply branch_returns caller selected state (v "leaves") _ exposedRows
      (a "if" [a "==" [v "head", v "drop"], a "Some" [v "name"], .symbol "None"]) _ leavesReturned
    · simp [exposedRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, lookup_cons,
        selected, freshHead, freshName]
    · apply bool_if_returns selected state _ (constructor == declaration.dropConstructor) _ _ _
      · apply strings_equal_returns selected state constructor declaration.dropConstructor "head" "drop"
        · simp [selected, applySubst, lookup_cons]
        · simpa [selected, applySubst, lookup_cons] using dropCaptured
      · by_cases dropped : constructor = declaration.dropConstructor
        · have equal : (constructor == declaration.dropConstructor) = true := by simp [dropped]
          simp only [equal, ite_true, if_pos dropped]
          simpa [optionValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
            applySubst.applySubstList, lookup_cons, selected] using
            PureData.template_return runtime selected state (a "Some" [v "name"])
              (data_constructor "Some" ["name"] (by decide))
        · have unequal : (constructor == declaration.dropConstructor) = false := by simp [dropped]
          simp only [unequal, Bool.false_eq_true, ite_false, if_neg dropped]
          exact symbol_returns runtime selected state "None"
  next notExposed =>
    have matched : SpaceSemantics.selectCase caller (patternsValue leaves) exposedRows =
        some (("other", patternsValue leaves) :: caller, .symbol "None") := by
      rcases leaves with _ | ⟨first, _ | ⟨second, rest⟩⟩
      · simp [exposedRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, freshOther]
      · cases first with
        | apply constructor children =>
            rcases children with _ | ⟨name, _ | ⟨other, more⟩⟩
            · simp [exposedRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                freshOther]
            · exact False.elim (notExposed constructor name rfl)
            · simp [exposedRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                freshOther]
        | bvar _ | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
            simp [exposedRows, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, freshOther]
      · simp [exposedRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom,
          freshOther]
    exact branch_returns caller _ state (v "leaves") _ exposedRows _ _ leavesReturned matched
      (symbol_returns runtime _ state "None")

private theorem exposed_drop_returns (state : State) (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    PureReturns runtime [] state
      (a Helper.exposedDrop.head [textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (optionValue (ReflectiveSubstitution.exposedDrop? declaration pattern)) := by
  let values := [textValue declaration.dropConstructor, kindValue declaration,
    textValue declaration.parallelUnitConstructor, patternValue pattern]
  let caller := environment .exposedDrop values
  let leaves := ReflectiveSubstitution.parallelLeaves declaration pattern
  let final := ("leaves", patternsValue leaves) :: caller
  apply helper_call .exposedDrop [] state values values _ rfl (captured_closed _)
  rw [source_body]
  change PureReturns runtime caller state exposedDropBody state _
  unfold exposedDropBody
  apply named_let_returns caller state "leaves" _ (patternsValue leaves) _ _
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · apply helper_capture .leaves caller state _ _ _ rfl _ (leaves_returns state declaration pattern)
    simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · apply exposed_case_returns final state declaration pattern
    · simp [final, caller, values, environment, Helper.names, Subst.lookup]
    · simp [final, caller, values, environment, Helper.names, Subst.lookup]
    · simp [final, caller, values, environment, Helper.names, Subst.lookup]
    · simp [final, caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [final, leaves, applySubst, Subst.lookup]

private theorem nonsingleton_selection (caller : Subst) (children : List Pattern)
    (first fallback : String) (yes no : Atom)
    (freshFallback : Subst.lookup caller fallback = none)
    (nonsingleton : ¬∃ payload, children = [payload]) :
    SpaceSemantics.selectCase caller (patternsValue children)
      [(a "LCons" [v first, .symbol "LNil"], yes), (v fallback, no)] =
      some ((fallback, patternsValue children) :: caller, no) := by
  rcases children with _ | ⟨payload, _ | ⟨second, rest⟩⟩
  · simp [InferenceCettaWire.encodePatterns, CettaWireAtom.encode, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, matchAtom, freshFallback]
  · exact False.elim (nonsingleton ⟨payload, rfl⟩)
  · simp [InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, freshFallback]

private theorem finish_resolve_nonsingleton (declaration : ReflectivePresentationDecl)
    (constructor : String) (children : List Pattern) (nonsingleton : ¬∃ payload, children = [payload]) :
    ReflectiveSubstitution.finishResolveApply declaration constructor children = .apply constructor children := by
  rcases children with _ | ⟨payload, _ | ⟨second, rest⟩⟩
  · rfl
  · exact False.elim (nonsingleton ⟨payload, rfl⟩)
  · rfl

private theorem resolve_finish_returns (state : State) (declaration : ReflectivePresentationDecl)
    (constructor : String) (children : List Pattern) :
    PureReturns runtime [] state
      (a Helper.resolveFinish.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, textValue constructor, patternsValue children]) state
      (patternValue (ReflectiveSubstitution.finishResolveApply declaration constructor children)) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    kindValue declaration, textValue declaration.parallelUnitConstructor, textValue constructor,
    patternsValue children]
  let caller := environment .resolveFinish values
  by_cases singleton : ∃ payload, children = [payload]
  · obtain ⟨payload, rfl⟩ := singleton
    let selected := ("payload", patternValue payload) :: caller
    apply helper_case .resolveFinish state values "children" (patternsValue [payload])
      resolveFinishRows selected resolveFinishRow0 _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [resolveFinishRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
        environment, Helper.names, Subst.lookup]
    · unfold resolveFinishRow0
      apply bool_if_returns selected state _ (constructor == declaration.quoteConstructor) _ _ _
      · apply strings_equal_returns selected state constructor declaration.quoteConstructor "head" "quote"
        · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · by_cases quoted : constructor = declaration.quoteConstructor
        · have equal : (constructor == declaration.quoteConstructor) = true := by simp [quoted]
          simp only [equal, ite_true, ReflectiveSubstitution.finishResolveApply, if_pos quoted]
          have exposedReturned := exposed_drop_returns state declaration payload
          cases found : ReflectiveSubstitution.exposedDrop? declaration payload with
          | none =>
              rw [found] at exposedReturned
              let bound := ("exposed", Atom.symbol "None") :: selected
              let other := ("none", Atom.symbol "None") :: bound
              apply named_let_returns selected state "exposed" _ (.symbol "None") _ _
              · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
              · apply helper_capture .exposedDrop selected state _ _ _ rfl _ exposedReturned
                simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
              · apply branch_returns bound other state (v "exposed") (.symbol "None") exposedNameRows
                  (a "PApp" [v "head", v "children"]) _
                · simpa [bound, applySubst, Subst.lookup] using variable_returns runtime bound state "exposed"
                · simp [exposedNameRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    matchAtom, other, bound, selected, caller,
                    values, environment, Helper.names, Subst.lookup]
                · apply finish_application_returns other state constructor [payload]
                  · simp [other, bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
                  · simp [other, bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          | some name =>
              rw [found] at exposedReturned
              let bound := ("exposed", optionValue (some name)) :: selected
              let named := ("name", patternValue name) :: bound
              apply named_let_returns selected state "exposed" _ (optionValue (some name)) _ _
              · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
              · apply helper_capture .exposedDrop selected state _ _ _ rfl _ exposedReturned
                simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
              · apply branch_returns bound named state (v "exposed") (optionValue (some name)) exposedNameRows
                  (v "name") _
                · simpa [bound, applySubst, Subst.lookup] using variable_returns runtime bound state "exposed"
                · simp [exposedNameRows, optionValue, CettaWireAtom.encode,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, named, bound, selected, caller,
                    values, environment, Helper.names, Subst.lookup]
                · simpa [named, applySubst, Subst.lookup] using variable_returns runtime named state "name"
        · have unequal : (constructor == declaration.quoteConstructor) = false := by simp [quoted]
          simp only [unequal, Bool.false_eq_true, ite_false, ReflectiveSubstitution.finishResolveApply,
            if_neg quoted]
          apply finish_application_returns selected state constructor [payload]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · rw [finish_resolve_nonsingleton declaration constructor children singleton]
    let selected := ("other", patternsValue children) :: caller
    apply helper_case .resolveFinish state values "children" (patternsValue children)
      resolveFinishRows selected (a "PApp" [v "head", v "children"]) _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · apply nonsingleton_selection caller children "payload" "other" _ _ _ singleton
      simp [caller, values, environment, Helper.names, Subst.lookup]
    · apply finish_application_returns selected state constructor children
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]

private theorem resolve_list_returns_from_elements (state : State)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a Helper.resolve.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.resolveQuotes declaration pattern))) :
    PureReturns runtime [] state
      (a Helper.resolveList.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue patterns]) state
      (patternsValue (patterns.map (ReflectiveSubstitution.resolveQuotes declaration))) := by
  induction patterns with
  | nil =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue []]
      apply helper_case .resolveList state values "patterns" (.symbol "LNil") resolveListRows
        (environment .resolveList values) resolveListRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [resolveListRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [resolveListRow0, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime _ state "LNil"
  | cons pattern patterns ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue (pattern :: patterns)]
      let caller := environment .resolveList values
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headValue := patternValue (ReflectiveSubstitution.resolveQuotes declaration pattern)
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue (patterns.map (ReflectiveSubstitution.resolveQuotes declaration))
      let final := ("tail", tailValue) :: headBound
      have headReturned := helper_capture .resolve selected state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]
        headValue rfl (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have tailReturned := helper_capture .resolveList headBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternsValue patterns]
        tailValue rfl (by simp [headBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply helper_case .resolveList state values "patterns" (patternsValue (pattern :: patterns))
        resolveListRows selected resolveListRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveListRows, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, environment, Helper.names, Subst.lookup]
      · unfold resolveListRow1
        apply PureData.let_bindings_return (pairs :=
          [(v "head", a Helper.resolve.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "pattern"]),
           (v "tail", a Helper.resolveList.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "rest"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              headBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) tailReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, headBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [List.map_cons, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            final, headBound, headValue, tailValue] using
            PureData.template_return runtime final state (a "LCons" [v "head", v "tail"])
              (data_constructor "LCons" ["head", "tail"] (by decide))

theorem resolve_returns (state : State) (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    PureReturns runtime [] state
      (a Helper.resolve.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue pattern]) state
      (patternValue (ReflectiveSubstitution.resolveQuotes declaration pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.bvar index)]
      let caller := environment .resolve values
      let selected := ("index", number index) :: caller
      apply helper_case .resolve state values "pattern" (patternValue (.bvar index))
        resolveRows selected resolveRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [resolveRow0, ReflectiveSubstitution.resolveQuotes, selected, caller, values,
          environment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime selected state "pattern"
  | hfvar name =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.fvar name)]
      let caller := environment .resolve values
      let selected := ("name", textValue name) :: caller
      apply helper_case .resolve state values "pattern" (patternValue (.fvar name))
        resolveRows selected resolveRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [resolveRow1, ReflectiveSubstitution.resolveQuotes, selected, caller, values,
          environment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime selected state "pattern"
  | happly head children ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.apply head children)]
      let caller := environment .resolve values
      let selected := ("children", patternsValue children) :: ("head", textValue head) :: caller
      let childrenResult := children.map (ReflectiveSubstitution.resolveQuotes declaration)
      let final := ("values", patternsValue childrenResult) :: selected
      simp only [ReflectiveSubstitution.resolveQuotes, ReflectiveSubstitution.resolveQuotesList_eq_map]
      apply helper_case .resolve state values "pattern" (patternValue (.apply head children))
        resolveRows selected resolveRow2 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold resolveRow2
        apply named_let_returns selected state "values" _ (patternsValue childrenResult) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .resolveList selected state _ _ _ rfl _
            (resolve_list_returns_from_elements state declaration children ih)
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · apply helper_capture .resolveFinish final state _ _ _ rfl _
            (resolve_finish_returns state declaration head childrenResult)
          simp [final, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  | hlambda binder body ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.lambda binder body)]
      let caller := environment .resolve values
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let result := ReflectiveSubstitution.resolveQuotes declaration body
      let final := ("value", patternValue result) :: selected
      simp only [ReflectiveSubstitution.resolveQuotes]
      apply helper_case .resolve state values "pattern" (patternValue (.lambda binder body))
        resolveRows selected resolveRow3 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold resolveRow3
        apply named_let_returns selected state "value" _ (patternValue result) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .resolve selected state _ _ _ rfl _ ih
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, result] using
            PureData.template_return runtime final state (a "PLam" [v "binder", v "value"])
              (data_constructor "PLam" ["binder", "value"] (by decide))
  | hmultiLambda arity binders body ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.multiLambda arity binders body)]
      let caller := environment .resolve values
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let result := ReflectiveSubstitution.resolveQuotes declaration body
      let final := ("value", patternValue result) :: selected
      simp only [ReflectiveSubstitution.resolveQuotes]
      apply helper_case .resolve state values "pattern" (patternValue (.multiLambda arity binders body))
        resolveRows selected resolveRow4 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold resolveRow4
        apply named_let_returns selected state "value" _ (patternValue result) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .resolve selected state _ _ _ rfl _ ih
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, result] using
            PureData.template_return runtime final state (a "PMultiLam" [v "arity", v "binders", v "value"])
              (data_constructor "PMultiLam" ["arity", "binders", "value"] (by decide))
  | hsubst body replacement ihBody ihReplacement =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.subst body replacement)]
      let caller := environment .resolve values
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      let bodyResult := ReflectiveSubstitution.resolveQuotes declaration body
      let replacementResult := ReflectiveSubstitution.resolveQuotes declaration replacement
      let bodyBound := ("value", patternValue bodyResult) :: selected
      let final := ("replacement-value", patternValue replacementResult) :: bodyBound
      have bodyReturned := helper_capture .resolve selected state [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue body]
        (patternValue bodyResult) rfl
        (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) ihBody
      have replacementReturned := helper_capture .resolve bodyBound state [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "replacement"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue replacement]
        (patternValue replacementResult) rfl
        (by simp [bodyBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) ihReplacement
      simp only [ReflectiveSubstitution.resolveQuotes]
      apply helper_case .resolve state values "pattern" (patternValue (.subst body replacement))
        resolveRows selected resolveRow5 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold resolveRow5
        apply PureData.let_bindings_return (pairs :=
          [(v "value", a Helper.resolve.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]),
           (v "replacement-value", a Helper.resolve.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "replacement"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := bodyBound) bodyReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              bodyBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) replacementReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, bodyBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, bodyBound, bodyResult, replacementResult] using
            PureData.template_return runtime final state (a "PSubst" [v "value", v "replacement-value"])
              (data_constructor "PSubst" ["value", "replacement-value"] (by decide))
  | hcollection kind elements rest ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, patternValue (.collection kind elements rest)]
      let caller := environment .resolve values
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      let results := elements.map (ReflectiveSubstitution.resolveQuotes declaration)
      let final := ("values", patternsValue results) :: selected
      simp only [ReflectiveSubstitution.resolveQuotes, ReflectiveSubstitution.resolveQuotesList_eq_map]
      apply helper_case .resolve state values "pattern" (patternValue (.collection kind elements rest))
        resolveRows selected resolveRow6 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [resolveRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold resolveRow6
        apply named_let_returns selected state "values" _ (patternsValue results) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .resolveList selected state _ _ _ rfl _
            (resolve_list_returns_from_elements state declaration elements ih)
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, results] using
            PureData.template_return runtime final state (a "PCollection" [v "kind", v "values", v "rest"])
              (data_constructor "PCollection" ["kind", "values", "rest"] (by decide))

private theorem substitute_unary_returns (state : State) (declaration : ReflectivePresentationDecl) (mode : Option Pattern)
    (depth : Nat) (replacement : Pattern) (head : String) (payload : Pattern)
    (payloadReturned : PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth,
        patternValue replacement, patternValue payload]) state
      (patternValue (substituteMode declaration mode replacement depth payload)))
    (entered : ∀ value, mode = some value → PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth,
        patternValue value, patternValue payload]) state
      (patternValue (substituteMode declaration mode value depth payload))) :
    PureReturns runtime [] state
      (a Helper.substituteUnary.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
        kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth,
        patternValue replacement, textValue head, patternValue payload]) state
      (patternValue (substituteMode declaration mode replacement depth
        (.apply head [payload]))) := by
  let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
    kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth,
    patternValue replacement, textValue head, patternValue payload]
  let caller := environment .substituteUnary values
  let result := substituteMode declaration mode replacement depth payload
  have through : ∀ selected : Subst,
      [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "payload"].map
          (applySubst selected) =
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor,
          kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth,
          patternValue replacement, patternValue payload] →
      applySubst (("value", patternValue result) :: selected) (v "head") = textValue head →
      Subst.lookup selected "value" = none →
      PureReturns runtime selected state substituteThrough state (patternValue (.apply head [result])) := by
    intro selected captured headCaptured fresh
    unfold substituteThrough
    apply named_let_returns selected state "value" _ (patternValue result) _ _ fresh
    · exact helper_capture .substitute selected state _ _ _ rfl captured payloadReturned
    · apply unary_constructor_returns (("value", patternValue result) :: selected) state "head" "value" head result
        headCaptured
      simp [applySubst, Subst.lookup]
  apply helper_call .substituteUnary [] state values values _ rfl (captured_closed _)
  rw [source_body]
  change PureReturns runtime caller state substituteUnaryBody state _
  unfold substituteUnaryBody
  apply bool_if_returns caller state _ (head == declaration.quoteConstructor) _ _ _
  · apply strings_equal_returns caller state head declaration.quoteConstructor "head" "quote"
    · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · by_cases quoted : head = declaration.quoteConstructor
    · have equal : (head == declaration.quoteConstructor) = true := by simp [quoted]
      simp only [equal, ite_true]
      have insideBound : PureReturns runtime caller state (v "inside") state (modeValue mode) := by
        simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime caller state "inside"
      unfold substituteQuote
      subst quoted
      cases mode with
      | none =>
          rw [mode_quote_none]
          apply branch_returns caller caller state (v "inside") (modeValue none) insideRows
            (a "PApp" [v "head", a "LCons" [v "payload", .symbol "LNil"]]) _ insideBound
          · simp [insideRows, modeValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · apply unary_constructor_returns caller state "head" "payload" _ payload
            · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
            · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      | some value =>
          rw [mode_quote_some]
          let inner := substituteMode declaration (some value) value depth payload
          let selected := ("value", patternValue value) :: caller
          let final := ("entered", patternValue inner) :: selected
          apply branch_returns caller selected state (v "inside") (modeValue (some value)) insideRows
            (a "let" [v "entered", a "gslt:rule:scope-reflective-substitute-at" [v "quote", v "drop",
              v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "value", v "payload"],
              a "PApp" [v "head", a "LCons" [v "entered", .symbol "LNil"]]]) _ insideBound
          · simp [insideRows, modeValue, CettaWireAtom.encode, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller,
              values, environment, Helper.names, Subst.lookup]
          · apply named_let_returns selected state "entered" _ (patternValue inner) _ _
            · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
            · exact helper_capture .substitute selected state _ _ _ rfl
                (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup,
                  modeValue])
                (entered value rfl)
            · apply unary_constructor_returns final state "head" "entered" _ inner
              · simp [final, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
              · simp [final, applySubst, Subst.lookup]
    · have unequal : (head == declaration.quoteConstructor) = false := by simp [quoted]
      simp only [unequal, Bool.false_eq_true, ite_false]
      apply bool_if_returns caller state _ (head == declaration.dropConstructor) _ _ _
      · apply strings_equal_returns caller state head declaration.dropConstructor "head" "drop"
        · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · by_cases dropped : head = declaration.dropConstructor
        · have equalDrop : (head == declaration.dropConstructor) = true := by simp [dropped]
          simp only [equalDrop, ite_true]
          rw [mode_unary_of_ne declaration mode replacement depth payload quoted, if_pos dropped]
          let binder := ReflectiveSubstitution.BinderHead.ofPattern declaration payload
          let final := ("binder", headValue binder) :: caller
          unfold substituteDrop
          apply named_let_returns caller state "binder" _ (headValue binder) _ _
          · simp [caller, values, environment, Helper.names, Subst.lookup]
          · apply helper_capture .binderHead caller state _ _ _ rfl _ (binder_head_returns state declaration payload)
            simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
          · have binderBound : applySubst final (v "binder") = headValue binder := by
              simp [final, applySubst, Subst.lookup]
            by_cases indexed : ∃ level, binder = .index level
            · obtain ⟨level, binderIs⟩ := indexed
              let selected := ("level", number level) :: final
              apply branch_returns final selected state _ (headValue (.index level)) binderRows
                (a "if" [a "==" [v "level", v "depth"], receiveHit, substituteThrough]) _
              · simpa [binderBound, binderIs] using variable_returns runtime final state "binder"
              · simp [binderRows, CettaWireAtom.encode, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, selected,
                  final, caller, values, environment, Helper.names, Subst.lookup]
              · apply bool_if_returns selected state _ (level == depth) _ _ _
                · have same : decide (level = depth) = (level == depth) := by
                    by_cases equal : level = depth <;> simp [equal]
                  simpa only [Term.natural.injEq, same] using
                    CettaWireAtom.equality_captured_returns runtime selected state (.natural level) (.natural depth)
                      "level" "depth" (by simp [selected, applySubst, Subst.lookup])
                      (by simp [selected, final, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                · by_cases hit : level = depth
                  · subst hit
                    have matched : ReflectiveSubstitution.matchesBinder declaration level payload = true := by
                      simp only [ReflectiveSubstitution.matchesBinder, decide_eq_true_eq]
                      exact binderIs
                    simp only [beq_self_eq_true, ↓reduceIte, matched]
                    let received := Substitution.instantiateBVarAt level replacement (.bvar level)
                    let bound := ("value", patternValue received) :: selected
                    have instantiated := retained_returns (by decide +kernel)
                      (RuleInstantiationExecution.instantiate_bvar_at_captured_returns selected state level replacement
                        (.bvar level) (v "depth") (v "replacement") (a "Var" [v "depth"]) (by
                          show _ = [CettaWireAtom.encode (.natural level),
                            CettaWireAtom.encode (InferenceCettaWire.encodePattern replacement),
                            CettaWireAtom.encode (InferenceCettaWire.encodePattern (.bvar level))]
                          simp [selected, final, caller, values, environment, Helper.names, applySubst,
                            applySubst.applySubstList, Subst.lookup, InferenceCettaWire.encodePattern,
                            CettaWireAtom.encode, CettaWireAtom.encodeMany]))
                    unfold receiveHit
                    apply named_let_returns selected state "value" _ (patternValue received) _ _
                    · simp [selected, final, caller, values, environment, Helper.names, Subst.lookup]
                    · exact instantiated
                    · apply helper_capture .receive bound state _ _ _ rfl _
                        (receive_returns state declaration head received)
                      simp [bound, selected, final, caller, values, environment, Helper.names, applySubst,
                        Subst.lookup]
                  · have missed : ReflectiveSubstitution.matchesBinder declaration depth payload = false := by
                      simp only [ReflectiveSubstitution.matchesBinder, decide_eq_false_iff_not]
                      intro same
                      exact hit (ReflectiveSubstitution.BinderHead.index.inj (binderIs.symm.trans same))
                    have unequalLevel : (level == depth) = false := by simp [hit]
                    simp only [unequalLevel, Bool.false_eq_true, ↓reduceIte, missed]
                    exact through selected
                      (by simp [selected, final, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                      (by simp [selected, final, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                      (by simp [selected, final, caller, values, environment, Helper.names, Subst.lookup])
            · let selected := ("other", headValue binder) :: final
              have missed : ReflectiveSubstitution.matchesBinder declaration depth payload = false := by
                simp only [ReflectiveSubstitution.matchesBinder, decide_eq_false_iff_not]
                intro same
                exact indexed ⟨depth, same⟩
              simp only [missed, Bool.false_eq_true, ↓reduceIte]
              apply branch_returns final selected state _ (headValue binder) binderRows substituteThrough _
              · simpa [binderBound] using variable_returns runtime final state "binder"
              · generalize binderIs : binder = observed at indexed
                cases observed with
                | index level => exact False.elim (indexed ⟨level, rfl⟩)
                | _ => simp_all [binderRows, CettaWireAtom.encode,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                    matchAtom, selected, final, caller, values, environment, Helper.names, Subst.lookup]
              · exact through selected
                  (by simp [selected, final, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                  (by simp [selected, final, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                  (by simp [selected, final, caller, values, environment, Helper.names, Subst.lookup])
        · have unequalDrop : (head == declaration.dropConstructor) = false := by simp [dropped]
          simp only [unequalDrop, Bool.false_eq_true, ite_false]
          rw [mode_unary_of_ne declaration mode replacement depth payload quoted, if_neg dropped]
          exact through caller
            (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, values, environment, Helper.names, Subst.lookup])

private theorem substitute_list_returns_from_elements (state : State)
    (declaration : ReflectivePresentationDecl) (mode : Option Pattern) (depth : Nat) (replacement : Pattern) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue pattern]) state
      (patternValue (substituteMode declaration mode replacement depth pattern))) :
    PureReturns runtime [] state
      (a Helper.substituteList.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternsValue patterns]) state
      (patternsValue (patterns.map (substituteMode declaration mode replacement depth))) := by
  induction patterns with
  | nil =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternsValue []]
      apply helper_case .substituteList state values "patterns" (.symbol "LNil") substituteListRows
        (environment .substituteList values) substituteListRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      · simp [substituteListRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [substituteListRow0, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns runtime _ state "LNil"
  | cons pattern patterns ih =>
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternsValue (pattern :: patterns)]
      let caller := environment .substituteList values
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headValue := patternValue (substituteMode declaration mode replacement depth pattern)
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue (patterns.map (substituteMode declaration mode replacement depth))
      let final := ("tail", tailValue) :: headBound
      have headReturned := helper_capture .substitute selected state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "pattern"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue pattern]
        headValue rfl (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have tailReturned := helper_capture .substituteList headBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "rest"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternsValue patterns]
        tailValue rfl (by simp [headBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply helper_case .substituteList state values "patterns" (patternsValue (pattern :: patterns))
        substituteListRows selected substituteListRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteListRows, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, environment, Helper.names, Subst.lookup]
      · unfold substituteListRow1
        apply PureData.let_bindings_return (pairs :=
          [(v "head", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "pattern"]),
           (v "tail", a Helper.substituteList.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "rest"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              headBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) tailReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, headBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [List.map_cons, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            final, headBound, headValue, tailValue] using
            PureData.template_return runtime final state (a "LCons" [v "head", v "tail"])
              (data_constructor "LCons" ["head", "tail"] (by decide))

private theorem substitute_apply_returns (state : State) (declaration : ReflectivePresentationDecl) (mode : Option Pattern)
    (depth : Nat) (replacement : Pattern) (head : String) (children : List Pattern)
    (elements : ∀ pattern ∈ children, PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue pattern]) state
      (patternValue (substituteMode declaration mode replacement depth pattern)))
    (entered : ∀ value, mode = some value → ∀ pattern ∈ children, PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue value, patternValue pattern]) state
      (patternValue (substituteMode declaration mode value depth pattern))) :
    PureReturns runtime [] state
      (a Helper.substituteApply.head [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, textValue head, patternsValue children]) state
      (patternValue (substituteMode declaration mode replacement depth (.apply head children))) := by
  by_cases singleton : ∃ payload, children = [payload]
  · obtain ⟨payload, rfl⟩ := singleton
    let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
      textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, textValue head, patternsValue [payload]]
    let caller := environment .substituteApply values
    let selected := ("payload", patternValue payload) :: caller
    apply helper_case .substituteApply state values "children" (patternsValue [payload])
      substituteApplyRows selected substituteApplyRow0 _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [substituteApplyRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
        environment, Helper.names, Subst.lookup]
    · unfold substituteApplyRow0
      apply helper_capture .substituteUnary selected state _ _ _ rfl _
        (substitute_unary_returns state declaration mode depth replacement head payload (elements payload (by simp))
          fun value same => entered value same payload (by simp))
      simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
      textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, textValue head, patternsValue children]
    let caller := environment .substituteApply values
    let selected := ("many", patternsValue children) :: caller
    let results := children.map (substituteMode declaration mode replacement depth)
    let final := ("values", patternsValue results) :: selected
    have ordinary : substituteMode declaration mode replacement depth (.apply head children) =
        .apply head results := by
      exact mode_apply_of_ne_one declaration mode replacement depth head singleton
    rw [ordinary]
    apply helper_case .substituteApply state values "children" (patternsValue children)
      substituteApplyRows selected substituteApplyRow1 _ rfl rfl
    · simp [values, environment, Helper.names, applySubst, Subst.lookup]
    · cases children with
      | nil => simp [substituteApplyRows, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
          selected, caller, values, environment, Helper.names, Subst.lookup]
      | cons payload rest =>
          cases rest with
          | nil => exact False.elim (singleton ⟨payload, rfl⟩)
          | cons child rest => simp [substituteApplyRows, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              selected, caller, values, environment, Helper.names, Subst.lookup]
    · unfold substituteApplyRow1
      apply named_let_returns selected state "values" _ (patternsValue results) _ _
      · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
      · apply helper_capture .substituteList selected state _ _ _ rfl _
          (substitute_list_returns_from_elements state declaration mode depth replacement children elements)
        simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
      · apply finish_application_returns final state head results "head" "values"
        · simp [final, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simp [final, applySubst, Subst.lookup]

private theorem add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String) (capturedFirst : applySubst caller (v first) = number left)
    (capturedSecond : applySubst caller (v second) = number right) :
    PureReturns runtime caller state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns runtime caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedFirst, capturedSecond]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns runtime caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns runtime caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state name
  · exact grounded_returns runtime caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

theorem substitute_returns (state : State) (declaration : ReflectivePresentationDecl) (mode : Option Pattern)
    (pattern : Pattern) : ∀ (depth : Nat) (replacement : Pattern),
    PureReturns runtime [] state
      (a Helper.substitute.head [textValue declaration.quoteConstructor,
        textValue declaration.dropConstructor, kindValue declaration, textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue pattern]) state
      (patternValue (substituteMode declaration mode replacement depth pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.bvar index)]
      let caller := environment .substitute values
      let selected := ("index", number index) :: caller
      apply helper_case .substitute state values "pattern" (patternValue (.bvar index))
        substituteRows selected substituteRow0 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow0
        simpa only [mode_bvar, eliminate] using
          retained_returns (by decide +kernel)
            (RuleInstantiationExecution.instantiate_bvar_at_captured_returns selected state depth replacement (.bvar index)
              (v "depth") (v "replacement") (v "pattern") (by
                simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]))
  | hfvar name =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.fvar name)]
      let caller := environment .substitute values
      let selected := ("name", textValue name) :: caller
      apply helper_case .substitute state values "pattern" (patternValue (.fvar name))
        substituteRows selected substituteRow1 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · simpa [substituteRow1, mode_fvar, selected, caller, values,
          environment, Helper.names, applySubst, Subst.lookup] using variable_returns runtime selected state "pattern"
  | happly head children ih =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.apply head children)]
      let caller := environment .substitute values
      let selected := ("children", patternsValue children) :: ("head", textValue head) :: caller
      apply helper_case .substitute state values "pattern" (patternValue (.apply head children))
        substituteRows selected substituteRow2 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow2
        apply helper_capture .substituteApply selected state _ _ _ rfl _
          (substitute_apply_returns state declaration mode depth replacement head children
            (fun child member => ih child member depth replacement)
            (fun value _ child member => ih child member depth value))
        simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
  | hlambda binder body ih =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.lambda binder body)]
      let caller := environment .substitute values
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let nextBound := ("next", number (depth + 1)) :: selected
      let result := substituteMode declaration mode replacement (depth + 1) body
      let final := ("value", patternValue result) :: nextBound
      have nextReturned := add_one_returns selected state depth "depth" (by
        simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
      have bodyReturned := helper_capture .substitute nextBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
          textValue declaration.parallelUnitConstructor, modeValue mode, number (depth + 1), patternValue replacement, patternValue body]
        (patternValue result) rfl (by
          simp [nextBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) (ih (depth + 1) replacement)
      simp only [mode_lambda]
      apply helper_case .substitute state values "pattern" (patternValue (.lambda binder body))
        substituteRows selected substituteRow3 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow3
        apply PureData.let_bindings_return (pairs :=
          [(v "next", a "+" [v "depth", number 1]),
           (v "value", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) bodyReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, nextBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, nextBound, selected, result] using
            PureData.template_return runtime final state (a "PLam" [v "binder", v "value"])
              (data_constructor "PLam" ["binder", "value"] (by decide))
  | hmultiLambda arity binders body ih =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.multiLambda arity binders body)]
      let caller := environment .substitute values
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let nextBound := ("next", number (depth + arity)) :: selected
      let result := substituteMode declaration mode replacement (depth + arity) body
      let final := ("value", patternValue result) :: nextBound
      have nextReturned := add_variables_returns selected state depth arity "depth" "arity"
        (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        (by simp [selected, applySubst, Subst.lookup])
      have bodyReturned := helper_capture .substitute nextBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
          textValue declaration.parallelUnitConstructor, modeValue mode, number (depth + arity), patternValue replacement, patternValue body]
        (patternValue result) rfl (by
          simp [nextBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) (ih (depth + arity) replacement)
      simp only [mode_multiLambda]
      apply helper_case .substitute state values "pattern" (patternValue (.multiLambda arity binders body))
        substituteRows selected substituteRow4 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow4
        apply PureData.let_bindings_return (pairs :=
          [(v "next", a "+" [v "depth", v "arity"]),
           (v "value", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) bodyReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, nextBound, selected, caller, values, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, nextBound, selected, result] using
            PureData.template_return runtime final state (a "PMultiLam" [v "arity", v "binders", v "value"])
              (data_constructor "PMultiLam" ["arity", "binders", "value"] (by decide))
  | hsubst body nested ihBody ihReplacement =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.subst body nested)]
      let caller := environment .substitute values
      let selected := ("nested-replacement", patternValue nested) :: ("body", patternValue body) :: caller
      let nextBound := ("next", number (depth + 1)) :: selected
      let bodyResult := substituteMode declaration mode replacement (depth + 1) body
      let replacementResult := substituteMode declaration mode replacement depth nested
      let bodyBound := ("value", patternValue bodyResult) :: nextBound
      let final := ("replacement-value", patternValue replacementResult) :: bodyBound
      have nextReturned := add_one_returns selected state depth "depth" (by
        simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
      have bodyReturned := helper_capture .substitute nextBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
          textValue declaration.parallelUnitConstructor, modeValue mode, number (depth + 1), patternValue replacement, patternValue body]
        (patternValue bodyResult) rfl (by
          simp [nextBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) (ihBody (depth + 1) replacement)
      have replacementReturned := helper_capture .substitute bodyBound state
        [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "nested-replacement"]
        [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
          textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue nested]
        (patternValue replacementResult) rfl (by
          simp [bodyBound, nextBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) (ihReplacement depth replacement)
      simp only [mode_subst]
      apply helper_case .substitute state values "pattern" (patternValue (.subst body nested))
        substituteRows selected substituteRow5 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow5
        apply PureData.let_bindings_return (pairs :=
          [(v "next", a "+" [v "depth", number 1]),
           (v "value", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "next", v "replacement", v "body"]),
           (v "replacement-value", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", v "depth", v "replacement", v "nested-replacement"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := bodyBound) bodyReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                bodyBound, nextBound, selected, caller, values, environment, Helper.names]
            · apply PureData.BindingsReturn.cons (bound := final) replacementReturned
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                  final, bodyBound, nextBound, selected, caller, values, environment, Helper.names]
              · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, bodyBound, bodyResult, replacementResult] using
            PureData.template_return runtime final state (a "PSubst" [v "value", v "replacement-value"])
              (data_constructor "PSubst" ["value", "replacement-value"] (by decide))
  | hcollection kind elements rest ih =>
      intro depth replacement
      let values := [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
        textValue declaration.parallelUnitConstructor, modeValue mode, number depth, patternValue replacement, patternValue (.collection kind elements rest)]
      let caller := environment .substitute values
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      let results := elements.map (substituteMode declaration mode replacement depth)
      let final := ("values", patternsValue results) :: selected
      simp only [mode_collection]
      apply helper_case .substitute state values "pattern" (patternValue (.collection kind elements rest))
        substituteRows selected substituteRow6 _ rfl rfl
      · simp [values, environment, Helper.names, applySubst, Subst.lookup]
      · simp [substituteRows, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold substituteRow6
        apply named_let_returns selected state "values" _ (patternsValue results) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · apply helper_capture .substituteList selected state _ _ _ rfl _
            (substitute_list_returns_from_elements state declaration mode depth replacement elements
              (fun child member => ih child member depth replacement))
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup, final, selected, results] using
            PureData.template_return runtime final state (a "PCollection" [v "kind", v "values", v "rest"])
              (data_constructor "PCollection" ["kind", "values", "rest"] (by decide))

def operationCall (declaration : ReflectivePresentationDecl) (replacement body : Pattern) : Atom :=
  a "gslt:rule:scope-reflective-binder-operation" [declarationValue declaration,
    patternValue replacement, patternValue body]
def operationAnswer (declaration : ReflectivePresentationDecl) (replacement body : Pattern) : Atom :=
  encoded (.application "Some" [InferenceCettaWire.encodePattern
    (ScopedRuleInstantiation.reflectiveOperation declaration replacement body)])

/-- The runtime spelling of a quote scope. -/
private abbrev scopeValue (scope : QuoteScope) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.quoteScopeTerm scope)

/-- The substitution mode a quote scope selects for a normalized replacement. -/
private def scopeMode (scope : QuoteScope) (normalized : Pattern) : Option Pattern :=
  match scope with
  | .closed => none
  | .reaching .apply => some normalized
  | .reaching (.freeze frozen) => some frozen.spelling
  | .reaching (.closure context) => some (.apply context [normalized])

private theorem eliminate_of_ne (first second : Pattern) {level index : Nat} (other : index ≠ level) :
    eliminate first level index = eliminate second level index := by
  unfold eliminate
  simp only [Substitution.instantiateBVarAt, other, if_false]

/-- The mode a scope selects is the declared substitution. -/
private theorem substituteMode_scopeMode (declaration : ReflectivePresentationDecl) (scope : QuoteScope)
    (normalized body : Pattern) (depth : Nat) :
    substituteMode declaration (scopeMode scope normalized) normalized depth
        (ReflectiveSubstitution.resolveQuotes declaration body) =
      ReflectiveSubstitution.substituteScoped declaration scope (eliminate normalized) depth body := by
  rcases scope with _ | (_ | frozen | context)
  · rfl
  · rfl
  · show ReflectiveSubstitution.substituteViewed declaration (eliminate frozen.spelling) (eliminate normalized)
        depth _ = ReflectiveSubstitution.substituteViewed declaration
          ((QuoteView.freeze frozen).inside (eliminate normalized)) (eliminate normalized) depth _
    congr 1
    funext level index
    by_cases same : index = level
    · subst same
      simp [QuoteView.inside, eliminate, Substitution.instantiateBVarAt,
        Substitution.liftBVars_eq_self_of_isWellScopedAt frozen.ground.2]
    · simp only [QuoteView.inside, same, if_false]
      exact eliminate_of_ne _ _ same
  · show ReflectiveSubstitution.substituteViewed declaration (eliminate (.apply context [normalized]))
        (eliminate normalized) depth _ = ReflectiveSubstitution.substituteViewed declaration
          ((QuoteView.closure context).inside (eliminate normalized)) (eliminate normalized) depth _
    congr 1
    funext level index
    by_cases same : index = level
    · subst same
      simp [QuoteView.inside, eliminate, Substitution.instantiateBVarAt, Substitution.liftBVars,
        Substitution.liftBVarsList]
    · simp only [QuoteView.inside, same, if_false]
      exact eliminate_of_ne _ _ same

private theorem enter_template (name : String) :
    PureData.Template runtime (a "Enter" [v name]) :=
  data_constructor "Enter" [name] (by decide)

private theorem enter_context_template :
    PureData.Template runtime (a "Enter" [a "PApp" [v "context", a "LCons" [v "normalized", .symbol "LNil"]]]) := by
  apply PureData.Template.constructor "Enter" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact unary_template "context" "normalized"

/-- The quote scope evaluates to the substitution mode it selects. -/
private theorem scopeCase_returns (caller : Subst) (state : State) (scope : QuoteScope) (normalized : Pattern)
    (scopeLookup : Subst.lookup caller "scope" = some (scopeValue scope))
    (normalizedLookup : Subst.lookup caller "normalized" = some (patternValue normalized))
    (freshSpelling : Subst.lookup caller "spelling" = none)
    (freshContext : Subst.lookup caller "context" = none) :
    PureReturns runtime caller state scopeCase state (modeValue (scopeMode scope normalized)) := by
  have scopeBound : PureReturns runtime caller state (v "scope") state (scopeValue scope) := by
    simpa [applySubst, scopeLookup] using variable_returns runtime caller state "scope"
  unfold scopeCase
  rcases scope with _ | (_ | frozen | context)
  · apply branch_returns caller caller state (v "scope") _ scopeRows (.symbol "Opaque") _ scopeBound
    · simp [scopeRows, scopeValue, InferenceCettaWire.AuthoredRule.quoteScopeTerm, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact symbol_returns runtime caller state "Opaque"
  · apply branch_returns caller caller state (v "scope") _ scopeRows (a "Enter" [v "normalized"]) _ scopeBound
    · simp [scopeRows, scopeValue, InferenceCettaWire.AuthoredRule.quoteScopeTerm, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom]
    · simpa [modeValue, scopeMode, applySubst, applySubst.applySubstList, normalizedLookup] using
        PureData.template_return runtime caller state _ (enter_template "normalized")
  · let selected := ("spelling", patternValue frozen.spelling) :: caller
    apply branch_returns caller selected state (v "scope") _ scopeRows (a "Enter" [v "spelling"]) _ scopeBound
    · simp [scopeRows, scopeValue, InferenceCettaWire.AuthoredRule.quoteScopeTerm, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, freshSpelling]
    · simpa [modeValue, scopeMode, applySubst, applySubst.applySubstList, selected, Subst.lookup] using
        PureData.template_return runtime selected state _ (enter_template "spelling")
  · let selected := ("context", textValue context) :: caller
    apply branch_returns caller selected state (v "scope") _ scopeRows
      (a "Enter" [a "PApp" [v "context", a "LCons" [v "normalized", .symbol "LNil"]]]) _ scopeBound
    · simp [scopeRows, scopeValue, InferenceCettaWire.AuthoredRule.quoteScopeTerm, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, freshContext]
    · have contextLookup : Subst.lookup selected "context" = some (textValue context) := by
        simp [selected, Subst.lookup]
      have normalizedSelected : Subst.lookup selected "normalized" = some (patternValue normalized) := by
        have passed : Subst.lookup selected "normalized" = Subst.lookup caller "normalized" := by
          simp [selected, Subst.lookup]
        rw [passed, normalizedLookup]
      simpa [modeValue, scopeMode, applySubst, applySubst.applySubstList, contextLookup,
        normalizedSelected, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime selected state _ enter_context_template

theorem operation_returns (state : State) (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) :
    PureReturns runtime [] state (operationCall declaration replacement body) state
      (operationAnswer declaration replacement body) := by
  let values := [declarationValue declaration, patternValue replacement, patternValue body]
  let caller := environment .operation values
  let selected := ("scope", scopeValue declaration.quoteScope) ::
    ("quote-drop-equation", textValue declaration.quoteDropEquation) ::
    ("parallel-unit", textValue declaration.parallelUnitConstructor) ::
    ("parallel-kind", encoded (InferenceCettaWire.encodeCollectionType declaration.parallelCollection)) ::
    ("drop", textValue declaration.dropConstructor) :: ("quote", textValue declaration.quoteConstructor) ::
    ("name-sort", textValue declaration.nameSort) :: ("process-sort", textValue declaration.processSort) ::
    ("name", textValue declaration.name) :: caller
  let normalized := ReflectiveSubstitution.normalizeReflectiveReplacement declaration replacement
  let normalizedBound := ("normalized", patternValue normalized) :: selected
  let resolved := ReflectiveSubstitution.resolveQuotes declaration body
  let resolvedBound := ("resolved", patternValue resolved) :: normalizedBound
  let mode := scopeMode declaration.quoteScope normalized
  let insideBound := ("inside", modeValue mode) :: resolvedBound
  let result := ScopedRuleInstantiation.reflectiveOperation declaration replacement body
  let final := ("value", patternValue result) :: insideBound
  have replacementReturned := helper_capture .replacement selected state
    [v "quote", v "drop", v "replacement"]
    [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, patternValue replacement]
    (patternValue normalized) rfl (by
      simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
    (replacement_returns state declaration replacement)
  have resolvedReturned := helper_capture .resolve normalizedBound state
    [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]
    [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
      textValue declaration.parallelUnitConstructor, patternValue body]
    (patternValue resolved) rfl (by
      simp [normalizedBound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
    (resolve_returns state declaration body)
  have insideReturned : PureReturns runtime resolvedBound state scopeCase state (modeValue mode) :=
    scopeCase_returns resolvedBound state declaration.quoteScope normalized
      (by simp [resolvedBound, normalizedBound, selected, Subst.lookup])
      (by simp [resolvedBound, normalizedBound, Subst.lookup])
      (by simp [resolvedBound, normalizedBound, selected, caller, values, environment, Helper.names, Subst.lookup])
      (by simp [resolvedBound, normalizedBound, selected, caller, values, environment, Helper.names, Subst.lookup])
  have resultEq : patternValue (substituteMode declaration mode normalized 0 resolved) = patternValue result := by
    simp only [mode, resolved, substituteMode_scopeMode]
    rfl
  have bodyReturned := helper_capture .substitute insideBound state
    [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside", number 0, v "normalized", v "resolved"]
    [textValue declaration.quoteConstructor, textValue declaration.dropConstructor, kindValue declaration,
      textValue declaration.parallelUnitConstructor, modeValue mode, number 0, patternValue normalized,
      patternValue resolved]
    (patternValue result) rfl (by
      simp [insideBound, resolvedBound, normalizedBound, selected, caller, values, environment, Helper.names,
        applySubst, Subst.lookup])
    (resultEq ▸ substitute_returns state declaration mode resolved 0 normalized)
  change PureReturns runtime [] state (a Helper.operation.head values) state _
  apply helper_case .operation state values "declaration" (declarationValue declaration)
    operationRows selected operationRow0 _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · simp [operationRows, InferenceCettaWire.AuthoredRule.reflectivePresentationTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      selected, caller, values, environment, Helper.names, Subst.lookup]
  · unfold operationRow0
    apply PureData.let_bindings_return (pairs :=
      [(v "normalized", a Helper.replacement.head [v "quote", v "drop", v "replacement"]),
       (v "resolved", a Helper.resolve.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "body"]),
       (v "inside", scopeCase),
       (v "value", a Helper.substitute.head [v "quote", v "drop", v "parallel-kind", v "parallel-unit", v "inside",
         number 0, v "normalized", v "resolved"])]) (final := final)
    · apply PureData.BindingsReturn.cons (bound := normalizedBound) replacementReturned
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          normalizedBound, selected, caller, values, environment, Helper.names]
      · apply PureData.BindingsReturn.cons (bound := resolvedBound) resolvedReturned
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            resolvedBound, normalizedBound, selected, caller, values, environment, Helper.names]
        · apply PureData.BindingsReturn.cons (bound := insideBound) insideReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              insideBound, resolvedBound, normalizedBound, selected, caller, values, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final) bodyReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, insideBound, resolvedBound, normalizedBound, selected, caller, values, environment,
                Helper.names]
            · exact .nil _ _
    · simpa [operationAnswer, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        applySubst, applySubst.applySubstList, Subst.lookup, final, result] using
        PureData.template_return runtime final state (a "Some" [v "value"])
          (data_constructor "Some" ["value"] (by decide))

theorem operation_captured_returns (caller : Subst) (state : State) (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [declarationValue declaration, patternValue replacement, patternValue body]) :
    PureReturns runtime caller state (a "gslt:rule:scope-reflective-binder-operation" arguments) state
      (operationAnswer declaration replacement body) :=
  helper_capture .operation caller state arguments _ _ rfl captured
    (operation_returns state declaration replacement body)

theorem operation_has_sufficient_fuel (state : State) (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) :
    ∃ fuel, Eval.run runtime fuel { state := state, control := .evaluate [] (operationCall declaration replacement body) } =
      .complete state [operationAnswer declaration replacement body] [] [] :=
  pure_returns_has_sufficient_fuel runtime [] state state _ _ (operation_returns state declaration replacement body)

theorem operation_completed_iff (state : State) (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel { state := state, control := .evaluate [] (operationCall declaration replacement body) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [operationAnswer declaration replacement body] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (operation_returns state declaration replacement body)
    after answers input output

theorem captured_operation_completed_iff (caller : Subst) (state : State)
    (declaration : ReflectivePresentationDecl) (replacement body : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [declarationValue declaration, patternValue replacement, patternValue body])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel
      { state := state, control := .evaluate caller (a "gslt:rule:scope-reflective-binder-operation" arguments) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [operationAnswer declaration replacement body] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime caller state state _ _
    (operation_captured_returns caller state declaration replacement body arguments captured) after answers input output

theorem unknown_declaration_returns_none (state : State) (replacement body : Pattern) :
    PureReturns runtime [] state (a "gslt:rule:scope-reflective-binder-operation"
      [.symbol "UnknownReflectivePresentation", patternValue replacement, patternValue body]) state (.symbol "None") := by
  let values := [.symbol "UnknownReflectivePresentation", patternValue replacement, patternValue body]
  let caller := environment .operation values
  let selected := ("invalid", .symbol "UnknownReflectivePresentation") :: caller
  apply helper_case .operation state values "declaration" (.symbol "UnknownReflectivePresentation")
    operationRows selected operationRow1 _ rfl rfl
  · simp [values, environment, Helper.names, applySubst, Subst.lookup]
  · simp [operationRows, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
  · exact symbol_returns runtime selected state "None"

def controlDeclaration : ReflectivePresentationDecl :=
  { name := "ReflectiveControl", processSort := "Process", nameSort := "Name",
    quoteConstructor := "Quote", dropConstructor := "Drop", parallelCollection := .hashBag,
    parallelUnitConstructor := "Zero", quoteDropEquation := "quote-drop",
    -- Closed, as rho; `viewDeclaration` varies the scope.
    quoteScope := .closed }
private def controlProcess : Pattern := .apply "ProcessPayload" []
private def controlQuote : Pattern := .apply "Quote" [controlProcess]

structure Control where
  label : String
  replacement : Pattern
  body : Pattern
  expected : Pattern
  deriving DecidableEq

private def collectionControl (kind : CollType) : Control :=
  { label := "collection-kind-order-rest",
    replacement := controlQuote,
    body := .collection kind [.apply "Drop" [.bvar 0], .apply "Quote" [.apply "Drop" [.fvar "literal"]], .bvar 1] (some "tail"),
    expected := .collection kind [controlProcess, .fvar "literal", .bvar 0] (some "tail") }

/-- A drop of the quotation of a parallel pair whose first component drops the
selected name. -/
private def parallelWrappedDrop (kind : CollType) (partner : Pattern) : Pattern :=
  .apply "Drop" [.apply "Quote" [.collection kind [.apply "Drop" [.bvar 0], partner] none]]

/-- A quotation whose payload drops a free name beside the declared unit. -/
private def hiddenQuoteDrop : Pattern :=
  .apply "Quote" [.collection .hashBag [.apply "Drop" [.fvar "x"], .apply "Zero" []] none]

def controls : List Control :=
  [{ label := "selected-dropped-quote-activates", replacement := controlQuote,
      body := .apply "Drop" [.bvar 0], expected := controlProcess },
   { label := "literal-quote-is-substitution-opaque", replacement := controlQuote,
      body := .apply "Quote" [.bvar 0], expected := .apply "Quote" [.bvar 0] },
   { label := "literal-dropped-quote-remains-inert", replacement := controlQuote,
      body := .apply "Drop" [controlQuote], expected := .apply "Drop" [controlQuote] },
   { label := "lowered-name-has-no-substitution-mark", replacement := controlQuote,
      body := .apply "Drop" [.bvar 1], expected := .apply "Drop" [.bvar 0] },
   { label := "open-replacement-lifts-under-binder", replacement := .apply "Quote" [.bvar 0],
      body := .lambda (some "n") (.apply "Drop" [.bvar 1]), expected := .lambda (some "n") (.bvar 1) },
   { label := "open-name-replacement-lifts-under-binder", replacement := .apply "Quote" [.apply "Drop" [.bvar 0]],
      body := .lambda (some "n") (.apply "Drop" [.bvar 1]),
      expected := .lambda (some "n") (.apply "Drop" [.bvar 1]) },
   { label := "ordinary-indices-substitute-and-lower", replacement := .fvar "R",
      body := .apply "Pair" [.bvar 0, .bvar 2], expected := .apply "Pair" [.fvar "R", .bvar 1] },
   { label := "binder-depth-preserves-local-indices", replacement := .fvar "R",
      body := .lambda none (.apply "Triple" [.bvar 0, .bvar 1, .bvar 2]),
      expected := .lambda none (.apply "Triple" [.bvar 0, .fvar "R", .bvar 1]) },
   { label := "multi-binder-depth-and-rest-address", replacement := controlQuote,
      body := .multiLambda 2 ["a", "b"] (.collection .vec [.bvar 0, .bvar 1, .apply "Drop" [.bvar 2], .bvar 3] (some "R")),
      expected := .multiLambda 2 ["a", "b"] (.collection .vec [.bvar 0, .bvar 1, controlProcess, .bvar 2] (some "R")) },
   { label := "subst-body-and-value-have-distinct-depths", replacement := controlQuote,
      body := .subst (.apply "Triple" [.bvar 0, .apply "Drop" [.bvar 1], .bvar 2]) (.apply "Drop" [.bvar 0]),
      expected := .subst (.apply "Triple" [.bvar 0, controlProcess, .bvar 1]) controlProcess },
   { label := "static-quote-drop-normalization", replacement := controlQuote,
      body := .apply "Quote" [.apply "Drop" [.fvar "literal"]], expected := .fvar "literal" },
   { label := "rule-introduced-outer-quote-keeps-provenance",
      replacement := .apply "Quote" [.apply "Drop" [controlQuote]],
      body := .apply "Drop" [.bvar 0], expected := .apply "Drop" [controlQuote] },
   { label := "nonunary-quote-traverses-ordinary-children", replacement := controlQuote,
      body := .apply "Quote" [.bvar 0, .bvar 1], expected := .apply "Quote" [controlQuote, .bvar 0] },
   { label := "nonunary-drop-has-no-activation-case", replacement := controlQuote,
      body := .apply "Drop" [.bvar 0, .bvar 1], expected := .apply "Drop" [controlQuote, .bvar 0] },
   { label := "unmarked-free-name-remains-inert", replacement := controlQuote,
      body := .apply "Drop" [.fvar "free"], expected := .apply "Drop" [.fvar "free"] },
   { label := "normalization-can-expose-selected-name", replacement := controlQuote,
      body := .apply "Drop" [.apply "Quote" [.apply "Drop" [.bvar 0]]], expected := controlProcess },
   { label := "unit-wrapped-dropped-quote-activates", replacement := controlQuote,
      body := parallelWrappedDrop .hashBag (.apply "Zero" []), expected := controlProcess },
   { label := "non-unit-parallel-partner-stays-literal", replacement := controlQuote,
      body := parallelWrappedDrop .hashBag (.apply "Other" []),
      expected := parallelWrappedDrop .hashBag (.apply "Other" []) },
   { label := "two-selected-drops-are-not-one-name", replacement := controlQuote,
      body := parallelWrappedDrop .hashBag (.apply "Drop" [.bvar 0]),
      expected := parallelWrappedDrop .hashBag (.apply "Drop" [.bvar 0]) },
   { label := "other-collection-kind-is-not-parallel", replacement := controlQuote,
      body := parallelWrappedDrop .vec (.apply "Zero" []),
      expected := parallelWrappedDrop .vec (.apply "Zero" []) },
   collectionControl .vec, collectionControl .hashBag, collectionControl .hashSet,
   { label := "hidden-quote-drop-channel-resolves", replacement := controlQuote,
      body := .apply "Send" [hiddenQuoteDrop, .apply "Zero" []],
      expected := .apply "Send" [.fvar "x", .apply "Zero" []] },
   { label := "hidden-quote-drop-inside-quoted-code-resolves", replacement := controlQuote,
      body := .apply "Quote" [.apply "Send" [hiddenQuoteDrop, .apply "Zero" []]],
      expected := .apply "Quote" [.apply "Send" [.fvar "x", .apply "Zero" []]] },
   { label := "nested-parallel-hidden-drop-activates", replacement := controlQuote,
      body := .apply "Drop" [.apply "Quote" [.collection .hashBag
        [.collection .hashBag [.apply "Drop" [.bvar 0]] none, .apply "Zero" []] none]],
      expected := controlProcess },
   { label := "unit-first-hidden-binder-receives-quote", replacement := controlQuote,
      body := .apply "Send" [.apply "Quote" [.collection .hashBag [.apply "Zero" [], .apply "Drop" [.bvar 0]] none],
        .bvar 1],
      expected := .apply "Send" [controlQuote, .bvar 0] }]

/-- A quotation of code that mentions the eliminated binder: `@y` read as code. -/
private def quotedIndex : Pattern := .apply "Quote" [.bvar 0]

/-- **Negative admission controls.** These bodies mention the eliminated binder
inside genuine quoted code, so they are outside the closed-code fragment;
substitution still passes their quotations by (`controls`). -/
theorem inadmissible_controls :
    ¬ ReflectiveSubstitution.QuotesClosed controlDeclaration quotedIndex ∧
      ¬ ReflectiveSubstitution.QuotesClosed controlDeclaration
        (parallelWrappedDrop .hashBag (.apply "Drop" [.bvar 0])) ∧
      ¬ ReflectiveSubstitution.QuotesClosed controlDeclaration
        (parallelWrappedDrop .hashBag (.apply "Other" [])) ∧
      ¬ ReflectiveSubstitution.QuotesClosed controlDeclaration
        (parallelWrappedDrop .vec (.apply "Zero" [])) := by
  decide

/-- The control presentation with another quote scope. -/
def viewDeclaration (scope : QuoteScope) : ReflectivePresentationDecl :=
  { controlDeclaration with quoteScope := scope }

/-- A frozen spelling for the controls. -/
def frozenControl : FrozenSpelling :=
  ⟨.apply "Frozen" [], by simp [Pattern.freeFvarNames, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]⟩

/-- `Pack(@(y!(0)))`: quoted code that sends on the eliminated binder. -/
def viewBody : Pattern := .apply "Pack" [.apply "Quote" [.apply "Send" [.bvar 0, .apply "Zero" []]]]

structure ViewControl where
  label : String
  scope : QuoteScope
  expected : Pattern
  deriving DecidableEq

/-- Each reaching view acts on quoted code that mentions the eliminated binder. -/
def viewControls : List ViewControl :=
  [{ label := "apply-view-enters-quotation", scope := .reaching .apply,
      expected := .apply "Pack" [.apply "Quote" [.apply "Send" [controlQuote, .apply "Zero" []]]] },
   { label := "freeze-view-names-binder-inside", scope := .reaching (.freeze frozenControl),
      expected := .apply "Pack" [.apply "Quote" [.apply "Send" [.apply "Frozen" [], .apply "Zero" []]]] },
   { label := "closure-view-keeps-context-inside", scope := .reaching (.closure "Ctx"),
      expected := .apply "Pack" [.apply "Quote"
        [.apply "Send" [.apply "Ctx" [controlQuote], .apply "Zero" []]]] }]

private theorem viewControls_reference : viewControls.all (fun control => decide
    (ScopedRuleInstantiation.reflectiveOperation (viewDeclaration control.scope) controlQuote viewBody =
      control.expected)) = true := by
  decide +kernel

theorem viewControls_returns (state : State) (control : ViewControl) (member : control ∈ viewControls) :
    PureReturns runtime [] state (operationCall (viewDeclaration control.scope) controlQuote viewBody) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern control.expected])) := by
  have checked := List.all_eq_true.mp viewControls_reference control member
  have equal := of_decide_eq_true checked
  simpa only [operationAnswer, equal] using
    operation_returns state (viewDeclaration control.scope) controlQuote viewBody

private theorem controls_reference : controls.all (fun control => decide
    (ScopedRuleInstantiation.reflectiveOperation controlDeclaration control.replacement control.body = control.expected)) = true := by
  decide +kernel

theorem controls_returns (state : State) (control : Control) (member : control ∈ controls) :
    PureReturns runtime [] state (operationCall controlDeclaration control.replacement control.body) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern control.expected])) := by
  have checked := List.all_eq_true.mp controls_reference control member
  have equal := of_decide_eq_true checked
  simpa only [operationAnswer, equal] using operation_returns state controlDeclaration control.replacement control.body

theorem controls_completed_iff (state : State) (control : Control) (member : control ∈ controls)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run runtime fuel
      { state := state, control := .evaluate [] (operationCall controlDeclaration control.replacement control.body) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (.application "Some" [InferenceCettaWire.encodePattern control.expected])] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (controls_returns state control member) after answers input output

theorem negative_literal_drop_does_not_activate (state : State) :
    PureReturns runtime [] state (operationCall controlDeclaration controlQuote (.apply "Drop" [controlQuote])) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern (.apply "Drop" [controlQuote])])) := by
  apply controls_returns state
    ⟨"literal-dropped-quote-remains-inert", controlQuote, .apply "Drop" [controlQuote], .apply "Drop" [controlQuote]⟩
  decide +kernel

theorem negative_lowered_name_does_not_activate (state : State) :
    PureReturns runtime [] state (operationCall controlDeclaration controlQuote (.apply "Drop" [.bvar 1])) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern (.apply "Drop" [.bvar 0])])) := by
  apply controls_returns state
    ⟨"lowered-name-has-no-substitution-mark", controlQuote, .apply "Drop" [.bvar 1], .apply "Drop" [.bvar 0]⟩
  decide +kernel

theorem positive_selected_drop_activates (state : State) :
    PureReturns runtime [] state (operationCall controlDeclaration controlQuote (.apply "Drop" [.bvar 0])) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern controlProcess])) := by
  apply controls_returns state
    ⟨"selected-dropped-quote-activates", controlQuote, .apply "Drop" [.bvar 0], controlProcess⟩
  decide +kernel

def executionHeadNames : List String :=
  ["+",
   "-",
   "<",
   "==",
   ">=",
   "BinderDrop",
   "BinderIndex",
   "BinderOpaque",
   "BinderUnit",
   "Enter",
   "FVar",
   "LCons",
   "LNil",
   "Opaque",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "QuoteClosed",
   "QuoteClosure",
   "QuoteFreeze",
   "QuoteReaching",
   "RNone",
   "ReflectivePresentation",
   "Some",
   "Var",
   "case",
   "gslt:rule:instantiate-bvar-at",
   "gslt:rule:instantiate-bvar-list-at",
   "gslt:rule:lift-bvars",
   "gslt:rule:lift-bvars-list",
   "gslt:rule:scope-reflective-append",
   "gslt:rule:scope-reflective-binder-head",
   "gslt:rule:scope-reflective-binder-head-apply",
   "gslt:rule:scope-reflective-binder-head-fold",
   "gslt:rule:scope-reflective-binder-head-join",
   "gslt:rule:scope-reflective-binder-head-list",
   "gslt:rule:scope-reflective-binder-operation",
   "gslt:rule:scope-reflective-exposed-drop",
   "gslt:rule:scope-reflective-leaves",
   "gslt:rule:scope-reflective-leaves-list",
   "gslt:rule:scope-reflective-normalize",
   "gslt:rule:scope-reflective-normalize-finish",
   "gslt:rule:scope-reflective-normalize-list",
   "gslt:rule:scope-reflective-receive",
   "gslt:rule:scope-reflective-replacement",
   "gslt:rule:scope-reflective-resolve",
   "gslt:rule:scope-reflective-resolve-finish",
   "gslt:rule:scope-reflective-resolve-list",
   "gslt:rule:scope-reflective-substitute-apply",
   "gslt:rule:scope-reflective-substitute-at",
   "gslt:rule:scope-reflective-substitute-list-at",
   "gslt:rule:scope-reflective-substitute-unary",
   "if",
   "let",
   "let*"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem runtime_closed : ProgramClosed executionHeads runtime := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : runtime.equations.all (fun equation =>
        !executionHeads equation.head || codeWithin executionHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem captured_variables_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (declaration : ReflectivePresentationDecl) (replacement body : Pattern)
    (declarationName replacementName bodyName : String)
    (captured : [v declarationName, v replacementName, v bodyName].map (applySubst caller) =
      [declarationValue declaration, patternValue replacement, patternValue body]) :
    PureReturns target caller state
      (a "gslt:rule:scope-reflective-binder-operation" [v declarationName, v replacementName, v bodyName]) state
      (operationAnswer declaration replacement body) :=
  path_of_closed_agreement runtime_closed agreement ⟨by rfl, rfl⟩
    (operation_captured_returns caller state declaration replacement body _ captured)

theorem captured_variables_completed_iff_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (declaration : ReflectivePresentationDecl) (replacement body : Pattern)
    (declarationName replacementName bodyName : String)
    (captured : [v declarationName, v replacementName, v bodyName].map (applySubst caller) =
      [declarationValue declaration, patternValue replacement, patternValue body])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run target fuel { state := state, control := .evaluate caller (a "gslt:rule:scope-reflective-binder-operation" [v declarationName, v replacementName, v bodyName]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [operationAnswer declaration replacement body] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (captured_variables_returns_in_extension target agreement caller state declaration replacement body
      declarationName replacementName bodyName captured) after answers input output

theorem source_no_initializers : sourceProgram.initializers = [] := by decide +kernel

theorem source_equation_heads_unique : (sourceProgram.equations.map (·.head)).Nodup := by decide +kernel

#print axioms runtime_eq_append
#print axioms retained_program_agreement
#print axioms retained_closed
#print axioms retained_agreement
#print axioms retained_returns
#print axioms helper_clause
#print axioms helper_raw
#print axioms helper_call
#print axioms captured_closed
#print axioms helper_capture
#print axioms branch_returns
#print axioms bool_if_returns
#print axioms named_let_returns
#print axioms constructor_variables
#print axioms strings_equal_returns
#print axioms source_body
#print axioms helper_case
#print axioms data_constructor
#print axioms normalize_list_map
#print axioms normalize_finish_shape
#print axioms finish_application_returns
#print axioms finish_nonunary_result
#print axioms normalize_finish_returns
#print axioms normalize_list_returns_from_elements
#print axioms normalize_returns
#print axioms join_returns
#print axioms fold_returns
#print axioms apply_returns
#print axioms binder_head_returns
#print axioms nonunary_selection
#print axioms unary_template
#print axioms unary_constructor_returns
#print axioms replacement_nonunary_result
#print axioms replacement_returns
#print axioms receive_nonunary
#print axioms receive_returns
#print axioms append_returns
#print axioms leaves_list_returns_from_elements
#print axioms leaves_returns
#print axioms lookup_cons
#print axioms exposed_case_returns
#print axioms exposed_drop_returns
#print axioms resolve_finish_returns
#print axioms resolve_list_returns_from_elements
#print axioms resolve_returns
#print axioms substitute_unary_returns
#print axioms substitute_list_returns_from_elements
#print axioms substitute_apply_returns
#print axioms substitute_returns
#print axioms add_variables_returns
#print axioms add_one_returns
#print axioms operation_returns
#print axioms operation_captured_returns
#print axioms operation_has_sufficient_fuel
#print axioms operation_completed_iff
#print axioms captured_operation_completed_iff
#print axioms unknown_declaration_returns_none
#print axioms controls_reference
#print axioms inadmissible_controls
#print axioms viewControls_reference
#print axioms viewControls_returns
#print axioms controls_returns
#print axioms controls_completed_iff
#print axioms negative_literal_drop_does_not_activate
#print axioms negative_lowered_name_does_not_activate
#print axioms positive_selected_drop_activates
#print axioms runtime_closed
#print axioms captured_variables_returns_in_extension
#print axioms captured_variables_completed_iff_in_extension
#print axioms source_no_initializers
#print axioms source_equation_heads_unique

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedReflectiveBinderOperationExecution

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedInstantiationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching Reflection
open RuleInstantiationExecution.ScopedCapture
open InferenceCettaWire.AuthoredRule (contextualValueTerm)
open scoped ProgramQuotation

def sourceProgram : Program := RuleExecutionProgram.scopedInstantiationProgram
def runtime : Program := ScopedReflectiveBinderOperationExecution.runtime.append sourceProgram
theorem runtime_eq_append : runtime =
    ScopedReflectiveBinderOperationExecution.runtime.append sourceProgram := rfl
/-- The instantiation operations, loaded over the reflective runtime, own their heads. -/
private def library : BridgeKit.Library :=
  ⟨ScopedReflectiveBinderOperationExecution.runtime, sourceProgram,
    ["gslt:rule:scope-binder-operation", "gslt:rule:scope-instantiate-slot", "gslt:rule:scope-instantiate-at",
     "gslt:rule:scope-instantiate-args-at", "gslt:rule:scope-reduct"]⟩

/-- The base defines and calls no owned operation, and the source defines and declares only owned
operations. -/
private theorem library_checked : library.check = true := by decide +kernel

private theorem registered_of_source {head : String}
    (found : sourceProgram.equations.any (·.head == head) = true) :
    runtime.equations.any (·.head == head) = true := by
  simp only [runtime, SpaceSemantics.Program.append, List.any_append, found, Bool.or_true]

private theorem raw_of_source {head : String} {index : Nat}
    (raw : argumentIsRaw sourceProgram head index = true) : argumentIsRaw runtime head index = true := by
  unfold argumentIsRaw at raw ⊢
  by_cases native : StdLib.known head
  · simpa only [native, ↓reduceIte] using raw
  · simp only [native, Bool.false_eq_true, ↓reduceIte] at raw ⊢
    simp only [runtime, SpaceSemantics.Program.append, List.any_append, raw, Bool.or_true]

private def retainedHead (head : String) : Bool :=
  head != "eval" && !sourceProgram.equations.any (fun equation => equation.head == head) &&
    !ScopedReflectiveBinderOperationExecution.sourceProgram.equations.any (fun equation => equation.head == head)

private theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !retainedHead equation.head || codeWithin retainedHead equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem extension_fresh_equations (extension : Program)
    (checked : extension.equations.all (fun equation => !retainedHead equation.head) = true)
    (equation : SpaceSemantics.Equation) (member : equation ∈ extension.equations) :
    retainedHead equation.head = false := by
  have row := List.all_eq_true.mp checked equation member
  cases selected : retainedHead equation.head with
  | false => rfl
  | true => simp [selected] at row

private theorem extension_fresh_declarations (extension : Program)
    (checked : extension.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !retainedHead head
        | _ => true) = true)
    (name : String) (types : List Atom)
    (member : .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] ∈ extension.declarations) :
    retainedHead name = false := by
  have row := List.all_eq_true.mp checked _ member
  cases selected : retainedHead name with
  | false => rfl
  | true => simp [selected] at row

private theorem retained_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.program runtime := by
  have first : ProgramAgreementOn retainedHead RuleExecutionProgram.program
      ScopedReflectiveBinderOperationExecution.runtime :=
    ScopedReflectiveBinderOperationExecution.retained_program_agreement retainedHead
      (extension_fresh_equations _ (by decide +kernel))
      (extension_fresh_declarations _ (by decide +kernel))
  have second : ProgramAgreementOn retainedHead ScopedReflectiveBinderOperationExecution.runtime runtime :=
    appended_program_agreement retainedHead _ sourceProgram
      (extension_fresh_equations _ (by decide +kernel))
      (extension_fresh_declarations _ (by decide +kernel))
  constructor
  · intro head supported
    exact (first.dispatch head supported).trans (second.dispatch head supported)
  · intro head index supported
    exact (first.demand head index supported).trans (second.demand head index supported)
  · intro head values supported
    exact (first.bodies head values supported).trans (second.bodies head values supported)

private theorem retained_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns runtime caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev patternOptionValue (result : Option Pattern) : Atom :=
  encoded (MatchAutomataBindingExecution.patternOptionTerm result)
private abbrev payloadOptionValue (result : Option Term) : Atom :=
  encoded (MatchAutomataBindingExecution.payloadOptionTerm result)
private abbrev ruleValue (rule : RewriteRule) : Atom := encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
private abbrev specValue (spec : RuleBindingSpec) : Atom := encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)
private abbrev siteValue (site : RulePatternSite) : Atom := encoded (InferenceCettaWire.AuthoredRule.siteTerm site)
private abbrev pathValue (path : List Nat) : Atom := encoded (encodeList Term.natural path)
private abbrev assignmentValue (assignment : Assignment) : Atom := encoded (scopedAssignmentTerm assignment)
private abbrev stringValue (name : String) : Atom := encoded (.string name)

private abbrev declarationValue (declaration : ReflectivePresentationDecl) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.reflectivePresentationTerm declaration)

def operationValue (selection : Option ReflectivePresentationDecl) : Atom :=
  match selection with
  | none => .symbol "None"
  | some declaration => a "Some" [declarationValue declaration]


private inductive Helper where | binder | slot | instantiate | arguments | reduct
private def Helper.head : Helper → String
  | .binder => "gslt:rule:scope-binder-operation"
  | .slot => "gslt:rule:scope-instantiate-slot"
  | .instantiate => "gslt:rule:scope-instantiate-at"
  | .arguments => "gslt:rule:scope-instantiate-args-at"
  | .reduct => "gslt:rule:scope-reduct"
private def Helper.names : Helper → List String
  | .binder => ["operation", "replacement", "body"]
  | .slot => ["rule", "spec", "ambient", "site", "path", "depth", "assignment", "name"]
  | .instantiate => ["operation", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "pattern"]
  | .arguments => ["operation", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "index", "patterns"]
  | .reduct => ["operation", "rule", "spec", "ambient", "assignment"]
private theorem helper_owned (helper : Helper) : library.owns helper.head = true := by
  cases helper <;> decide +kernel
private def equations (head : String) : List SpaceSemantics.Equation := sourceProgram.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : SpaceSemantics.Equation := (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by
      exact (BridgeKit.Library.owned_equations library_checked (helper_owned helper)).trans
        (by cases helper <;> kernel_reflexivity)) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw sourceProgram helper.head index) = true := by
    cases helper <;> decide +kernel
  exact raw_of_source (List.all_eq_true.mp checked index (List.mem_range.mpr bounded))

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (environment helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (registered_of_source (by cases helper <;> decide +kernel))
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (by simp only [registered_of_source (head := helper.head) (by cases helper <;> decide +kernel), Bool.or_true])
    _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private def binderBody : Atom :=
  a "let" [v "result", a "gslt:rule:instantiate-bvar-at" [number 0, v "replacement", v "body"],
    a "Some" [v "result"]]
private def binderSelectedBody : Atom :=
  a "gslt:rule:scope-reflective-binder-operation" [v "declaration", v "replacement", v "body"]
private def binderCases : SpaceSemantics.Cases :=
  [(.symbol "None", binderBody), (a "Some" [v "declaration"], binderSelectedBody),
   (v "invalid", .symbol "None")]
private theorem binder_shape : (equation .binder).body =
    a "case" [v "operation", .expression (binderCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem ordinary_binder_returns (state : State) (replacement body : Pattern) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-binder-operation" [.symbol "None", patternValue replacement, patternValue body])
      state (patternOptionValue (some (Substitution.instantiateBVar replacement body))) := by
  let caller := environment .binder [.symbol "None", patternValue replacement, patternValue body]
  apply helper_call .binder [] state _ _ _ rfl (captured_closed _)
  rw [binder_shape]
  apply branch_returns caller caller state _ (.symbol "None") binderCases binderBody _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "operation"
  · simp [binderCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · unfold binderBody
    let result := Substitution.instantiateBVar replacement body
    let bound := ("result", patternValue result) :: caller
    apply let_returns runtime caller bound state state state (v "result")
      (a "gslt:rule:instantiate-bvar-at" [number 0, v "replacement", v "body"])
      (a "Some" [v "result"]) (patternValue result) _
    · exact retained_returns (by decide +kernel)
        (RuleInstantiationExecution.instantiate_bvar_at_captured_returns caller state 0 replacement body
          (number 0) (v "replacement") (v "body") (by
            simp [caller, environment, Helper.names, applySubst, Subst.lookup]))
    · simp [bound, caller, environment, Helper.names, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · simpa [patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
        patternValue, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        bound, applySubst, Subst.lookup] using
        constructor_variables_return runtime bound state "Some" ["result"] (by decide +kernel) (by decide)

#print axioms ordinary_binder_returns

private theorem reflective_agreement :
    ProgramAgreementOn ScopedReflectiveBinderOperationExecution.executionHeads
      ScopedReflectiveBinderOperationExecution.runtime runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : sourceProgram.equations.all (fun equation =>
        !ScopedReflectiveBinderOperationExecution.executionHeads equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : ScopedReflectiveBinderOperationExecution.executionHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : sourceProgram.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
            !ScopedReflectiveBinderOperationExecution.executionHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : ScopedReflectiveBinderOperationExecution.executionHeads name with
    | false => rfl
    | true => simp [selected] at row

/-- A selected declaration executes its original reflective binder operation. -/
theorem selected_binder_returns (state : State) (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-binder-operation"
        [operationValue (some declaration), patternValue replacement, patternValue body]) state
      (patternOptionValue (some (ScopedRuleInstantiation.reflectiveOperation declaration replacement body))) := by
  let values := [operationValue (some declaration), patternValue replacement, patternValue body]
  let caller := environment .binder values
  let selected := ("declaration", declarationValue declaration) :: caller
  apply helper_call .binder [] state values values _ rfl (captured_closed _)
  rw [binder_shape]
  apply branch_returns caller selected state (v "operation") (operationValue (some declaration))
    binderCases binderSelectedBody
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "operation"
  · simp [binderCases, operationValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
  · simpa only [binderSelectedBody, ScopedReflectiveBinderOperationExecution.operationAnswer,
        patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
        encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      ScopedReflectiveBinderOperationExecution.captured_variables_returns_in_extension
        runtime reflective_agreement selected state declaration replacement body
        "declaration" "replacement" "body" (by
          simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup,
            declarationValue])

#print axioms reflective_agreement
#print axioms selected_binder_returns

private def slotInstantiateBody : Atom :=
  a "gslt:rule:scope-instantiate-value" [v "value", v "ambient", v "depth", v "arguments"]
private def slotArgumentCases : SpaceSemantics.Cases :=
  [(a "Some" [v "arguments"], slotInstantiateBody), (v "missing", .symbol "None")]
private def slotArgumentBody : Atom :=
  a "case" [a "gslt:rule:scope-metadata-arguments" [v "rule", v "spec", v "name", v "site", v "path"],
    .expression (slotArgumentCases.map fun row => .expression [row.1, row.2])]
private def slotLookupCases : SpaceSemantics.Cases :=
  [(a "Some" [v "value"], slotArgumentBody), (v "missing", .symbol "None")]
private theorem slot_shape : (equation .slot).body =
    a "case" [a "gslt:automata:binding" [v "name", v "assignment"],
      .expression (slotLookupCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem contextual_lookup_returns (caller : Subst) (state : State)
    (assignment : Assignment) (name : String)
    (captured : [v "name", v "assignment"].map (applySubst caller) =
      [stringValue name, assignmentValue assignment]) :
    PureReturns runtime caller state (a "gslt:automata:binding" [v "name", v "assignment"]) state
      (payloadOptionValue ((ScopedRuleMatching.lookup assignment name).map contextualValueTerm)) := by
  apply retained_returns (by decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
  simpa only [RuleInstantiationExecution.ScopedCapture.scoped_lookup_wire] using
    MatchAutomataBindingExecution.payload_binding_captured_returns caller state name
      (assignment.map fun entry => (entry.1, contextualValueTerm entry.2)) [v "name", v "assignment"]
      (by simpa only [assignmentValue, scopedAssignmentTerm] using captured)

/-- A captured variable is instantiated at its actual authored occurrence.
Missing captures and missing occurrence metadata remain refused. -/
theorem slot_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-slot"
        [ruleValue rule, specValue spec, number ambient, siteValue site, pathValue path,
         number depth, assignmentValue assignment, stringValue name]) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment (.fvar name))) := by
  let values := [ruleValue rule, specValue spec, number ambient, siteValue site, pathValue path,
    number depth, assignmentValue assignment, stringValue name]
  let caller := environment .slot values
  apply helper_call .slot [] state values values _ rfl (captured_closed _) ?_
  rw [slot_shape]
  have looked := contextual_lookup_returns caller state assignment name (by
    simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
  unfold ScopedRuleMatching.instantiateAt?
  rw [ScopedRuleMatching.instantiateWith?.eq_1]
  cases found : ScopedRuleMatching.lookup assignment name with
  | none =>
      let selected := ("missing", .symbol "None") :: caller
      apply branch_returns caller selected state _ (.symbol "None") slotLookupCases (.symbol "None") _
      · simpa only [found, Option.map_none, payloadOptionValue,
          MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using looked
      · simp [slotLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
      · simpa [found, patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode] using symbol_returns runtime selected state "None"
  | some value =>
      let selected := ("value", encoded (contextualValueTerm value)) :: caller
      apply branch_returns caller selected state _ (a "Some" [encoded (contextualValueTerm value)])
        slotLookupCases slotArgumentBody _
      · simpa [found, payloadOptionValue, MatchAutomataBindingExecution.payloadOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using looked
      · simp [slotLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, values,
          environment, Helper.names, Subst.lookup]
      · unfold slotArgumentBody
        have argumentsReturned := retained_returns (by decide +kernel)
          (RuleInstantiationExecution.ScopedMetadata.arguments_captured_returns
            selected state rule spec name site path (v "rule") (v "spec") (v "name") (v "site") (v "path") (by
              simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]))
        change PureReturns runtime selected state
          (a "gslt:rule:scope-metadata-arguments" [v "rule", v "spec", v "name", v "site", v "path"])
          state (payloadOptionValue ((RuleBinding.arguments? rule spec name site path).map
            InferenceCettaWire.encodePatterns)) at argumentsReturned
        cases argumentsFound : RuleBinding.arguments? rule spec name site path with
        | none =>
            let framed := ("missing", .symbol "None") :: selected
            apply branch_returns selected framed state _ (.symbol "None") slotArgumentCases (.symbol "None") _
            · simpa [argumentsFound, payloadOptionValue, encoded,
                MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using argumentsReturned
            · simp [slotArgumentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, framed, selected, caller, values, environment, Helper.names, Subst.lookup]
            · simpa [found, argumentsFound, patternOptionValue,
                MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                symbol_returns runtime framed state "None"
        | some arguments =>
            let framed := ("arguments", patternsValue arguments) :: selected
            apply branch_returns selected framed state _ (a "Some" [patternsValue arguments])
              slotArgumentCases slotInstantiateBody _
            · simpa [argumentsFound, payloadOptionValue, patternsValue, encoded,
                MatchAutomataBindingExecution.payloadOptionTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using argumentsReturned
            · simp [slotArgumentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, framed, selected, caller, values,
                environment, Helper.names, Subst.lookup]
            · simpa [slotInstantiateBody, found, argumentsFound] using
                retained_returns (by decide +kernel)
                  (RuleInstantiationExecution.ScopedCapture.instantiate_value_captured_returns
                    framed state value ambient depth arguments (v "value") (v "ambient") (v "depth") (v "arguments") (by
                      simp [framed, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]))

#print axioms slot_returns

theorem ordinary_binder_captured_returns (caller : Subst) (state : State)
    (replacement body : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [.symbol "None", patternValue replacement, patternValue body]) :
    PureReturns runtime caller state (a "gslt:rule:scope-binder-operation" arguments) state
      (patternOptionValue (some (Substitution.instantiateBVar replacement body))) :=
  helper_capture .binder caller state arguments _ _ rfl captured
    (ordinary_binder_returns state replacement body)

theorem slot_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [ruleValue rule, specValue spec, number ambient, siteValue site, pathValue path,
       number depth, assignmentValue assignment, stringValue name]) :
    PureReturns runtime caller state (a "gslt:rule:scope-instantiate-slot" arguments) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment (.fvar name))) :=
  helper_capture .slot caller state arguments _ _ rfl captured
    (slot_returns state rule spec ambient site path depth assignment name)

theorem ordinary_binder_derivation_iff (state : State) (replacement body : Pattern)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs runtime
      { state, control := .evaluate []
          (a "gslt:rule:scope-binder-operation" [.symbol "None", patternValue replacement, patternValue body]) }
      (.complete after answers input output) ↔ after = state ∧ answers =
        [patternOptionValue (some (Substitution.instantiateBVar replacement body))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (ordinary_binder_returns state replacement body) after answers input output

theorem slot_derivation_iff (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs runtime
      { state, control := .evaluate [] (a "gslt:rule:scope-instantiate-slot"
        [ruleValue rule, specValue spec, number ambient, siteValue site, pathValue path,
         number depth, assignmentValue assignment, stringValue name]) } (.complete after answers input output) ↔
      after = state ∧ answers = [patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment (.fvar name))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (slot_returns state rule spec ambient site path depth assignment name) after answers input output

#print axioms ordinary_binder_captured_returns
#print axioms slot_captured_returns
#print axioms ordinary_binder_derivation_iff
#print axioms slot_derivation_iff

private def optionalValue {α : Type} (encoder : α → Atom) : Option α → Atom
  | none => .symbol "None"
  | some value => a "Some" [encoder value]

private def optionalCases (name : String) (body : Atom) : SpaceSemantics.Cases :=
  [(a "Some" [v name], body), (v "failed", .symbol "None")]

private theorem optional_returns {α : Type} (caller : Subst) (state : State)
    (expression : Atom) (result : Option α) (encoder : α → Atom)
    (name : String) (body : Atom) (answer : Option α → Atom)
    (fresh : Subst.lookup caller name = none)
    (failedFresh : Subst.lookup caller "failed" = none)
    (noneAnswer : answer none = .symbol "None")
    (computed : PureReturns runtime caller state expression state (optionalValue encoder result))
    (continued : ∀ value, result = some value →
      PureReturns runtime ((name, encoder value) :: caller) state body state (answer (some value))) :
    PureReturns runtime caller state
      (a "case" [expression, .expression ((optionalCases name body).map fun row => .expression [row.1, row.2])])
      state (answer result) := by
  cases result with
  | none =>
      apply branch_returns caller (("failed", .symbol "None") :: caller) state expression
        (.symbol "None") (optionalCases name body) (.symbol "None") _ computed
      · simp [optionalCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
          failedFresh]
      · rw [noneAnswer]
        exact symbol_returns runtime _ state "None"
  | some value =>
      apply branch_returns caller ((name, encoder value) :: caller) state expression
        (a "Some" [encoder value]) (optionalCases name body) body _ computed
      · simp [optionalCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, fresh]
      · exact continued value rfl

#print axioms optional_returns

private def variableBody : Atom :=
  a "gslt:rule:scope-instantiate-slot" [v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "name"]

private def boundBody : Atom :=
  a "Some" [v "pattern"]

private def applicationBody : Atom :=
  a "case" [a "gslt:rule:scope-instantiate-args-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", number 0, v "children"], .expression [.expression [a "Some" [v "values"], a "let" [v "result", a "PApp" [v "head", v "values"], a "Some" [v "result"]]], .expression [v "failed", .symbol "None"]]]

private def lambdaBody : Atom :=
  a "let*" [.expression [.expression [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]], .expression [v "child-depth", a "+" [v "depth", number 1]]], a "case" [a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "child-depth", v "assignment", v "body"], .expression [.expression [a "Some" [v "value"], a "let" [v "result", a "PLam" [v "binder", v "value"], a "Some" [v "result"]]], .expression [v "failed", .symbol "None"]]]]

private def multiLambdaBody : Atom :=
  a "let*" [.expression [.expression [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]], .expression [v "child-depth", a "+" [v "depth", v "arity"]]], a "case" [a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "child-depth", v "assignment", v "body"], .expression [.expression [a "Some" [v "value"], a "let" [v "result", a "PMultiLam" [v "arity", v "binders", v "value"], a "Some" [v "result"]]], .expression [v "failed", .symbol "None"]]]]

private def substitutionBody : Atom :=
  a "let*" [.expression [.expression [v "body-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]], .expression [v "body-depth", a "+" [v "depth", number 1]]], a "case" [a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "body-path", v "body-depth", v "assignment", v "body"], .expression [.expression [a "Some" [v "body-value"], a "let" [v "replacement-path", a "gslt:automata:append" [v "path", a "LCons" [number 1, .symbol "LNil"]], a "case" [a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "replacement-path", v "depth", v "assignment", v "replacement"], .expression [.expression [a "Some" [v "replacement-value"], a "gslt:rule:scope-binder-operation" [v "operation", v "replacement-value", v "body-value"]], .expression [v "failed", .symbol "None"]]]]], .expression [v "failed", .symbol "None"]]]]

private def collectionBody : Atom :=
  a "case" [a "gslt:rule:scope-instantiate-args-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", number 0, v "elements"], .expression [.expression [a "Some" [v "explicit"], a "case" [v "rest", .expression [a "RNone" [a "let" [v "result", a "PCollection" [v "kind", v "explicit", .symbol "RNone"], a "Some" [v "result"]]], .expression [a "RSome" [v "name"], a "let*" [.expression [.expression [v "length", a "gslt:automata:length" [v "elements"]], .expression [v "rest-path", a "gslt:automata:append" [v "path", a "LCons" [v "length", .symbol "LNil"]]]], a "case" [a "gslt:rule:scope-instantiate-slot" [v "rule", v "spec", v "ambient", v "site", v "rest-path", v "depth", v "assignment", v "name"], .expression [.expression [a "Some" [a "PCollection" [v "actual-kind", v "residual", .symbol "RNone"]], a "if" [a "==" [v "actual-kind", v "kind"], a "let*" [.expression [.expression [v "values", a "gslt:automata:append" [v "explicit", v "residual"]], .expression [v "result", a "PCollection" [v "kind", v "values", .symbol "RNone"]]], a "Some" [v "result"]], .symbol "None"]], .expression [v "failed", .symbol "None"]]]]], .expression [v "invalid", .symbol "None"]]]], .expression [v "failed", .symbol "None"]]]

private def invalidBody : Atom :=
  .symbol "None"

private def instantiationCases : SpaceSemantics.Cases :=
  [(a "FVar" [v "name"], variableBody),
   (a "Var" [v "index"], boundBody),
   (a "PApp" [v "head", v "children"], applicationBody),
   (a "PLam" [v "binder", v "body"], lambdaBody),
   (a "PMultiLam" [v "arity", v "binders", v "body"], multiLambdaBody),
   (a "PSubst" [v "body", v "replacement"], substitutionBody),
   (a "PCollection" [v "kind", v "elements", v "rest"], collectionBody),
   (v "invalid", invalidBody)]

private def argumentsConsBody : Atom :=
  a "let" [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]], a "case" [a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "depth", v "assignment", v "pattern"], .expression [.expression [a "Some" [v "head"], a "let" [v "next", a "+" [v "index", number 1], a "case" [a "gslt:rule:scope-instantiate-args-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "next", v "rest"], .expression [.expression [a "Some" [v "tail"], a "let" [v "values", a "LCons" [v "head", v "tail"], a "Some" [v "values"]]], .expression [v "failed", .symbol "None"]]]]], .expression [v "failed", .symbol "None"]]]]

private def argumentsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [.symbol "LNil"]),
   (a "LCons" [v "pattern", v "rest"], argumentsConsBody),
   (v "invalid", .symbol "None")]

private theorem instantiation_shape : (equation .instantiate).body =
    a "case" [v "pattern", .expression (instantiationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem arguments_shape : (equation .arguments).body =
    a "case" [v "patterns", .expression (argumentsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

def instantiationValues (operation : Atom) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) : List Atom :=
  [operation, ruleValue rule, specValue spec, number ambient, siteValue site,
   pathValue path, number depth, assignmentValue assignment, patternValue pattern]

private def argumentsValues (operation : Atom) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns : List Pattern) : List Atom :=
  [operation, ruleValue rule, specValue spec, number ambient, siteValue site,
   pathValue path, number depth, assignmentValue assignment, number index, patternsValue patterns]

private theorem instantiation_case_returns (state : State)
    (operation : Atom) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase
        (environment .instantiate (instantiationValues operation rule spec ambient site path depth assignment pattern))
        (patternValue pattern) instantiationCases = some (selected, body))
    (returned : PureReturns runtime selected state body state answer) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operation rule spec ambient site path depth assignment pattern)) state answer := by
  apply helper_call .instantiate [] state _ _ _ rfl (captured_closed _) ?_
  rw [instantiation_shape]
  apply branch_returns _ selected state _ (patternValue pattern) instantiationCases body answer _ matched returned
  simpa [environment, Helper.names, instantiationValues, applySubst, Subst.lookup] using
    variable_returns runtime
      (environment .instantiate (instantiationValues operation rule spec ambient site path depth assignment pattern))
      state "pattern"

private theorem arguments_case_returns (state : State)
    (operation : Atom) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns : List Pattern)
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase
        (environment .arguments (argumentsValues operation rule spec ambient site path depth assignment index patterns))
        (patternsValue patterns) argumentsCases = some (selected, body))
    (returned : PureReturns runtime selected state body state answer) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-args-at"
        (argumentsValues operation rule spec ambient site path depth assignment index patterns)) state answer := by
  apply helper_call .arguments [] state _ _ _ rfl (captured_closed _) ?_
  rw [arguments_shape]
  apply branch_returns _ selected state _ (patternsValue patterns) argumentsCases body answer _ matched returned
  simpa [environment, Helper.names, argumentsValues, applySubst, Subst.lookup] using
    variable_returns runtime
      (environment .arguments (argumentsValues operation rule spec ambient site path depth assignment index patterns))
      state "patterns"

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem append_path_returns (caller : Subst) (state : State) (path : List Nat) (index : Nat)
    (one two : Atom)
    (matcherOne : codeWithin RuleExecutionProgram.matcherHead one = true)
    (matcherTwo : codeWithin RuleExecutionProgram.matcherHead two = true)
    (retainedOne : codeWithin retainedHead one = true)
    (retainedTwo : codeWithin retainedHead two = true)
    (captured : [one, two].map (applySubst caller) = [pathValue path, pathValue [index]]) :
    PureReturns runtime caller state (a "gslt:automata:append" [one, two]) state
      (pathValue (path ++ [index])) := by
  have lifted := RuleExecutionProgram.automata_captured_returns (by
      simp [codeWithin, expressionHeadWithin, atomsWithin, RuleExecutionProgram.matcherHead, matcherOne, matcherTwo])
    (MatchAutomataSourceExecution.append_captured_returns caller state (path.map Term.natural) [Term.natural index]
      one two (by simpa [pathValue, MatchAutomataSourceExecution.listValue] using captured))
  have kept := retained_returns (by
    simp [codeWithin, expressionHeadWithin, atomsWithin, retainedHead, retainedOne, retainedTwo]
    decide +kernel) lifted
  have mapped : path.map Term.natural ++ [Term.natural index] = (path ++ [index]).map Term.natural := by simp
  change PureReturns runtime caller state (a "gslt:automata:append" [one, two]) state
    (encoded (encodeList id (path.map Term.natural ++ [Term.natural index]))) at kept
  rw [mapped, encodeList_map] at kept
  exact kept

private theorem add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns runtime caller state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns runtime caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns runtime caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns runtime caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state name
  · exact grounded_returns runtime caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

#print axioms instantiation_case_returns
#print axioms arguments_case_returns
#print axioms append_path_returns
#print axioms add_variables_returns
#print axioms add_one_returns

private theorem pattern_option_optional (result : Option Pattern) :
    patternOptionValue result = optionalValue patternValue result := by cases result <;> rfl

private def instantiationArguments : List Atom :=
  [v "operation", v "rule", v "spec", v "ambient", v "site", v "path",
   v "depth", v "assignment", v "pattern"]

theorem instantiate_variable_returns (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.fvar name))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.fvar name))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.fvar name))
  let selected := ("name", stringValue name) :: caller
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.fvar name) selected variableBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, stringValue, Subst.lookup]
  · simpa only [variableBody, ScopedRuleMatching.instantiateWith?.eq_1,
      ScopedRuleMatching.instantiateAt?] using
      slot_captured_returns selected state rule spec ambient site path depth assignment name
        [v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "name"] (by
          simp [selected, caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup])

theorem instantiate_bound_returns (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.bvar index))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.bvar index))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.bvar index))
  let selected := ("index", number index) :: caller
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.bvar index) selected boundBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, Subst.lookup]
  · simpa [boundBody, ScopedRuleMatching.instantiateWith?, patternOptionValue,
      MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      patternValue, encoded, selected, caller, environment, Helper.names, instantiationValues,
      applySubst, Subst.lookup] using
      constructor_variables_return runtime selected state "Some" ["pattern"] (by decide +kernel) (by decide)

private def argumentsNextBody : Atom :=
  a "let" [v "next", a "+" [v "index", number 1], a "case" [a "gslt:rule:scope-instantiate-args-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "next", v "rest"], .expression [.expression [a "Some" [v "tail"], a "let" [v "values", a "LCons" [v "head", v "tail"], a "Some" [v "values"]]], .expression [v "failed", .symbol "None"]]]]

private def argumentsTailBody : Atom :=
  a "let" [v "values", a "LCons" [v "head", v "tail"], a "Some" [v "values"]]

private theorem arguments_from_elements (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, ∀ childPath,
      PureReturns runtime [] state
        (a "gslt:rule:scope-instantiate-at"
          (instantiationValues operationValue rule spec ambient site childPath depth assignment pattern)) state
        (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
          rule spec ambient site childPath depth assignment pattern))) (index : Nat) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-args-at"
        (argumentsValues operationValue rule spec ambient site path depth assignment index patterns)) state
      (optionalValue patternsValue (ScopedRuleMatching.instantiateArgsWith? operation
        rule spec ambient site path depth assignment index patterns)) := by
  induction patterns generalizing index with
  | nil =>
      let caller := environment .arguments
        (argumentsValues operationValue rule spec ambient site path depth assignment index [])
      apply arguments_case_returns state operationValue rule spec ambient site path depth assignment index []
        caller (a "Some" [.symbol "LNil"])
      · simp [argumentsCases, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, caller]
      · simpa [ScopedRuleMatching.instantiateArgsWith?, optionalValue, patternsValue,
          InferenceCettaWire.encodePatterns, CettaWireAtom.encode, applySubst,
          applySubst.applySubstList] using
          PureData.template_return runtime caller state (a "Some" [.symbol "LNil"])
            (.constructor "Some" [.symbol "LNil"] (by decide +kernel) (by decide)
              (by intro argument member; simp only [List.mem_singleton] at member; subst argument; exact .symbol _))
  | cons pattern patterns ih =>
      let caller := environment .arguments
        (argumentsValues operationValue rule spec ambient site path depth assignment index (pattern :: patterns))
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let childBound := ("child-path", pathValue (path ++ [index])) :: selected
      let headResult := ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site (path ++ [index]) depth assignment pattern
      let tailResult := ScopedRuleMatching.instantiateArgsWith? operation
        rule spec ambient site path depth assignment (index + 1) patterns
      have headReturned := helper_capture .instantiate childBound state
        [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "depth", v "assignment", v "pattern"]
        (instantiationValues operationValue rule spec ambient site (path ++ [index]) depth assignment pattern)
        _ rfl (by
          simp [childBound, selected, caller, environment, Helper.names, argumentsValues,
            instantiationValues, applySubst, Subst.lookup])
        (elements pattern (by simp) (path ++ [index]))
      apply arguments_case_returns state operationValue rule spec ambient site path depth assignment
        index (pattern :: patterns) selected argumentsConsBody
      · simp [argumentsCases, patternsValue, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
      · rw [ScopedRuleMatching.instantiateArgsWith?.eq_2]
        unfold argumentsConsBody
        apply named_let_returns selected state "child-path" _ (pathValue (path ++ [index]))
        · simp [selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
        · apply append_path_returns selected state path index (v "path") (a "LCons" [v "index", .symbol "LNil"])
            (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
          simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            selected, caller, environment, Helper.names, argumentsValues,
            applySubst, applySubst.applySubstList, Subst.lookup]
        · apply optional_returns childBound state _ headResult patternValue "head" argumentsNextBody
            (fun result => optionalValue patternsValue (result.bind fun head => tailResult.bind fun tail => some (head :: tail)))
          · simp [childBound, selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
          · simp [childBound, selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
          · rfl
          · simpa only [Helper.head, headResult, pattern_option_optional] using headReturned
          · intro head _found
            let headBound := ("head", patternValue head) :: childBound
            let nextBound := ("next", number (index + 1)) :: headBound
            have tailReturned := helper_capture .arguments nextBound state
              [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "next", v "rest"]
              (argumentsValues operationValue rule spec ambient site path depth assignment (index + 1) patterns)
              _ rfl (by
                simp [nextBound, headBound, childBound, selected, caller, environment, Helper.names,
                  argumentsValues, applySubst, Subst.lookup])
              (ih (fun child member childPath => elements child (List.mem_cons_of_mem _ member) childPath) (index + 1))
            unfold argumentsNextBody
            apply named_let_returns headBound state "next" _ (number (index + 1))
            · simp [headBound, childBound, selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
            · apply add_one_returns headBound state index "index"
              simp [headBound, childBound, selected, caller, environment, Helper.names, argumentsValues,
                applySubst, Subst.lookup]
            · apply optional_returns nextBound state _ tailResult patternsValue "tail" argumentsTailBody
                (fun result => optionalValue patternsValue (result.bind fun tail => some (head :: tail)))
              · simp [nextBound, headBound, childBound, selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
              · simp [nextBound, headBound, childBound, selected, caller, environment, Helper.names, argumentsValues, Subst.lookup]
              · rfl
              · simpa only [Helper.head, tailResult] using tailReturned
              · intro tail _tailFound
                let tailBound := ("tail", patternsValue tail) :: nextBound
                let valuesBound := ("values", patternsValue (head :: tail)) :: tailBound
                unfold argumentsTailBody
                apply named_let_returns tailBound state "values" _ (patternsValue (head :: tail))
                · simp [tailBound, nextBound, headBound, childBound, selected, caller, environment,
                    Helper.names, argumentsValues, Subst.lookup]
                · simpa [patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, tailBound, nextBound, headBound, childBound, applySubst,
                    Subst.lookup] using
                    constructor_variables_return runtime tailBound state "LCons" ["head", "tail"] (by decide +kernel) (by decide)
                · simpa [optionalValue, patternsValue, encoded, valuesBound, applySubst, Subst.lookup] using
                    constructor_variables_return runtime valuesBound state "Some" ["values"] (by decide +kernel) (by decide)

#print axioms instantiate_variable_returns
#print axioms instantiate_bound_returns
#print axioms arguments_from_elements

private def applicationResultBody : Atom :=
  a "let" [v "result", a "PApp" [v "head", v "values"], a "Some" [v "result"]]

private theorem instantiate_application_from_arguments (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (head : String) (children : List Pattern)
    (childrenReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-args-at"
        (argumentsValues operationValue rule spec ambient site path depth assignment 0 children)) state
      (optionalValue patternsValue (ScopedRuleMatching.instantiateArgsWith? operation
        rule spec ambient site path depth assignment 0 children))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.apply head children))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.apply head children))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.apply head children))
  let selected := ("children", patternsValue children) :: ("head", stringValue head) :: caller
  let result := ScopedRuleMatching.instantiateArgsWith? operation
    rule spec ambient site path depth assignment 0 children
  have recursive := helper_capture .arguments selected state
    [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", number 0, v "children"]
    (argumentsValues operationValue rule spec ambient site path depth assignment 0 children)
    _ rfl (by simp [selected, caller, environment, Helper.names, instantiationValues, argumentsValues,
      applySubst, Subst.lookup]) childrenReturned
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.apply head children) selected applicationBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, stringValue, Subst.lookup]
  · rw [ScopedRuleMatching.instantiateWith?.eq_3]
    unfold applicationBody
    apply optional_returns selected state _ result patternsValue "values" applicationResultBody
      (fun values => patternOptionValue (values.bind fun arguments => some (.apply head arguments)))
    · simp [selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
    · simp [selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
    · rfl
    · simpa only [Helper.head, result] using recursive
    · intro values _found
      let framed := ("values", patternsValue values) :: selected
      let final := ("result", patternValue (.apply head values)) :: framed
      unfold applicationResultBody
      apply named_let_returns framed state "result" _ (patternValue (.apply head values))
      · simp [framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · simpa [patternValue, encoded, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, framed, selected, caller, stringValue, applySubst, Subst.lookup] using
          constructor_variables_return runtime framed state "PApp" ["head", "values"] (by decide +kernel) (by decide)
      · simpa [patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, final, applySubst, Subst.lookup] using
          constructor_variables_return runtime final state "Some" ["result"] (by decide +kernel) (by decide)

#print axioms instantiate_application_from_arguments

private theorem some_result_returns (caller : Subst) (state : State) (expression value : Atom)
    (fresh : Subst.lookup caller "result" = none)
    (computed : PureReturns runtime caller state expression state value) :
    PureReturns runtime caller state
      (a "let" [v "result", expression, a "Some" [v "result"]]) state (a "Some" [value]) := by
  apply named_let_returns caller state "result" expression value _ _ fresh computed
  simpa [applySubst, Subst.lookup] using
    constructor_variables_return runtime (("result", value) :: caller) state "Some" ["result"]
      (by decide +kernel) (by decide)

private def lambdaResultBody : Atom :=
  a "let" [v "result", a "PLam" [v "binder", v "value"], a "Some" [v "result"]]
private def multiLambdaResultBody : Atom :=
  a "let" [v "result", a "PMultiLam" [v "arity", v "binders", v "value"], a "Some" [v "result"]]

private theorem instantiate_lambda_from_body (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (binder : Option String) (body : Pattern)
    (bodyReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + 1) assignment body)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site (path ++ [0]) (depth + 1) assignment body))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.lambda binder body))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.lambda binder body))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.lambda binder body))
  let selected := ("body", patternValue body) ::
    ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
  let pathBound := ("child-path", pathValue (path ++ [0])) :: selected
  let nextBound := ("child-depth", number (depth + 1)) :: pathBound
  let result := ScopedRuleMatching.instantiateWith? operation
    rule spec ambient site (path ++ [0]) (depth + 1) assignment body
  have recursive := helper_capture .instantiate nextBound state
    [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "child-depth", v "assignment", v "body"]
    (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + 1) assignment body)
    _ rfl (by simp [nextBound, pathBound, selected, caller, environment, Helper.names,
      instantiationValues, applySubst, Subst.lookup]) bodyReturned
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.lambda binder body) selected lambdaBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, Subst.lookup]
  · rw [ScopedRuleMatching.instantiateWith?.eq_4]
    unfold lambdaBody
    apply PureData.let_bindings_return
      (pairs := [(v "child-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
        (v "child-depth", a "+" [v "depth", number 1])]) (final := nextBound)
    · apply PureData.BindingsReturn.cons (bound := pathBound)
      · apply append_path_returns selected state path 0 (v "path") (a "LCons" [number 0, .symbol "LNil"])
          (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
        simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, environment, Helper.names, instantiationValues, applySubst,
          applySubst.applySubstList, Subst.lookup]
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          pathBound, selected, caller, environment, Helper.names, instantiationValues]
      · apply PureData.BindingsReturn.cons (bound := nextBound)
        · apply add_one_returns pathBound state depth "depth"
          simp [pathBound, selected, caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues]
        · exact .nil _ _
    · apply optional_returns nextBound state _ result patternValue "value" lambdaResultBody
        (fun result => patternOptionValue (result.bind fun value => some (.lambda binder value)))
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · rfl
      · simpa only [Helper.head, result, pattern_option_optional] using recursive
      · intro value _found
        let framed := ("value", patternValue value) :: nextBound
        unfold lambdaResultBody
        rw [pattern_option_optional]
        apply some_result_returns framed state _ (patternValue (.lambda binder value))
        · simp [framed, nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
        · simpa [patternValue, encoded, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, framed, nextBound, pathBound, selected, caller,
            applySubst, Subst.lookup] using
            constructor_variables_return runtime framed state "PLam" ["binder", "value"] (by decide +kernel) (by decide)

private theorem instantiate_multiLambda_from_body (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (arity : Nat) (binders : List String) (body : Pattern)
    (bodyReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + arity) assignment body)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site (path ++ [0]) (depth + arity) assignment body))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.multiLambda arity binders body))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.multiLambda arity binders body))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.multiLambda arity binders body))
  let selected := ("body", patternValue body) :: ("binders", encoded (encodeList Term.string binders)) ::
    ("arity", number arity) :: caller
  let pathBound := ("child-path", pathValue (path ++ [0])) :: selected
  let nextBound := ("child-depth", number (depth + arity)) :: pathBound
  let result := ScopedRuleMatching.instantiateWith? operation
    rule spec ambient site (path ++ [0]) (depth + arity) assignment body
  have recursive := helper_capture .instantiate nextBound state
    [v "operation", v "rule", v "spec", v "ambient", v "site", v "child-path", v "child-depth", v "assignment", v "body"]
    (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + arity) assignment body)
    _ rfl (by simp [nextBound, pathBound, selected, caller, environment, Helper.names,
      instantiationValues, applySubst, Subst.lookup]) bodyReturned
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.multiLambda arity binders body) selected multiLambdaBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, Subst.lookup]
  · rw [ScopedRuleMatching.instantiateWith?.eq_5]
    unfold multiLambdaBody
    apply PureData.let_bindings_return
      (pairs := [(v "child-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
        (v "child-depth", a "+" [v "depth", v "arity"])]) (final := nextBound)
    · apply PureData.BindingsReturn.cons (bound := pathBound)
      · apply append_path_returns selected state path 0 (v "path") (a "LCons" [number 0, .symbol "LNil"])
          (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
        simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, environment, Helper.names, instantiationValues, applySubst,
          applySubst.applySubstList, Subst.lookup]
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          pathBound, selected, caller, environment, Helper.names, instantiationValues]
      · apply PureData.BindingsReturn.cons (bound := nextBound)
        · apply add_variables_returns pathBound state depth arity "depth" "arity"
          · simp [pathBound, selected, caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup]
          · simp [pathBound, selected, caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues]
        · exact .nil _ _
    · apply optional_returns nextBound state _ result patternValue "value" multiLambdaResultBody
        (fun result => patternOptionValue (result.bind fun value => some (.multiLambda arity binders value)))
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · rfl
      · simpa only [Helper.head, result, pattern_option_optional] using recursive
      · intro value _found
        let framed := ("value", patternValue value) :: nextBound
        unfold multiLambdaResultBody
        rw [pattern_option_optional]
        apply some_result_returns framed state _ (patternValue (.multiLambda arity binders value))
        · simp [framed, nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
        · simpa [patternValue, encoded, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, framed, nextBound, pathBound, selected, caller,
            applySubst, Subst.lookup] using
            constructor_variables_return runtime framed state "PMultiLam" ["arity", "binders", "value"] (by decide +kernel) (by decide)

#print axioms instantiate_lambda_from_body
#print axioms instantiate_multiLambda_from_body

private def substitutionReplacementBody : Atom :=
  a "let" [v "replacement-path", a "gslt:automata:append" [v "path", a "LCons" [number 1, .symbol "LNil"]],
    a "case" [a "gslt:rule:scope-instantiate-at"
      [v "operation", v "rule", v "spec", v "ambient", v "site", v "replacement-path", v "depth", v "assignment", v "replacement"],
      .expression [.expression [a "Some" [v "replacement-value"],
        a "gslt:rule:scope-binder-operation" [v "operation", v "replacement-value", v "body-value"]],
        .expression [v "failed", .symbol "None"]]]]

private def substitutionOperationBody : Atom :=
  a "gslt:rule:scope-binder-operation" [v "operation", v "replacement-value", v "body-value"]

private theorem instantiate_substitution_from_children (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (body replacement : Pattern)
    (bodyReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + 1) assignment body)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site (path ++ [0]) (depth + 1) assignment body)))
    (replacementReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site (path ++ [1]) depth assignment replacement)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site (path ++ [1]) depth assignment replacement)))
    (operationReturned : ∀ replacement body,
      PureReturns runtime [] state
        (a "gslt:rule:scope-binder-operation" [operationValue, patternValue replacement, patternValue body]) state
        (patternOptionValue (some (operation replacement body)))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.subst body replacement))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.subst body replacement))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.subst body replacement))
  let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
  let pathBound := ("body-path", pathValue (path ++ [0])) :: selected
  let nextBound := ("body-depth", number (depth + 1)) :: pathBound
  let bodyResult := ScopedRuleMatching.instantiateWith? operation
    rule spec ambient site (path ++ [0]) (depth + 1) assignment body
  let replacementResult := ScopedRuleMatching.instantiateWith? operation
    rule spec ambient site (path ++ [1]) depth assignment replacement
  have recursive := helper_capture .instantiate nextBound state
    [v "operation", v "rule", v "spec", v "ambient", v "site", v "body-path", v "body-depth", v "assignment", v "body"]
    (instantiationValues operationValue rule spec ambient site (path ++ [0]) (depth + 1) assignment body)
    _ rfl (by simp [nextBound, pathBound, selected, caller, environment, Helper.names,
      instantiationValues, applySubst, Subst.lookup]) bodyReturned
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.subst body replacement) selected substitutionBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, Subst.lookup]
  · rw [ScopedRuleMatching.instantiateWith?.eq_6]
    unfold substitutionBody
    apply PureData.let_bindings_return
      (pairs := [(v "body-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
        (v "body-depth", a "+" [v "depth", number 1])]) (final := nextBound)
    · apply PureData.BindingsReturn.cons (bound := pathBound)
      · apply append_path_returns selected state path 0 (v "path") (a "LCons" [number 0, .symbol "LNil"])
          (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
        simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, environment, Helper.names, instantiationValues, applySubst,
          applySubst.applySubstList, Subst.lookup]
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          pathBound, selected, caller, environment, Helper.names, instantiationValues]
      · apply PureData.BindingsReturn.cons (bound := nextBound)
        · apply add_one_returns pathBound state depth "depth"
          simp [pathBound, selected, caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues]
        · exact .nil _ _
    · apply optional_returns nextBound state _ bodyResult patternValue "body-value" substitutionReplacementBody
        (fun result => patternOptionValue (result.bind fun bodyValue =>
          replacementResult.bind fun replacementValue => some (operation replacementValue bodyValue)))
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · simp [nextBound, pathBound, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
      · rfl
      · simpa only [Helper.head, bodyResult, pattern_option_optional] using recursive
      · intro bodyValue _found
        let bodyBound := ("body-value", patternValue bodyValue) :: nextBound
        let replacementBound := ("replacement-path", pathValue (path ++ [1])) :: bodyBound
        unfold substitutionReplacementBody
        apply named_let_returns bodyBound state "replacement-path" _ _ _ _
        · simp [bodyBound, nextBound, pathBound, selected, caller, environment, Helper.names,
            instantiationValues, Subst.lookup]
        · apply append_path_returns bodyBound state path 1 (v "path") (a "LCons" [number 1, .symbol "LNil"])
            (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
          simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            bodyBound, nextBound, pathBound, selected, caller, environment, Helper.names,
            instantiationValues, applySubst, applySubst.applySubstList, Subst.lookup]
        · apply optional_returns replacementBound state _ replacementResult patternValue "replacement-value"
            substitutionOperationBody
            (fun result => patternOptionValue (result.bind fun replacementValue => some (operation replacementValue bodyValue)))
          · simp [replacementBound, bodyBound, nextBound, pathBound, selected, caller, environment,
              Helper.names, instantiationValues, Subst.lookup]
          · simp [replacementBound, bodyBound, nextBound, pathBound, selected, caller, environment,
              Helper.names, instantiationValues, Subst.lookup]
          · rfl
          · rw [← pattern_option_optional]
            simpa only [Helper.head] using helper_capture .instantiate replacementBound state
              [v "operation", v "rule", v "spec", v "ambient", v "site", v "replacement-path", v "depth", v "assignment", v "replacement"]
              (instantiationValues operationValue rule spec ambient site (path ++ [1]) depth assignment replacement)
              _ rfl (by simp [replacementBound, bodyBound, nextBound, pathBound, selected, caller,
                environment, Helper.names, instantiationValues, applySubst, Subst.lookup]) replacementReturned
          · intro replacementValue _found
            let operationBound := ("replacement-value", patternValue replacementValue) :: replacementBound
            unfold substitutionOperationBody
            simpa only [Helper.head, Option.bind_some, operationBound] using helper_capture .binder operationBound state
              [v "operation", v "replacement-value", v "body-value"]
              [operationValue, patternValue replacementValue, patternValue bodyValue] _ rfl
              (by simp [operationBound, replacementBound, bodyBound, nextBound, pathBound, selected,
                caller, environment, Helper.names, instantiationValues, applySubst, Subst.lookup])
              (operationReturned replacementValue bodyValue)

#print axioms instantiate_substitution_from_children

private theorem lookup_cons (caller : Subst) (name query : String) (value : Atom) :
    Subst.lookup ((name, value) :: caller) query =
      if name == query then some value else Subst.lookup caller query := by
  simp only [Subst.lookup, List.find?_cons]
  cases same : (name == query) <;> simp

private theorem variable_cons (caller : Subst) (name query : String) (value : Atom) :
    applySubst ((name, value) :: caller) (v query) =
      if name == query then value else applySubst caller (v query) := by
  simp only [applySubst, lookup_cons]
  cases same : (name == query) <;> simp

attribute [local simp] lookup_cons variable_cons

private abbrev kindValue (kind : CollType) : Atom :=
  encoded (InferenceCettaWire.encodeCollectionType kind)

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem collection_type_encode_eq (left right : CollType) :
    InferenceCettaWire.encodeCollectionType left = InferenceCettaWire.encodeCollectionType right ↔ left = right := by
  constructor
  · intro equal
    have decoded := congrArg InferenceCettaWire.decodeCollectionType equal
    simpa using decoded
  · rintro rfl
    rfl

private theorem append_patterns_returns (caller : Subst) (state : State) (left right : List Pattern)
    (first second : String)
    (captured : [v first, v second].map (applySubst caller) = [patternsValue left, patternsValue right]) :
    PureReturns runtime caller state (a "gslt:automata:append" [v first, v second]) state
      (patternsValue (left ++ right)) := by
  apply retained_returns (by
    simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead]
    decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  simpa only [patternsValue, encoded, InferenceCettaWire.encodePatterns_eq_encodeList,
      MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp,
      ← List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map InferenceCettaWire.encodePattern) (right.map InferenceCettaWire.encodePattern) (v first) (v second)
      (by simpa only [patternsValue, encoded, InferenceCettaWire.encodePatterns_eq_encodeList,
        MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)

private theorem length_patterns_returns (caller : Subst) (state : State) (values : List Pattern)
    (argument : String) (captured : applySubst caller (v argument) = patternsValue values) :
    PureReturns runtime caller state (a "gslt:automata:length" [v argument]) state (number values.length) := by
  apply retained_returns (by
    simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead]
    decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  simpa only [List.length_map] using
    MatchAutomataSourceExecution.length_captured_returns caller state
      (values.map InferenceCettaWire.encodePattern) (v argument)
      (by simpa only [patternsValue, encoded, InferenceCettaWire.encodePatterns_eq_encodeList,
        MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)

private def collectionResidualOption (kind : CollType) (explicit : List Pattern)
    (result : Option Pattern) : Option Pattern :=
  result.bind fun value => match value with
    | .collection actualKind residual none =>
        if actualKind == kind then some (.collection kind (explicit ++ residual) none) else none
    | _ => none

private def collectionSpliceBody : Atom :=
  a "let*" [.expression [
    .expression [v "values", a "gslt:automata:append" [v "explicit", v "residual"]],
    .expression [v "result", a "PCollection" [v "kind", v "values", .symbol "RNone"]]],
    a "Some" [v "result"]]

private def collectionResidualBody : Atom :=
  a "if" [a "==" [v "actual-kind", v "kind"], collectionSpliceBody, .symbol "None"]

private def collectionResidualCases : SpaceSemantics.Cases :=
  [(a "Some" [a "PCollection" [v "actual-kind", v "residual", .symbol "RNone"]], collectionResidualBody),
    (v "failed", .symbol "None")]

private theorem match_value_var (caller : Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue caller (v name) value = matchAtom caller (v name) value := by
  cases value <;> simp only [v, SpaceSemantics.matchValue]

private theorem match_head_mismatch (caller : Subst) (leftHead rightHead : String)
    (left right : List Atom) (notCons : leftHead ≠ "cons") (different : leftHead ≠ rightHead) :
    SpaceSemantics.matchValue caller (a leftHead left) (a rightHead right) = none := by
  have ordinary : ∀ first rest, (.symbol leftHead :: left) ≠ [.symbol "cons", first, rest] := by
    intro first rest same
    have headSame := congrArg List.head? same
    simp only [List.head?_cons, Option.some.injEq, Atom.symbol.injEq] at headSame
    exact notCons headSame
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller _ _ ordinary]
  have headMissed : SpaceSemantics.matchValue caller (.symbol leftHead) (.symbol rightHead) = none := by
    rw [SpaceSemantics.matchValue_literal (.symbol leftHead)]
    simp only [Atom.symbol.injEq, different, ite_false]
  rw [SpaceSemantics.matchValue.matchValues.eq_2, headMissed]
  rfl

private theorem match_some_mismatch (caller : Subst) (pattern value : Atom)
    (missed : SpaceSemantics.matchValue caller pattern value = none) :
    SpaceSemantics.matchValue caller (a "Some" [pattern]) (a "Some" [value]) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller _ _ (by intro first rest; simp)]
  rw [SpaceSemantics.matchValue.matchValues.eq_2,
    SpaceSemantics.matchValue_literal (.symbol "Some")]
  simp only [ite_true, bind, Option.bind]
  rw [SpaceSemantics.matchValue.matchValues.eq_2, missed]
  rfl

private theorem collection_rest_shape_mismatch (caller : Subst)
    (actualKind : CollType) (residual : List Pattern) (name : String)
    (freshActual : Subst.lookup caller "actual-kind" = none)
    (freshResidual : Subst.lookup caller "residual" = none) :
    SpaceSemantics.matchValue caller
      (a "PCollection" [v "actual-kind", v "residual", .symbol "RNone"])
      (patternValue (.collection actualKind residual (some name))) = none := by
  simp only [patternValue, encoded, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
    CettaWireAtom.encode, CettaWireAtom.encodeMany]
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller _ _ (by intro first rest; simp)]
  rw [SpaceSemantics.matchValue.matchValues.eq_2,
    SpaceSemantics.matchValue_literal (.symbol "PCollection")]
  simp only [ite_true, bind, Option.bind]
  rw [SpaceSemantics.matchValue.matchValues.eq_2, match_value_var]
  simp only [matchAtom, freshActual, bind, Option.bind]
  rw [SpaceSemantics.matchValue.matchValues.eq_2, match_value_var]
  have differentNames : ("actual-kind" == "residual") = false := by decide +kernel
  simp only [matchAtom, lookup_cons, differentNames, freshResidual,
    Bool.false_eq_true, ite_false, bind, Option.bind]
  rw [SpaceSemantics.matchValue.matchValues.eq_2,
    SpaceSemantics.matchValue_literal (.symbol "RNone")]
  simp only [reduceCtorEq, ite_false, bind, Option.bind]

private theorem collection_residual_returns (caller : Subst) (state : State)
    (kind : CollType) (explicit : List Pattern) (expression : Atom) (result : Option Pattern)
    (kindCaptured : applySubst caller (v "kind") = kindValue kind)
    (explicitCaptured : applySubst caller (v "explicit") = patternsValue explicit)
    (freshActual : Subst.lookup caller "actual-kind" = none)
    (freshResidual : Subst.lookup caller "residual" = none)
    (freshFailed : Subst.lookup caller "failed" = none)
    (freshValues : Subst.lookup caller "values" = none)
    (freshResult : Subst.lookup caller "result" = none)
    (computed : PureReturns runtime caller state expression state (patternOptionValue result)) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (collectionResidualCases.map fun row => .expression [row.1, row.2])])
      state (patternOptionValue (collectionResidualOption kind explicit result)) := by
  by_cases closed : ∃ actualKind residual, result = some (.collection actualKind residual none)
  · rcases closed with ⟨actualKind, residual, rfl⟩
    let selected := ("residual", patternsValue residual) :: ("actual-kind", kindValue actualKind) :: caller
    apply branch_returns caller selected state expression
      (patternOptionValue (some (.collection actualKind residual none))) collectionResidualCases collectionResidualBody
    · exact computed
    · simp [collectionResidualCases, patternOptionValue, encoded,
        MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, selected, freshActual, freshResidual]
    · have compared : PureReturns runtime selected state (a "==" [v "actual-kind", v "kind"]) state
          (Effects.boolean (decide (actualKind = kind))) := by
        simpa only [collection_type_encode_eq] using
          CettaWireAtom.equality_captured_returns runtime selected state
            (InferenceCettaWire.encodeCollectionType actualKind) (InferenceCettaWire.encodeCollectionType kind)
            "actual-kind" "kind"
            (by simp [selected])
            (by simpa [selected] using kindCaptured)
      unfold collectionResidualBody
      apply bool_if_returns selected state _ (decide (actualKind = kind)) _ _ _ compared
      by_cases same : actualKind = kind
      · subst actualKind
        simp only [collectionResidualOption, Option.bind_some, beq_self_eq_true, ite_true, decide_true]
        let valuesBound := ("values", patternsValue (explicit ++ residual)) :: selected
        let final := ("result", patternValue (.collection kind (explicit ++ residual) none)) :: valuesBound
        unfold collectionSpliceBody
        apply PureData.let_bindings_return
          (pairs := [(v "values", a "gslt:automata:append" [v "explicit", v "residual"]),
            (v "result", a "PCollection" [v "kind", v "values", .symbol "RNone"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := valuesBound)
          · apply append_patterns_returns selected state explicit residual "explicit" "residual"
            simp [selected, explicitCaptured]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              valuesBound, selected, freshValues]
          · apply PureData.BindingsReturn.cons (bound := final)
            · have built := PureData.template_return runtime valuesBound state
                (a "PCollection" [v "kind", v "values", .symbol "RNone"])
                (PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide) (by
                  intro code member
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with (rfl | rfl | rfl)
                  · exact .captured _
                  · exact .captured _
                  · exact .symbol _))
              have templateValue : applySubst valuesBound
                  (a "PCollection" [v "kind", v "values", .symbol "RNone"]) =
                  patternValue (.collection kind (explicit ++ residual) none) := by
                change a "PCollection" [applySubst valuesBound (v "kind"),
                  applySubst valuesBound (v "values"), .symbol "RNone"] = _
                simp [valuesBound, selected, kindCaptured, patternValue, encoded,
                  InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany]
              simpa only [templateValue] using built
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                final, valuesBound, selected, freshResult, patternValue, encoded, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · exact .nil _ _
        · simpa [final, patternOptionValue,
            MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            constructor_variables_return runtime final state "Some" ["result"] (by decide +kernel) (by decide)
      · have unequal : (actualKind == kind) = false := beq_eq_false_iff_ne.mpr same
        simp only [collectionResidualOption, Option.bind_some, unequal, Bool.false_eq_true, ite_false,
          decide_eq_false same]
        exact symbol_returns runtime selected state "None"
  · have refused : collectionResidualOption kind explicit result = none := by
      cases result with
      | none => rfl
      | some value =>
          cases value <;> try rfl
          case collection actualKind residual rest =>
            cases rest with
            | some name => rfl
            | none => exact False.elim (closed ⟨actualKind, residual, rfl⟩)
    rw [refused]
    let selected := ("failed", patternOptionValue result) :: caller
    apply branch_returns caller selected state expression (patternOptionValue result)
      collectionResidualCases (.symbol "None")
    · exact computed
    · have missed : SpaceSemantics.matchValue caller
          (a "Some" [a "PCollection" [v "actual-kind", v "residual", .symbol "RNone"]])
          (patternOptionValue result) = none := by
        cases result with
        | none =>
            simp only [a, patternOptionValue, encoded,
              MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode]
            unfold SpaceSemantics.matchValue
            split <;> simp_all
        | some value =>
            simp only [patternOptionValue, encoded, MatchAutomataBindingExecution.patternOptionTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany]
            apply match_some_mismatch
            cases value <;> simp only [InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · exact match_head_mismatch caller "PCollection" "Var" _ _ (by decide) (by decide)
            · exact match_head_mismatch caller "PCollection" "FVar" _ _ (by decide) (by decide)
            · exact match_head_mismatch caller "PCollection" "PApp" _ _ (by decide) (by decide)
            · exact match_head_mismatch caller "PCollection" "PLam" _ _ (by decide) (by decide)
            · exact match_head_mismatch caller "PCollection" "PMultiLam" _ _ (by decide) (by decide)
            · exact match_head_mismatch caller "PCollection" "PSubst" _ _ (by decide) (by decide)
            · rename_i actualKind residual rest
              cases rest with
              | none => exact False.elim (closed ⟨actualKind, residual, rfl⟩)
              | some name => simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  collection_rest_shape_mismatch caller actualKind residual name freshActual freshResidual
      simp only [collectionResidualCases, SpaceSemantics.selectCase, missed, match_value_var,
        matchAtom, freshFailed, selected]
    · exact symbol_returns runtime selected state "None"

#print axioms collection_residual_returns

private theorem collection_with_slot (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth assignment
        (.collection kind elements rest) =
      (ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth assignment 0 elements).bind
        (fun explicit => match rest with
          | none => some (.collection kind explicit none)
          | some name => collectionResidualOption kind explicit
              (ScopedRuleMatching.instantiateAt? rule spec ambient site
                (path ++ [elements.length]) depth assignment (.fvar name))) := by
  rw [ScopedRuleMatching.instantiateWith?.eq_7]
  cases rest with
  | none => rfl
  | some name =>
      simp only [collectionResidualOption, ScopedRuleMatching.instantiateAt?,
        ScopedRuleMatching.instantiateWith?.eq_1, bind, Option.bind_assoc]
      rfl

private def collectionNoneBody : Atom :=
  a "let" [v "result", a "PCollection" [v "kind", v "explicit", .symbol "RNone"], a "Some" [v "result"]]

private def collectionSomeBody : Atom :=
  a "let*" [.expression [
    .expression [v "length", a "gslt:automata:length" [v "elements"]],
    .expression [v "rest-path", a "gslt:automata:append" [v "path", a "LCons" [v "length", .symbol "LNil"]]]],
    a "case" [a "gslt:rule:scope-instantiate-slot" [v "rule", v "spec", v "ambient", v "site", v "rest-path", v "depth", v "assignment", v "name"],
      .expression (collectionResidualCases.map fun row => .expression [row.1, row.2])]]

private def collectionRestCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", collectionNoneBody), (a "RSome" [v "name"], collectionSomeBody),
    (v "invalid", .symbol "None")]

private def collectionExplicitBody : Atom :=
  a "case" [v "rest", .expression (collectionRestCases.map fun row => .expression [row.1, row.2])]

private theorem instantiate_collection_from_arguments (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (kind : CollType) (elements : List Pattern) (rest : Option String)
    (elementsReturned : PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-args-at"
        (argumentsValues operationValue rule spec ambient site path depth assignment 0 elements)) state
      (optionalValue patternsValue (ScopedRuleMatching.instantiateArgsWith? operation
        rule spec ambient site path depth assignment 0 elements))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment (.collection kind elements rest))) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment (.collection kind elements rest))) := by
  let caller := environment .instantiate
    (instantiationValues operationValue rule spec ambient site path depth assignment (.collection kind elements rest))
  let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
    ("elements", patternsValue elements) :: ("kind", kindValue kind) :: caller
  let result := ScopedRuleMatching.instantiateArgsWith? operation
    rule spec ambient site path depth assignment 0 elements
  have recursive := helper_capture .arguments selected state
    [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", number 0, v "elements"]
    (argumentsValues operationValue rule spec ambient site path depth assignment 0 elements)
    _ rfl (by simp [selected, caller, environment, Helper.names, instantiationValues, argumentsValues,
      applySubst, Subst.lookup]) elementsReturned
  apply instantiation_case_returns state operationValue rule spec ambient site path depth assignment
    (.collection kind elements rest) selected collectionBody
  · simp [instantiationCases, patternValue, encoded, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment,
      Helper.names, instantiationValues, kindValue, Subst.lookup]
  · rw [collection_with_slot]
    change PureReturns runtime selected state
      (a "case" [a "gslt:rule:scope-instantiate-args-at" [v "operation", v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", number 0, v "elements"],
        .expression ((optionalCases "explicit" collectionExplicitBody).map fun row => .expression [row.1, row.2])]) state _
    apply optional_returns selected state _ result patternsValue "explicit" collectionExplicitBody
      (fun values => patternOptionValue (values.bind fun explicit => match rest with
        | none => some (.collection kind explicit none)
        | some name => collectionResidualOption kind explicit
            (ScopedRuleMatching.instantiateAt? rule spec ambient site
              (path ++ [elements.length]) depth assignment (.fvar name))))
    · simp [selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
    · simp [selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
    · rfl
    · simpa only [Helper.head, result] using recursive
    · intro explicit _found
      let framed := ("explicit", patternsValue explicit) :: selected
      unfold collectionExplicitBody
      cases rest with
      | none =>
          simp only [Option.bind_some]
          apply branch_returns framed framed state (v "rest") (.symbol "RNone")
            collectionRestCases collectionNoneBody
          · simpa [framed, selected, caller, environment, Helper.names, instantiationValues,
              InferenceCettaWire.encodeRest, encoded, CettaWireAtom.encode] using
              variable_returns runtime framed state "rest"
          · simp [collectionRestCases, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, matchAtom, framed]
          · unfold collectionNoneBody
            rw [pattern_option_optional]
            apply some_result_returns framed state _ (patternValue (.collection kind explicit none))
            · simp [framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
            · have built := PureData.template_return runtime framed state
                (a "PCollection" [v "kind", v "explicit", .symbol "RNone"])
                (PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide) (by
                  intro code member
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with (rfl | rfl | rfl)
                  · exact .captured _
                  · exact .captured _
                  · exact .symbol _))
              simpa [patternValue, encoded, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, framed, selected, caller, kindValue,
                applySubst, applySubst.applySubstList, Subst.lookup] using built
      | some name =>
          simp only [Option.bind_some]
          let nameBound := ("name", stringValue name) :: framed
          let lengthBound := ("length", number elements.length) :: nameBound
          let restPathBound := ("rest-path", pathValue (path ++ [elements.length])) :: lengthBound
          apply branch_returns framed nameBound state (v "rest") (a "RSome" [stringValue name])
            collectionRestCases collectionSomeBody
          · simpa [framed, selected, caller, environment, Helper.names, instantiationValues,
              InferenceCettaWire.encodeRest, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              variable_returns runtime framed state "rest"
          · simp [collectionRestCases, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, nameBound,
              framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
          · unfold collectionSomeBody
            apply PureData.let_bindings_return
              (pairs := [(v "length", a "gslt:automata:length" [v "elements"]),
                (v "rest-path", a "gslt:automata:append" [v "path", a "LCons" [v "length", .symbol "LNil"]])])
              (final := restPathBound)
            · apply PureData.BindingsReturn.cons (bound := lengthBound)
              · apply length_patterns_returns nameBound state elements "elements"
                simp [nameBound, framed, selected, applySubst, Subst.lookup]
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  lengthBound, nameBound, framed, selected, caller, environment, Helper.names,
                  instantiationValues, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := restPathBound)
                · apply append_path_returns lengthBound state path elements.length (v "path")
                    (a "LCons" [v "length", .symbol "LNil"])
                    (by rfl) (by decide +kernel) (by rfl) (by decide +kernel)
                  simp [pathValue, CettaWire.encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    lengthBound, nameBound, framed, selected, caller, environment, Helper.names,
                    instantiationValues, applySubst, applySubst.applySubstList, Subst.lookup]
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    restPathBound, lengthBound, nameBound, framed, selected, caller, environment,
                    Helper.names, instantiationValues, Subst.lookup]
                · exact .nil _ _
            · apply collection_residual_returns restPathBound state kind explicit
                (a "gslt:rule:scope-instantiate-slot" [v "rule", v "spec", v "ambient", v "site", v "rest-path", v "depth", v "assignment", v "name"])
                (ScopedRuleMatching.instantiateAt? rule spec ambient site
                  (path ++ [elements.length]) depth assignment (.fvar name))
              · simp [restPathBound, lengthBound, nameBound, framed, selected, applySubst, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, applySubst, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
              · simp [restPathBound, lengthBound, nameBound, framed, selected, caller, environment, Helper.names, instantiationValues, Subst.lookup]
              · simpa only [Helper.head] using helper_capture .slot restPathBound state
                  [v "rule", v "spec", v "ambient", v "site", v "rest-path", v "depth", v "assignment", v "name"]
                  [ruleValue rule, specValue spec, number ambient, siteValue site, pathValue (path ++ [elements.length]),
                    number depth, assignmentValue assignment, stringValue name] _ rfl
                  (by simp [restPathBound, lengthBound, nameBound, framed, selected, caller,
                    environment, Helper.names, instantiationValues, applySubst, Subst.lookup])
                  (slot_returns state rule spec ambient site (path ++ [elements.length]) depth assignment name)

#print axioms instantiate_collection_from_arguments

theorem instantiate_with_returns (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern)
    (operationReturned : ∀ replacement body,
      PureReturns runtime [] state
        (a "gslt:rule:scope-binder-operation" [operationValue, patternValue replacement, patternValue body]) state
        (patternOptionValue (some (operation replacement body)))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues operationValue rule spec ambient site path depth assignment pattern)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith? operation
        rule spec ambient site path depth assignment pattern)) := by
  induction pattern using Pattern.inductionOn generalizing path depth with
  | hbvar index => exact instantiate_bound_returns state operationValue operation rule spec ambient site path depth assignment index
  | hfvar name => exact instantiate_variable_returns state operationValue operation rule spec ambient site path depth assignment name
  | happly head children ih =>
      apply instantiate_application_from_arguments state operationValue operation rule spec ambient site path depth assignment head children
      apply arguments_from_elements
      intro pattern member childPath
      exact ih pattern member childPath depth
  | hlambda binder body ih =>
      exact instantiate_lambda_from_body state operationValue operation rule spec ambient site path depth assignment binder body
        (ih (path ++ [0]) (depth + 1))
  | hmultiLambda arity binders body ih =>
      exact instantiate_multiLambda_from_body state operationValue operation rule spec ambient site path depth assignment arity binders body
        (ih (path ++ [0]) (depth + arity))
  | hsubst body replacement ihBody ihReplacement =>
      exact instantiate_substitution_from_children state operationValue operation rule spec ambient site path depth assignment body replacement
        (ihBody (path ++ [0]) (depth + 1)) (ihReplacement (path ++ [1]) depth) operationReturned
  | hcollection kind elements rest ih =>
      apply instantiate_collection_from_arguments state operationValue operation rule spec ambient site path depth assignment kind elements rest
      apply arguments_from_elements
      intro pattern member childPath
      exact ih pattern member childPath depth

theorem instantiate_ordinary_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues (.symbol "None") rule spec ambient site path depth assignment pattern)) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment pattern)) :=
  instantiate_with_returns state (.symbol "None") Substitution.instantiateBVar rule spec ambient site path depth assignment pattern
    (fun replacement body => ordinary_binder_returns state replacement body)

theorem instantiate_ordinary_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      instantiationValues (.symbol "None") rule spec ambient site path depth assignment pattern) :
    PureReturns runtime caller state (a "gslt:rule:scope-instantiate-at" arguments) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment pattern)) := by
  simpa only [Helper.head] using helper_capture .instantiate caller state arguments _ _ rfl captured
    (instantiate_ordinary_returns state rule spec ambient site path depth assignment pattern)

theorem instantiate_ordinary_completed_iff (caller : Subst) (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      instantiationValues (.symbol "None") rule spec ambient site path depth assignment pattern)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run runtime fuel {state, control := .evaluate caller (a "gslt:rule:scope-instantiate-at" arguments)} =
      .complete after answers input output) ↔
      after = state ∧ answers = [patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment pattern)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime caller state state _ _
    (instantiate_ordinary_captured_returns caller state rule spec ambient site path depth assignment pattern arguments captured)
    after answers input output

#print axioms instantiate_with_returns
#print axioms instantiate_ordinary_returns
#print axioms instantiate_ordinary_captured_returns
#print axioms instantiate_ordinary_completed_iff

private def reductBody : Atom :=
  a "gslt:rule:scope-instantiate-at" [v "operation", v "rule", v "spec", v "ambient",
    .symbol "RuleRight", .symbol "LNil", number 0, v "assignment", v "right"]

private def reductCases : SpaceSemantics.Cases :=
  [(a "ScopedRewriteRuleV1" [v "name", v "context", v "premises", v "left", v "right", v "bindings"], reductBody),
    (v "invalid", .symbol "None")]

private theorem reduct_shape : (equation .reduct).body =
    a "case" [v "rule", .expression (reductCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem reduct_with_returns (state : State) (operationValue : Atom)
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment)
    (operationReturned : ∀ replacement body,
      PureReturns runtime [] state
        (a "gslt:rule:scope-binder-operation" [operationValue, patternValue replacement, patternValue body]) state
        (patternOptionValue (some (operation replacement body)))) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-reduct" [operationValue, ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) state
      (patternOptionValue (ScopedRuleMatching.reductWith? operation rule spec ambient assignment)) := by
  let values := [operationValue, ruleValue rule, specValue spec, number ambient, assignmentValue assignment]
  let caller := environment .reduct values
  let selected := ("bindings", encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)) ::
    ("right", patternValue rule.right) :: ("left", patternValue rule.left) ::
    ("premises", encoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)) ::
    ("context", encoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)) ::
    ("name", stringValue rule.name) :: caller
  apply helper_call .reduct [] state values values _ rfl (captured_closed _)
  rw [reduct_shape]
  apply branch_returns caller selected state (v "rule") (ruleValue rule) reductCases reductBody
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "rule"
  · simp [reductCases, ruleValue, encoded, InferenceCettaWire.AuthoredRule.rewriteTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      selected, caller, values, environment, Helper.names, stringValue, patternValue, Subst.lookup]
  · simpa only [Helper.head, reductBody, ScopedRuleMatching.reductWith?] using
      helper_capture .instantiate selected state
        [v "operation", v "rule", v "spec", v "ambient", .symbol "RuleRight", .symbol "LNil", number 0, v "assignment", v "right"]
        (instantiationValues operationValue rule spec ambient .right [] 0 assignment rule.right) _ rfl
        (by simp [selected, caller, values, environment, Helper.names, instantiationValues,
          siteValue, pathValue, encodeList, encoded, InferenceCettaWire.AuthoredRule.siteTerm,
          CettaWireAtom.encode, applySubst, Subst.lookup])
        (instantiate_with_returns state operationValue operation rule spec ambient .right [] 0 assignment rule.right operationReturned)

theorem reduct_ordinary_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-reduct" [.symbol "None", ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) state
      (patternOptionValue (ScopedRuleMatching.reduct? rule spec ambient assignment)) :=
  reduct_with_returns state (.symbol "None") Substitution.instantiateBVar rule spec ambient assignment
    (fun replacement body => ordinary_binder_returns state replacement body)

theorem reduct_ordinary_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [.symbol "None", ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns runtime caller state (a "gslt:rule:scope-reduct" arguments) state
      (patternOptionValue (ScopedRuleMatching.reduct? rule spec ambient assignment)) := by
  simpa only [Helper.head] using helper_capture .reduct caller state arguments _ _ rfl captured
    (reduct_ordinary_returns state rule spec ambient assignment)


/-- Full occurrence-aware traversal with the selected declaration, including
nested binders, explicit substitutions and ordered residual collections. -/
theorem instantiate_selected_returns (state : State) (declaration : ReflectivePresentationDecl)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-instantiate-at"
        (instantiationValues (operationValue (some declaration)) rule spec ambient site path depth assignment pattern)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith?
        (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient site path depth assignment pattern)) :=
  instantiate_with_returns state (operationValue (some declaration))
    (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient site path depth assignment pattern
    (fun replacement body => selected_binder_returns state declaration replacement body)

theorem instantiate_selected_captured_returns (caller : Subst) (state : State)
    (declaration : ReflectivePresentationDecl) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      instantiationValues (operationValue (some declaration)) rule spec ambient site path depth assignment pattern) :
    PureReturns runtime caller state (a "gslt:rule:scope-instantiate-at" arguments) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith?
        (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient site path depth assignment pattern)) := by
  simpa only [Helper.head] using helper_capture .instantiate caller state arguments _ _ rfl captured
    (instantiate_selected_returns state declaration rule spec ambient site path depth assignment pattern)

theorem reduct_selected_returns (state : State) (declaration : ReflectivePresentationDecl)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) :
    PureReturns runtime [] state
      (a "gslt:rule:scope-reduct"
        [operationValue (some declaration), ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) state
      (patternOptionValue (ScopedRuleMatching.reductWith?
        (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient assignment)) :=
  reduct_with_returns state (operationValue (some declaration))
    (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient assignment
    (fun replacement body => selected_binder_returns state declaration replacement body)

theorem reduct_selected_captured_returns (caller : Subst) (state : State)
    (declaration : ReflectivePresentationDecl) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [operationValue (some declaration), ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns runtime caller state (a "gslt:rule:scope-reduct" arguments) state
      (patternOptionValue (ScopedRuleMatching.reductWith?
        (ScopedRuleInstantiation.reflectiveOperation declaration) rule spec ambient assignment)) := by
  simpa only [Helper.head] using helper_capture .reduct caller state arguments _ _ rfl captured
    (reduct_selected_returns state declaration rule spec ambient assignment)

/-- The original rule/profile lookup determines which actual operation is used. -/
theorem instantiate_profile_captured_returns (caller : Subst) (state : State)
    (profile : ReflectionProfile) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      instantiationValues (operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule))
        rule spec ambient site path depth assignment pattern) :
    PureReturns runtime caller state (a "gslt:rule:scope-instantiate-at" arguments) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient site path depth assignment pattern)) := by
  cases chosen : ReflectiveSubstitution.substitutionPresentationForRule? profile rule with
  | none =>
    simpa only [ScopedReflectiveExecution.binderOperation, chosen, ScopedRuleInstantiation.ordinary_specialization] using
      instantiate_ordinary_captured_returns caller state rule spec ambient site path depth assignment pattern arguments
        (by simpa only [chosen, operationValue] using captured)
  | some declaration =>
    simpa only [ScopedReflectiveExecution.binderOperation, chosen] using
      instantiate_selected_captured_returns caller state declaration rule spec ambient site path depth assignment pattern arguments
        (by simpa only [chosen] using captured)

theorem reduct_profile_captured_returns (caller : Subst) (state : State)
    (profile : ReflectionProfile) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule),
       ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns runtime caller state (a "gslt:rule:scope-reduct" arguments) state
      (patternOptionValue (ScopedRuleMatching.reductWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment)) := by
  cases chosen : ReflectiveSubstitution.substitutionPresentationForRule? profile rule with
  | none =>
    simpa only [ScopedReflectiveExecution.binderOperation, chosen, ScopedRuleMatching.reductWith?_ordinary] using
      reduct_ordinary_captured_returns caller state rule spec ambient assignment arguments
        (by simpa only [chosen, operationValue] using captured)
  | some declaration =>
    simpa only [ScopedReflectiveExecution.binderOperation, chosen] using
      reduct_selected_captured_returns caller state declaration rule spec ambient assignment arguments
        (by simpa only [chosen] using captured)

#print axioms instantiate_selected_returns
#print axioms instantiate_selected_captured_returns
#print axioms reduct_selected_returns
#print axioms reduct_selected_captured_returns
#print axioms instantiate_profile_captured_returns
#print axioms reduct_profile_captured_returns

def executionHeadNames : List String :=
  ["gslt:rule:scope-binder-operation", "gslt:rule:scope-instantiate-slot", "gslt:rule:scope-instantiate-at",
   "gslt:rule:scope-instantiate-args-at", "gslt:rule:scope-reduct", "case", "None", "let",
   "gslt:rule:instantiate-bvar-at", "Some", "gslt:automata:binding", "gslt:rule:scope-metadata-arguments",
   "gslt:rule:scope-instantiate-value", "FVar", "Var", "PApp", "PLam", "let*", "gslt:automata:append",
   "LCons", "+", "PMultiLam", "PSubst", "PCollection", "RNone", "RSome", "gslt:automata:length", "if", "==",
   "LNil", "ScopedRewriteRuleV1", "Binding", "<", "gslt:rule:lift-bvars", "-",
   "gslt:rule:instantiate-bvar-list-at", "ContextualValue", "gslt:rule:scope-well-scoped",
   "gslt:rule:scope-well-scoped-list", "OccurrenceAssignment", "gslt:rule:scope-substitute",
   "gslt:rule:scope-metadata-dependencies", "gslt:rule:scope-metadata-occurrence-declared", "RuleOccurrence",
   "RuleBindingSpec", "gslt:rule:scope-metadata-occurrence-rows", ">=", "gslt:rule:lift-bvars-list",
   "gslt:rule:scope-assignment", "gslt:rule:scope-substitute-list", "gslt:rule:scope-metadata-dependency-rows",
   "RuleDependency", "gslt:rule:scope-metadata-site-pattern", "gslt:rule:scope-metadata-occurrence-name",
   "gslt:rule:row-at", "RecoveryAssignment", "gslt:rule:scope-index", "RuleLeft", "RuleRight", "RulePremise",
   "gslt:rule:scope-metadata-site-premise", "gslt:rule:scope-metadata-premise-pattern",
   "gslt:rule:scope-metadata-quantified-body", "Freshness", "Congruence", "ScopedStep", "RelationQuery", "ForAll"] ++
    ScopedReflectiveBinderOperationExecution.executionHeadNames

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem runtime_closed : ProgramClosed executionHeads runtime := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : runtime.equations.all (fun equation =>
        !executionHeads equation.head || codeWithin executionHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem variable_call_supported (head : String) (names : List String)
    (headSupported : executionHeads head = true) (notEval : head ≠ "eval") :
    codeWithin executionHeads (a head (names.map Atom.var)) = true := by
  have notUnique : head ≠ "unique" := by
    intro same
    subst head
    have excluded : executionHeads "unique" = false := by decide +kernel
    rw [excluded] at headSupported
    cases headSupported
  have variablesSupported : atomsWithin executionHeads (names.map Atom.var) = true := by
    induction names with
    | nil => rfl
    | cons name names ih => simpa only [List.map_cons, atomsWithin, codeWithin, Bool.true_and] using ih
  simp only [codeWithin, expressionHeadWithin, headSupported,
    atomsWithin, Bool.true_and, variablesSupported, bne_iff_ne.mpr notUnique, Bool.true_or, Bool.and_true]
  exact bne_iff_ne.mpr notEval

theorem instantiate_ordinary_variables_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      instantiationValues (.symbol "None") rule spec ambient site path depth assignment pattern) :
    PureReturns target caller state (a "gslt:rule:scope-instantiate-at" (names.map Atom.var)) state
      (patternOptionValue (ScopedRuleMatching.instantiateAt?
        rule spec ambient site path depth assignment pattern)) :=
  path_of_closed_agreement runtime_closed agreement
    ⟨variable_call_supported "gslt:rule:scope-instantiate-at" names (by decide +kernel) (by decide), rfl⟩
    (instantiate_ordinary_captured_returns caller state rule spec ambient site path depth assignment pattern _ captured)

theorem reduct_ordinary_variables_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      [.symbol "None", ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns target caller state (a "gslt:rule:scope-reduct" (names.map Atom.var)) state
      (patternOptionValue (ScopedRuleMatching.reduct? rule spec ambient assignment)) :=
  path_of_closed_agreement runtime_closed agreement
    ⟨variable_call_supported "gslt:rule:scope-reduct" names (by decide +kernel) (by decide), rfl⟩
    (reduct_ordinary_captured_returns caller state rule spec ambient assignment _ captured)


/-- The complete source-selected traversal is retained inside a larger authored
program when its actual reachable dispatch, demand and bodies agree. -/
theorem instantiate_profile_variables_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (profile : ReflectionProfile)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      instantiationValues (operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule))
        rule spec ambient site path depth assignment pattern) :
    PureReturns target caller state (a "gslt:rule:scope-instantiate-at" (names.map Atom.var)) state
      (patternOptionValue (ScopedRuleMatching.instantiateWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient site path depth assignment pattern)) :=
  path_of_closed_agreement runtime_closed agreement
    ⟨variable_call_supported "gslt:rule:scope-instantiate-at" names (by decide +kernel) (by decide), rfl⟩
    (instantiate_profile_captured_returns caller state profile rule spec ambient site path depth assignment pattern _ captured)

theorem reduct_profile_variables_returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (profile : ReflectionProfile)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      [operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule),
       ruleValue rule, specValue spec, number ambient, assignmentValue assignment]) :
    PureReturns target caller state (a "gslt:rule:scope-reduct" (names.map Atom.var)) state
      (patternOptionValue (ScopedRuleMatching.reductWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment)) :=
  path_of_closed_agreement runtime_closed agreement
    ⟨variable_call_supported "gslt:rule:scope-reduct" names (by decide +kernel) (by decide), rfl⟩
    (reduct_profile_captured_returns caller state profile rule spec ambient assignment _ captured)

theorem instantiate_profile_variables_completed_iff_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (profile : ReflectionProfile)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      instantiationValues (operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule))
        rule spec ambient site path depth assignment pattern)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run target fuel
      {state, control := .evaluate caller (a "gslt:rule:scope-instantiate-at" (names.map Atom.var))} =
        .complete after answers input output) ↔
      after = state ∧ answers = [patternOptionValue (ScopedRuleMatching.instantiateWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient site path depth assignment pattern)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (instantiate_profile_variables_returns_in_extension target agreement caller state profile rule spec ambient
      site path depth assignment pattern names captured) after answers input output

theorem reduct_profile_variables_completed_iff_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    (caller : Subst) (state : State) (profile : ReflectionProfile)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) (names : List String)
    (captured : (names.map Atom.var).map (applySubst caller) =
      [operationValue (ReflectiveSubstitution.substitutionPresentationForRule? profile rule),
       ruleValue rule, specValue spec, number ambient, assignmentValue assignment])
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run target fuel {state, control := .evaluate caller (a "gslt:rule:scope-reduct" (names.map Atom.var))} =
        .complete after answers input output) ↔
      after = state ∧ answers = [patternOptionValue (ScopedRuleMatching.reductWith?
        (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (reduct_profile_variables_returns_in_extension target agreement caller state profile rule spec ambient
      assignment names captured) after answers input output

#print axioms instantiate_profile_variables_returns_in_extension
#print axioms reduct_profile_variables_returns_in_extension
#print axioms instantiate_profile_variables_completed_iff_in_extension
#print axioms reduct_profile_variables_completed_iff_in_extension

#print axioms reduct_with_returns
#print axioms reduct_ordinary_returns
#print axioms reduct_ordinary_captured_returns
#print axioms runtime_closed
#print axioms instantiate_ordinary_variables_returns_in_extension
#print axioms reduct_ordinary_variables_returns_in_extension

/-- The selected scoped RHS operations retain their dispatch, argument demand
and bodies in the complete conditional machine. -/
theorem scoped_machine_agreement : ProgramAgreementOn executionHeads runtime
    RuleExecutionProgram.scopedMachineProgram := by
  apply programAgreementOn_of_retained_rows
  · kernel_reflexivity
  · kernel_reflexivity

#print axioms scoped_machine_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedInstantiationExecution
