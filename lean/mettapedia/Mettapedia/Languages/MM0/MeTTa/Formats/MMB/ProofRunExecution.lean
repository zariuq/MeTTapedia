import Mettapedia.Languages.MeTTa.PeTTa.PureData
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBExecution
import Mettapedia.Languages.MM0.MeTTa.Kernel.Hypothesis
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Executing binary reference, save and hypothesis proof commands

This module follows the quoted, unchanged binary frontend. Its supported
commands preserve expression allocation identities and actual witness atoms;
its finite-run theorem includes refused commands and the untouched suffix.
Theorem application, term construction, dummy allocation, conversion
continuations and assertion resolution require further execution proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBProofRunExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst applySubst_nil matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)

abbrev program := MMBExecution.program

/-- The original source constructor, including its complete saved-proof state. -/
def stateValue (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) : Atom :=
  .expression [.symbol "MM0:MMBPState", natural next, natural arity, natural count,
    listValue stack, listValue heap, listValue dummies, listValue hypotheses, listValue saved]

def expressionValue (allocation : Nat) (expression node : Atom) : Atom :=
  .expression [.symbol "MM0:MMBExpression", natural allocation, expression, node]

def provedValue (witness target : Atom) : Atom :=
  .expression [.symbol "MM0:MMBProved", witness, target]

/-- Only these two original entry constructors are directly reusable.
Conversion entries have a different continuation-consuming reference path. -/
inductive ReusableEntry : Atom → Prop where
  | expression (allocation : Nat) (expression node : Atom) :
      ReusableEntry (expressionValue allocation expression node)
  | proved (witness target : Atom) : ReusableEntry (provedValue witness target)

private def checkerHead (head : String) : Bool :=
  MMUResolution.checkerHead head && !(head.startsWith "mm0:mmb:")

private theorem checker_closed : ProgramClosed checkerHead MeTTa.program := by
  constructor
  · decide
  · intro equation member supported
    have allBodies : MeTTa.program.equations.all (fun equation =>
        !checkerHead equation.head || codeWithin checkerHead equation.body) = true := by
      decide +kernel
    have body := List.all_eq_true.mp allBodies equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using body

private theorem checker_agreement :
    ProgramAgreementOn checkerHead MeTTa.program program := by
  have expanded : program = MeTTa.program.append
      ((TextualExecution.textualSource.program.append MMUResolution.resolverSource.program).append
        MMBExecution.binarySource.program) := by
    simp [MMBExecution.program, MMUResolution.program, TextualExecution.program,
      SpaceSemantics.Program.append, List.append_assoc]
  rw [expanded]
  apply appended_program_agreement
  · intro equation member
    have fresh : ((TextualExecution.textualSource.program.append
        MMUResolution.resolverSource.program).append MMBExecution.binarySource.program).equations.all
        (fun equation => !checkerHead equation.head) = true := by decide +kernel
    have checked := List.all_eq_true.mp fresh equation member
    cases result : checkerHead _ <;> simp_all
  · intro head types member
    have fresh : ((TextualExecution.textualSource.program.append
        MMUResolution.resolverSource.program).append MMBExecution.binarySource.program).declarations.all
        (fun declaration => match declaration with
          | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: _)] =>
              !checkerHead name
          | _ => true) = true := by decide +kernel
    have checked := List.all_eq_true.mp fresh _ member
    cases result : checkerHead _ <;> simp_all

/-- Loading the binary frontend preserves actual original checker paths. -/
theorem checker_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin checkerHead code = true)
    (returned : PureReturns MeTTa.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement checker_closed checker_agreement ⟨supported, rfl⟩ returned

private theorem arguments_return (bindings : Subst) (state : State) (arguments values : List Atom)
    (index : Nat)
    (computed : ∀ argument ∈ arguments,
      PureReturns program bindings state argument state (applySubst bindings argument)) :
    (theory program).MultiStep
      { state, control := .arguments bindings .data arguments values index }
      (finished state [.expression (values ++ arguments.map (applySubst bindings))] [] []) := by
  induction arguments generalizing values index with
  | nil => simpa using data_arguments_values_return program bindings state values index
  | cons first rest ih =>
      apply evaluated_argument_returns program bindings state state state .data first
        (applySubst bindings first) _ rest values index rfl (computed first (by simp))
      simpa [List.append_assoc] using ih (values ++ [applySubst bindings first]) (index + 1)
        (fun argument member => computed argument (by simp [member]))

private theorem substituted_list (bindings : Subst) (arguments : List Atom) :
    applySubst.applySubstList bindings arguments = arguments.map (applySubst bindings) := by
  induction arguments with
  | nil => rfl
  | cons first rest ih => simp only [applySubst.applySubstList, List.map_cons, ih]

private theorem constructor_returns (bindings : Subst) (state : State) (head : String)
    (arguments : List Atom)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (computed : ∀ argument ∈ arguments,
      PureReturns program bindings state argument state (applySubst bindings argument)) :
    PureReturns program bindings state (.expression (.symbol head :: arguments)) state
      (applySubst bindings (.expression (.symbol head :: arguments))) := by
  apply data_call_returns program bindings state state head arguments _ inert _ ordinary
  apply evaluated_argument_returns program bindings state state state .data (.symbol head)
    (.symbol head) _ arguments [] 0 rfl (symbol_returns program bindings state head)
  simpa [applySubst, substituted_list] using
    arguments_return bindings state arguments [.symbol head] 1 computed

private theorem empty_data_returns (bindings : Subst) (state : State) :
    PureReturns program bindings state (.expression []) state (.expression []) :=
  .step (step_transition rfl) (.step (step_transition rfl) (.refl _))

local macro "mmb_data" : tactic => `(tactic|
  repeat' first
  | exact variable_returns program _ _ _
  | exact symbol_returns program _ _ _
  | exact grounded_returns program _ _ _
  | exact empty_data_returns _ _
  | apply And.intro
  | exact True.intro
  | (intro x impossible; cases impossible)
  | (apply constructor_returns _ _ _ _ (by decide +kernel) (by decide)
     simp only [List.forall_mem_cons]))

private theorem cons_returns (bindings : Subst) (state : State) (first : Atom) (rest : List Atom)
    (firstCode restCode : Atom)
    (firstCaptured : applySubst bindings firstCode = first)
    (restCaptured : applySubst bindings restCode = listValue rest) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:list-cons", firstCode, restCode]) state
      (listValue (first :: rest)) := by
  let prior : Subst := [("tail", listValue rest), ("head", first)]
  have original := checker_returns (by decide +kernel)
    (ListAccess.cons_captured_returns prior state first rest "head" "tail" rfl rfl)
  apply captured_call_returns program prior bindings state state "mm0:list-cons"
    [.var "head", .var "tail"] [firstCode, restCode] _
    (by decide +kernel) (by decide) _ _ _ original
  · intro offset argument found
    have bounded : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    left
    have positions : offset = 0 ∨ offset = 1 := by omega
    rcases positions with rfl | rfl <;> decide +kernel
  · intro offset argument found
    have bounded : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    left
    have positions : offset = 0 ∨ offset = 1 := by omega
    rcases positions with rfl | rfl <;> decide +kernel
  · simp [prior, firstCaptured, restCaptured, applySubst, Subst.lookup]

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩

private def snocEquation := sourceEquation "mm0:mmb:snoc"
private def snocEnvironment (items : List Atom) (value : Atom) : Subst :=
  [("value", value), ("items", listValue items)]

private theorem snoc_unique : program.equations.filter (·.head == "mm0:mmb:snoc") =
    [snocEquation] := by decide +kernel
private theorem snoc_formals : snocEquation.arguments = [.var "items", .var "value"] := by decide
private theorem snoc_shape : snocEquation.body =
    .expression [.symbol "let", .var "last", .expression [.symbol "MM0:L", .expression [.var "value"]],
      .expression [.symbol "mm0:list-append", .var "items", .var "last"]] := by decide
private theorem snoc_clause (items : List Atom) (value : Atom) :
    clauses program "mm0:mmb:snoc" [listValue items, value] =
      [.evaluate (snocEnvironment items value) snocEquation.body] := by
  rw [clauses_use_only_the_named_equations, snoc_unique]
  simp [snoc_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, snocEnvironment]

private theorem snoc_body_returns (state : State) (items : List Atom) (value : Atom) :
    PureReturns program (snocEnvironment items value) state snocEquation.body state
      (listValue (items ++ [value])) := by
  let bindings := snocEnvironment items value
  let bound := ("last", listValue [value]) :: bindings
  rw [snoc_shape]
  apply let_returns program bindings bound state state state (.var "last") _ _ (listValue [value]) _
  · apply unary_constructor_of_returns program bindings state state "MM0:L" _ _
      (by decide) (by decide)
    simpa [bindings, snocEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["value"]
  · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, snocEnvironment, Subst.lookup]
  · exact checker_returns (by decide +kernel)
      (ListAccess.append_captured_returns bound state items [value] "items" "last" rfl rfl)

theorem snoc_returns (bindings : Subst) (state : State) (items : List Atom) (value : Atom)
    (itemsName valueName : String)
    (capturedItems : applySubst bindings (.var itemsName) = listValue items)
    (capturedValue : applySubst bindings (.var valueName) = value) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:snoc", .var itemsName, .var valueName]) state
      (listValue (items ++ [value])) := by
  apply authored_variable_call_returns program bindings (snocEnvironment items value) state state
    "mm0:mmb:snoc" [itemsName, valueName] snocEquation.body _
    (by decide) (by decide) (by decide) _ (snoc_body_returns state items value) (by decide)
  simpa [capturedItems, capturedValue] using snoc_clause items value

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def referenceEquation := sourceEquation "mm0:mmb:proof-reference"
private def referenceCases := casesOf referenceEquation.body
private def referenceSome := (referenceCases[1]'(by decide)).2
private def referenceTestCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"],
      boolean true),
   (.expression [.symbol "MM0:MMBProved", .var "witness", .var "target"], boolean true),
   (.var "bad", boolean false)]

private def stateEnvironment (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) : Subst :=
  [("saved", listValue saved), ("hyps", listValue hypotheses), ("dummies", listValue dummies),
    ("heap", listValue heap), ("stack", .expression stack), ("count", natural count),
    ("arity", natural arity), ("next", natural next)]

private def referenceEnvironment (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) : Subst :=
  ("index", natural index) :: stateEnvironment next arity count stack heap dummies hypotheses saved

private theorem reference_unique : program.equations.filter (·.head == "mm0:mmb:proof-reference") =
    [referenceEquation] := by decide +kernel
private theorem reference_formals : referenceEquation.arguments =
    [.expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
      .expression [.symbol "MM0:L", .var "stack"], .var "heap", .var "dummies", .var "hyps", .var "saved"],
      .var "index"] := by decide
private theorem reference_shape : referenceEquation.body =
    .expression [.symbol "case", .expression [.symbol "mm0:data-at", .var "heap", .var "index"],
      .expression (referenceCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem reference_some_shape : referenceSome =
    .expression [.symbol "if", .expression [.symbol "case", .var "entry",
      .expression (referenceTestCases.map fun row => .expression [row.1, row.2])],
      .expression [.symbol "let", .var "pushed",
        .expression [.symbol "mm0:list-cons", .var "entry", .expression [.symbol "MM0:L", .var "stack"]],
        .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity",
          .var "count", .var "pushed", .var "heap", .var "dummies", .var "hyps", .var "saved"]]],
      .symbol "None"] := by decide

private theorem reference_clause (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) :
    clauses program "mm0:mmb:proof-reference"
      [stateValue next arity count stack heap dummies hypotheses saved, natural index] =
      [.evaluate (referenceEnvironment next arity count stack heap dummies hypotheses saved index)
        referenceEquation.body] := by
  rw [clauses_use_only_the_named_equations, reference_unique]
  simp [reference_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, stateValue, listValue, referenceEnvironment, stateEnvironment]

private theorem reference_test_returns (bindings : Subst) (state : State) (entry : Atom)
    (name : String) (captured : applySubst bindings (.var name) = entry)
    (fresh : ∀ field ∈ ["id", "expression", "node", "witness", "target", "bad"],
      Subst.lookup bindings field = none)
    (reusable : ReusableEntry entry) :
    PureReturns program bindings state
      (.expression [.symbol "case", .var name,
        .expression (referenceTestCases.map fun row => .expression [row.1, row.2])]) state
      (boolean true) := by
  simp only [Subst.lookup] at fresh
  cases reusable with
  | expression allocation expression node =>
      let bound := ("node", node) :: ("expression", expression) :: ("id", natural allocation) :: bindings
      apply case_returns program bindings bound state state state (.var name) _ (boolean true) _ _
        referenceTestCases (read_cases_encoded referenceTestCases)
      · simpa only [captured] using variable_returns program bindings state name
      · simp [referenceTestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, expressionValue, matchAtom, Subst.lookup,
          bound, fresh "id" (by simp), fresh "expression" (by simp),
          fresh "node" (by simp)]
      · exact grounded_returns program bound state (.bool true)
  | proved witness target =>
      let bound := ("target", target) :: ("witness", witness) :: bindings
      apply case_returns program bindings bound state state state (.var name) _ (boolean true) _ _
        referenceTestCases (read_cases_encoded referenceTestCases)
      · simpa only [captured] using variable_returns program bindings state name
      · simp [referenceTestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, provedValue, matchAtom, Subst.lookup, bound,
          fresh "witness" (by simp), fresh "target" (by simp)]
      · exact grounded_returns program bound state (.bool true)

private theorem reference_some_returns (state : State) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) (entry : Atom)
    (reusable : ReusableEntry entry) :
    PureReturns program (("entry", entry) ::
      referenceEnvironment next arity count stack heap dummies hypotheses saved index)
      state referenceSome state
      (optionValue (some (stateValue next arity count (entry :: stack) heap dummies hypotheses saved))) := by
  let bindings := ("entry", entry) ::
    referenceEnvironment next arity count stack heap dummies hypotheses saved index
  let bound := ("pushed", listValue (entry :: stack)) :: bindings
  rw [reference_some_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ _
  · apply reference_test_returns bindings state entry "entry" rfl _ reusable
    intro field member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [bindings, referenceEnvironment, stateEnvironment, Subst.lookup]
  · simp only [boolean, beq_self_eq_true, ↓reduceIte]
    apply let_returns program bindings bound state state state (.var "pushed") _ _
      (listValue (entry :: stack)) _
    · apply cons_returns bindings state entry stack (.var "entry")
        (.expression [.symbol "MM0:L", .var "stack"]) rfl
      simp [bindings, referenceEnvironment, stateEnvironment, applySubst,
        applySubst.applySubstList, Subst.lookup, listValue]
    · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, referenceEnvironment,
        stateEnvironment, Subst.lookup]
    · apply unary_constructor_of_returns program bound state state "Some" _ _ (by decide +kernel) (by decide)
      simpa [bound, bindings, referenceEnvironment, stateEnvironment, applySubst,
        applySubst.applySubstList, Subst.lookup, optionValue, stateValue] using
        constructor_variables_return program bound state "MM0:MMBPState"
          ["next", "arity", "count", "pushed", "heap", "dummies", "hyps", "saved"]
          (by decide +kernel) (by decide)

private def referenceConversion := (referenceCases[0]'(by decide)).2
private theorem reference_cases_shape : referenceCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBConversion", .var "witness",
       .expression [.symbol "MM0:MMBExpression", .var "leftId", .var "left", .var "leftNode"],
       .expression [.symbol "MM0:MMBExpression", .var "rightId", .var "right", .var "rightNode"]]],
       referenceConversion),
     (.expression [.symbol "Some", .var "entry"], referenceSome),
     (.var "bad", .symbol "None")] := by decide

private theorem reference_body_returns (state : State) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) (entry : Atom)
    (found : heap[index]? = some entry) (reusable : ReusableEntry entry) :
    PureReturns program (referenceEnvironment next arity count stack heap dummies hypotheses saved index)
      state referenceEquation.body state
      (optionValue (some (stateValue next arity count (entry :: stack) heap dummies hypotheses saved))) := by
  let bindings := referenceEnvironment next arity count stack heap dummies hypotheses saved index
  let bound := ("entry", entry) :: bindings
  rw [reference_shape]
  apply case_returns program bindings bound state state state _ (optionValue (some entry)) referenceSome
    _ _ referenceCases (read_cases_encoded referenceCases)
  · simpa only [found] using checker_returns (by decide +kernel)
      (ListAccess.data_at_list_returns bindings state heap index "heap" "index" rfl rfl)
  · rw [reference_cases_shape]
    cases reusable with
    | expression allocation expression node =>
        simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, optionValue, expressionValue, bound, bindings,
          referenceEnvironment, stateEnvironment]
    | proved witness target =>
        simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, optionValue, provedValue, bound, bindings,
          referenceEnvironment, stateEnvironment]
  · exact reference_some_returns state next arity count stack heap dummies hypotheses saved index entry reusable

/-- A reference returns the existing entry, preserving all allocation and witness data. -/
theorem reference_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) (entry : Atom)
    (stateName indexName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      stateValue next arity count stack heap dummies hypotheses saved)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (found : heap[index]? = some entry) (reusable : ReusableEntry entry) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-reference", .var stateName, .var indexName]) state
      (optionValue (some (stateValue next arity count (entry :: stack) heap dummies hypotheses saved))) := by
  apply authored_variable_call_returns program bindings
    (referenceEnvironment next arity count stack heap dummies hypotheses saved index) state state
    "mm0:mmb:proof-reference" [stateName, indexName] referenceEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (reference_body_returns state next arity count stack heap dummies hypotheses saved index entry found reusable)
    (by decide)
  simpa [stateCaptured, indexCaptured] using reference_clause next arity count stack heap dummies hypotheses saved index

private theorem reference_missing_body_returns (state : State) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat) (missing : heap[index]? = none) :
    PureReturns program (referenceEnvironment next arity count stack heap dummies hypotheses saved index)
      state referenceEquation.body state (.symbol "None") := by
  let bindings := referenceEnvironment next arity count stack heap dummies hypotheses saved index
  let bound := ("bad", .symbol "None") :: bindings
  rw [reference_shape]
  apply case_returns program bindings bound state state state _ (.symbol "None") (.symbol "None")
    _ _ referenceCases (read_cases_encoded referenceCases)
  · simpa only [missing, optionValue] using checker_returns (by decide +kernel)
      (ListAccess.data_at_list_returns bindings state heap index "heap" "index" rfl rfl)
  · simp [reference_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup, bound, bindings,
      referenceEnvironment, stateEnvironment]
  · exact symbol_returns program bound state "None"

theorem reference_missing_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (index : Nat)
    (stateName indexName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      stateValue next arity count stack heap dummies hypotheses saved)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (missing : heap[index]? = none) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-reference", .var stateName, .var indexName]) state (.symbol "None") := by
  apply authored_variable_call_returns program bindings
    (referenceEnvironment next arity count stack heap dummies hypotheses saved index) state state
    "mm0:mmb:proof-reference" [stateName, indexName] referenceEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (reference_missing_body_returns state next arity count stack heap dummies hypotheses saved index missing)
    (by decide)
  simpa [stateCaptured, indexCaptured] using reference_clause next arity count stack heap dummies hypotheses saved index

private def saveEquation := sourceEquation "mm0:mmb:proof-save"
private def saveCases := casesOf saveEquation.body
private def saveCons := (saveCases[0]'(by decide)).2
private def saveTestCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"],
      .expression [.symbol "==", .var "pop", boolean false]),
   (.expression [.symbol "MM0:MMBProved", .var "witness", .var "target"],
      .expression [.symbol "==", .var "pop", boolean false]),
   (.expression [.symbol "MM0:MMBConversion", .var "witness", .var "left", .var "right"], boolean true),
   (.var "bad", boolean false)]
private def saveEnvironment (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (pop : Bool) : Subst :=
  ("pop", boolean pop) :: stateEnvironment next arity count stack heap dummies hypotheses saved
private theorem save_unique : program.equations.filter (·.head == "mm0:mmb:proof-save") =
    [saveEquation] := by decide +kernel
private theorem save_formals : saveEquation.arguments =
    referenceEquation.arguments.take 1 ++ [.var "pop"] := by decide
private theorem save_shape : saveEquation.body =
    .expression [.symbol "case", .var "stack",
      .expression (saveCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem save_cases_shape : saveCases =
    [(.expression [.symbol "cons", .var "first", .var "rest"], saveCons),
     (.var "bad", .symbol "None")] := by decide
private theorem save_cons_shape : saveCons =
    .expression [.symbol "if", .expression [.symbol "case", .var "first",
      .expression (saveTestCases.map fun row => .expression [row.1, row.2])],
      .expression [.symbol "let*", .expression [
        .expression [.var "after", .expression [.symbol "mm0:mmb:snoc", .var "heap", .var "first"]],
        .expression [.var "remaining", .expression [.symbol "if", .var "pop",
          .expression [.symbol "MM0:L", .var "rest"], .expression [.symbol "MM0:L", .var "stack"]]]],
        .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity",
          .var "count", .var "remaining", .var "after", .var "dummies", .var "hyps", .var "saved"]]],
      .symbol "None"] := by decide
private theorem save_clause (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (pop : Bool) :
    clauses program "mm0:mmb:proof-save"
      [stateValue next arity count stack heap dummies hypotheses saved, boolean pop] =
      [.evaluate (saveEnvironment next arity count stack heap dummies hypotheses saved pop)
        saveEquation.body] := by
  rw [clauses_use_only_the_named_equations, save_unique]
  simp [save_formals, reference_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, stateValue, listValue, saveEnvironment, stateEnvironment]

private theorem save_test_returns (bindings : Subst) (state : State) (entry : Atom) (pop : Bool)
    (entryCaptured : applySubst bindings (.var "first") = entry)
    (popCaptured : applySubst bindings (.var "pop") = boolean pop)
    (fresh : ∀ field ∈ ["id", "expression", "node", "witness", "target", "bad"],
      Subst.lookup bindings field = none)
    (reusable : ReusableEntry entry) :
    PureReturns program bindings state
      (.expression [.symbol "case", .var "first",
        .expression (saveTestCases.map fun row => .expression [row.1, row.2])]) state
      (boolean (!pop)) := by
  simp only [Subst.lookup] at fresh
  have equality (bound : Subst) (captured : applySubst bound (.var "pop") = boolean pop) :
      PureReturns program bound state (.expression [.symbol "==", .var "pop", boolean false])
        state (boolean (!pop)) := by
    apply native_binary_call_returns program bound state state state state "==" _ _
      (boolean pop) (boolean false) _ (by decide) (by decide) (by decide +kernel)
      (by decide +kernel)
      (by simpa only [captured] using variable_returns program bound state "pop")
      (grounded_returns program bound state (.bool false)) _ (by decide)
    cases pop <;> rfl
  cases reusable with
  | expression allocation expression node =>
      let bound := ("node", node) :: ("expression", expression) :: ("id", natural allocation) :: bindings
      apply case_returns program bindings bound state state state (.var "first") _
        (.expression [.symbol "==", .var "pop", boolean false]) _ _ saveTestCases (read_cases_encoded saveTestCases)
      · simpa only [entryCaptured] using variable_returns program bindings state "first"
      · simp [saveTestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, expressionValue, matchAtom, Subst.lookup, bound, fresh "id" (by simp),
          fresh "expression" (by simp), fresh "node" (by simp)]
      · apply equality bound
        simpa [bound, applySubst, Subst.lookup] using popCaptured
  | proved witness target =>
      let bound := ("target", target) :: ("witness", witness) :: bindings
      apply case_returns program bindings bound state state state (.var "first") _
        (.expression [.symbol "==", .var "pop", boolean false]) _ _ saveTestCases (read_cases_encoded saveTestCases)
      · simpa only [entryCaptured] using variable_returns program bindings state "first"
      · simp [saveTestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, provedValue, matchAtom, Subst.lookup, bound, fresh "witness" (by simp),
          fresh "target" (by simp)]
      · apply equality bound
        simpa [bound, applySubst, Subst.lookup] using popCaptured

private theorem save_cons_returns (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (entry : Atom) (pop : Bool)
    (reusable : ReusableEntry entry) :
    PureReturns program (("rest", .expression rest) :: ("first", entry) ::
      saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop)
      state saveCons state
      (optionValue (if pop then none else
        some (stateValue next arity count (entry :: rest) (heap ++ [entry]) dummies hypotheses saved))) := by
  let bindings := ("rest", .expression rest) :: ("first", entry) ::
    saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop
  rw [save_cons_shape]
  apply if_returns program bindings state state state _ (boolean (!pop)) _ _ _
  · apply save_test_returns bindings state entry pop rfl _ _ reusable
    · simp [bindings, saveEnvironment, stateEnvironment, applySubst, Subst.lookup]
    · intro field member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [bindings, saveEnvironment, stateEnvironment, Subst.lookup]
  · cases pop with
    | true =>
        simp only [Bool.not_true, boolean, ↓reduceIte, optionValue]
        exact symbol_returns program bindings state "None"
    | false =>
        simp only [Bool.not_false, boolean, beq_self_eq_true, ↓reduceIte]
        let after := ("after", listValue (heap ++ [entry])) :: bindings
        let remaining := ("remaining", listValue (entry :: rest)) :: after
        apply let_star_returns program bindings state state _ _ _ _ rfl
        apply let_returns program bindings after state state state (.var "after") _ _
          (listValue (heap ++ [entry])) _
        · apply snoc_returns bindings state heap entry "heap" "first" _ rfl
          simp [bindings, saveEnvironment, stateEnvironment, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchValue, matchAtom, after, bindings, saveEnvironment,
            stateEnvironment, Subst.lookup]
        · apply let_returns program after remaining state state state (.var "remaining") _ _
            (listValue (entry :: rest)) _
          · apply if_returns program after state state state _ (boolean false) _ _ _
            · simpa [after, bindings, saveEnvironment, stateEnvironment, applySubst, Subst.lookup] using
                variable_returns program after state "pop"
            · simp only [boolean]
              simpa [after, bindings, saveEnvironment, stateEnvironment, applySubst,
                applySubst.applySubstList, Subst.lookup, listValue] using
                unary_constructor_returns program after state "MM0:L" "stack" (by decide +kernel) (by decide)
          · simp [SpaceSemantics.matchValue, matchAtom, remaining, after, bindings, saveEnvironment,
              stateEnvironment, Subst.lookup]
          · have result : PureReturns program remaining state
                (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next",
                  .var "arity", .var "count", .var "remaining", .var "after", .var "dummies",
                  .var "hyps", .var "saved"]]) state
                (applySubst remaining (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next",
                  .var "arity", .var "count", .var "remaining", .var "after", .var "dummies",
                  .var "hyps", .var "saved"]])) := by mmb_data
            simpa [remaining, after, bindings, saveEnvironment, stateEnvironment, stateValue,
              optionValue, applySubst, applySubst.applySubstList, Subst.lookup] using result

private theorem save_body_returns (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (entry : Atom) (pop : Bool)
    (reusable : ReusableEntry entry) :
    PureReturns program (saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop)
      state saveEquation.body state
      (optionValue (if pop then none else
        some (stateValue next arity count (entry :: rest) (heap ++ [entry]) dummies hypotheses saved))) := by
  let bindings := saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop
  let bound := ("rest", .expression rest) :: ("first", entry) :: bindings
  rw [save_shape]
  apply case_returns program bindings bound state state state (.var "stack")
    (.expression (entry :: rest)) saveCons _ _ saveCases (read_cases_encoded saveCases)
  · simpa [bindings, saveEnvironment, stateEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "stack"
  · simp [save_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup, bindings, bound,
      saveEnvironment, stateEnvironment]
  · exact save_cons_returns state next arity count rest heap dummies hypotheses saved entry pop reusable

/-- Expression and proved entries can be copied into the heap, with duplicates retained.
The source refuses popping either of these entry kinds. -/
theorem save_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (entry : Atom) (pop : Bool)
    (stateName popName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      stateValue next arity count (entry :: rest) heap dummies hypotheses saved)
    (popCaptured : applySubst bindings (.var popName) = boolean pop)
    (reusable : ReusableEntry entry) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-save", .var stateName, .var popName]) state
      (optionValue (if pop then none else
        some (stateValue next arity count (entry :: rest) (heap ++ [entry]) dummies hypotheses saved))) := by
  apply authored_variable_call_returns program bindings
    (saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop) state state
    "mm0:mmb:proof-save" [stateName, popName] saveEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (save_body_returns state next arity count rest heap dummies hypotheses saved entry pop reusable)
    (by decide)
  simpa [stateCaptured, popCaptured] using save_clause next arity count (entry :: rest) heap dummies hypotheses saved pop

private def hypothesisEquation := sourceEquation "mm0:mmb:proof-hypothesis"
private def hypothesisCases := casesOf hypothesisEquation.body
private def hypothesisCons := (hypothesisCases[0]'(by decide)).2
private def hypothesisEnvironment (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) : Subst :=
  [("saved", listValue saved), ("hyps", .expression hypotheses), ("dummies", listValue dummies),
    ("heap", listValue heap), ("stack", .expression stack), ("count", natural count),
    ("arity", natural arity), ("next", natural next)]
private theorem hypothesis_unique : program.equations.filter (·.head == "mm0:mmb:proof-hypothesis") =
    [hypothesisEquation] := by decide +kernel
private theorem hypothesis_formals : hypothesisEquation.arguments =
    [.expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
      .expression [.symbol "MM0:L", .var "stack"], .var "heap", .var "dummies",
      .expression [.symbol "MM0:L", .var "hyps"], .var "saved"]] := by decide
private theorem hypothesis_shape : hypothesisEquation.body =
    .expression [.symbol "case", .var "stack",
      .expression (hypothesisCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem hypothesis_cases_shape : hypothesisCases =
    [(.expression [.symbol "cons", .expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"],
       .var "rest"], hypothesisCons), (.var "bad", .symbol "None")] := by decide
private theorem hypothesis_clause (next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) :
    clauses program "mm0:mmb:proof-hypothesis"
      [stateValue next arity count stack heap dummies hypotheses saved] =
      [.evaluate (hypothesisEnvironment next arity count stack heap dummies hypotheses saved)
        hypothesisEquation.body] := by
  rw [clauses_use_only_the_named_equations, hypothesis_unique]
  simp [hypothesis_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, stateValue, listValue, hypothesisEnvironment]

private theorem hypothesis_cons_shape : hypothesisCons =
    .expression [.symbol "let", .var "index", .expression [.symbol "size-atom", .var "hyps"],
      .expression [.symbol "if", .expression [.symbol "<", .var "index", .var "count"],
        .expression [.symbol "let*", .expression [
          .expression [.var "target", .expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"]],
          .expression [.var "witness", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]]],
          .expression [.var "proof", .expression [.symbol "MM0:MMBProved", .var "witness", .var "target"]],
          .expression [.var "after", .expression [.symbol "mm0:mmb:snoc", .var "heap", .var "proof"]],
          .expression [.var "hypotheses", .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "hyps"], .var "target"]]],
          .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
            .expression [.symbol "MM0:L", .var "rest"], .var "after", .var "dummies", .var "hypotheses", .var "saved"]]],
        .symbol "None"]] := by decide

private theorem snoc_raw_returns (bindings : Subst) (state : State) (items : List Atom) (value : Atom)
    (itemsCode valueCode : Atom)
    (itemsCaptured : applySubst bindings itemsCode = listValue items)
    (valueCaptured : applySubst bindings valueCode = value) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:snoc", itemsCode, valueCode]) state (listValue (items ++ [value])) := by
  apply raw_call_returns program bindings state state "mm0:mmb:snoc" _ _ (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have positions : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases positions with rfl | rfl <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, itemsCaptured, valueCaptured] using
      authored_function_arguments_return program bindings (snocEnvironment items value) state state
        "mm0:mmb:snoc" [listValue items, value] 2 snocEquation.body _ (by decide) (by decide)
        (snoc_clause items value) (snoc_body_returns state items value)

/-- Exact source readout, including the witness's original hypothesis position. -/
def hypothesisResult (next arity count : Nat) (rest heap dummies hypotheses saved : List Atom)
    (allocation : Nat) (expression node : Atom) : Option Atom :=
  if hypotheses.length < count then
    let target := expressionValue allocation expression node
    some (stateValue next arity count rest
      (heap ++ [provedValue (Hypothesis.witness hypotheses.length) target]) dummies
      (hypotheses ++ [target]) saved)
  else none

private theorem hypothesis_cons_returns (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (allocation : Nat) (expression node : Atom) :
    PureReturns program (("rest", .expression rest) :: ("node", node) ::
      ("expression", expression) :: ("id", natural allocation) ::
      hypothesisEnvironment next arity count (expressionValue allocation expression node :: rest)
        heap dummies hypotheses saved) state hypothesisCons state
      (optionValue (hypothesisResult next arity count rest heap dummies hypotheses saved allocation expression node)) := by
  let target := expressionValue allocation expression node
  let witness := Hypothesis.witness hypotheses.length
  let proof := provedValue witness target
  let bindings := ("rest", .expression rest) :: ("node", node) ::
    ("expression", expression) :: ("id", natural allocation) ::
    hypothesisEnvironment next arity count (target :: rest) heap dummies hypotheses saved
  let indexed := ("index", natural hypotheses.length) :: bindings
  rw [hypothesis_cons_shape]
  apply let_returns program bindings indexed state state state (.var "index") _ _ (natural hypotheses.length) _
  · apply native_variable_call_returns program bindings state state "size-atom" ["hyps"] _
      (by decide) (by decide) _ (by decide)
    simp [bindings, hypothesisEnvironment, applySubst, Subst.lookup, natural]
  · simp [SpaceSemantics.matchValue, matchAtom, indexed, bindings, hypothesisEnvironment, Subst.lookup]
  · apply if_returns program indexed state state state _ (boolean (hypotheses.length < count)) _ _ _
    · apply native_variable_call_returns program indexed state state "<" ["index", "count"] _
        (by decide) (by decide) _ (by decide)
      simp [indexed, bindings, hypothesisEnvironment, applySubst, Subst.lookup, natural,
        boolean]
    · by_cases available : hypotheses.length < count
      · simp only [available, decide_true, boolean, beq_self_eq_true, ↓reduceIte]
        let targeted := ("target", target) :: indexed
        let witnessed := ("witness", witness) :: targeted
        let proved := ("proof", proof) :: witnessed
        let heaped := ("after", listValue (heap ++ [proof])) :: proved
        let hypothesized := ("hypotheses", listValue (hypotheses ++ [target])) :: heaped
        apply let_star_returns program indexed state state _ _ _ _ rfl
        apply let_returns program indexed targeted state state state (.var "target") _ _ target _
        · have constructed : PureReturns program indexed state
              (.expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"]) state
              (applySubst indexed (.expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"])) := by mmb_data
          simpa [indexed, bindings, target, expressionValue, applySubst, applySubst.applySubstList,
            Subst.lookup] using constructed
        · simp [SpaceSemantics.matchValue, matchAtom, targeted, indexed, bindings, hypothesisEnvironment, Subst.lookup]
        · apply let_returns program targeted witnessed state state state (.var "witness") _ _ witness _
          · have constructed : PureReturns program targeted state
                (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]]) state
                (applySubst targeted (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]])) := by mmb_data
            simpa [targeted, indexed, bindings, witness, Hypothesis.witness, applySubst,
              applySubst.applySubstList, Subst.lookup] using constructed
          · simp [SpaceSemantics.matchValue, matchAtom, witnessed, targeted, indexed, bindings,
              hypothesisEnvironment, Subst.lookup]
          · apply let_returns program witnessed proved state state state (.var "proof") _ _ proof _
            · have constructed : PureReturns program witnessed state
                  (.expression [.symbol "MM0:MMBProved", .var "witness", .var "target"]) state
                  (applySubst witnessed (.expression [.symbol "MM0:MMBProved", .var "witness", .var "target"])) := by mmb_data
              simpa [witnessed, targeted, proof, provedValue, applySubst, applySubst.applySubstList,
                Subst.lookup] using constructed
            · simp [SpaceSemantics.matchValue, matchAtom, proved, witnessed, targeted, indexed, bindings,
                hypothesisEnvironment, Subst.lookup]
            · apply let_returns program proved heaped state state state (.var "after") _ _
                (listValue (heap ++ [proof])) _
              · apply snoc_returns proved state heap proof "heap" "proof" _ rfl
                simp [proved, witnessed, targeted, indexed, bindings, hypothesisEnvironment, applySubst, Subst.lookup]
              · simp [SpaceSemantics.matchValue, matchAtom, heaped, proved, witnessed, targeted,
                  indexed, bindings, hypothesisEnvironment, Subst.lookup]
              · apply let_returns program heaped hypothesized state state state (.var "hypotheses") _ _
                  (listValue (hypotheses ++ [target])) _
                · apply snoc_raw_returns heaped state hypotheses target
                    (.expression [.symbol "MM0:L", .var "hyps"]) (.var "target")
                  · simp [heaped, proved, witnessed, targeted, indexed, bindings, hypothesisEnvironment,
                      applySubst, applySubst.applySubstList, Subst.lookup, listValue]
                  · simp [heaped, proved, witnessed, targeted, indexed, bindings, hypothesisEnvironment,
                      applySubst, Subst.lookup]
                · simp [SpaceSemantics.matchValue, matchAtom, hypothesized, heaped, proved,
                    witnessed, targeted, indexed, bindings, hypothesisEnvironment, Subst.lookup]
                · have constructed : PureReturns program hypothesized state
                      (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
                        .expression [.symbol "MM0:L", .var "rest"], .var "after", .var "dummies", .var "hypotheses", .var "saved"]]) state
                      (applySubst hypothesized (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
                        .expression [.symbol "MM0:L", .var "rest"], .var "after", .var "dummies", .var "hypotheses", .var "saved"]])) := by mmb_data
                  simpa [hypothesized, heaped, proved, witnessed, targeted, indexed, bindings,
                    hypothesisEnvironment, hypothesisResult, available, stateValue, optionValue,
                    applySubst, applySubst.applySubstList, Subst.lookup, listValue, proof, witness,
                    target] using constructed
      · simp only [available, decide_false, boolean, ↓reduceIte,
          hypothesisResult, optionValue]
        exact symbol_returns program indexed state "None"

private theorem hypothesis_body_returns (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (allocation : Nat) (expression node : Atom) :
    PureReturns program (hypothesisEnvironment next arity count
      (expressionValue allocation expression node :: rest) heap dummies hypotheses saved)
      state hypothesisEquation.body state
      (optionValue (hypothesisResult next arity count rest heap dummies hypotheses saved allocation expression node)) := by
  let bindings := hypothesisEnvironment next arity count
    (expressionValue allocation expression node :: rest) heap dummies hypotheses saved
  let bound := ("rest", .expression rest) :: ("node", node) :: ("expression", expression) ::
    ("id", natural allocation) :: bindings
  rw [hypothesis_shape]
  apply case_returns program bindings bound state state state (.var "stack")
    (.expression (expressionValue allocation expression node :: rest)) hypothesisCons _ _
    hypothesisCases (read_cases_encoded hypothesisCases)
  · simpa [bindings, hypothesisEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "stack"
  · simp [hypothesis_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, bound,
      hypothesisEnvironment, expressionValue]
  · exact hypothesis_cons_returns state next arity count rest heap dummies hypotheses saved allocation expression node

/-- Hypothesis introduction consumes an expression and stores the actual `Hyp`
witness at its chronological hypothesis index. An exhausted budget returns `None`. -/
theorem hypothesis_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (allocation : Nat) (expression node : Atom)
    (stateName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      stateValue next arity count (expressionValue allocation expression node :: rest)
        heap dummies hypotheses saved) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-hypothesis", .var stateName]) state
      (optionValue (hypothesisResult next arity count rest heap dummies hypotheses saved allocation expression node)) := by
  apply authored_variable_call_returns program bindings
    (hypothesisEnvironment next arity count (expressionValue allocation expression node :: rest)
      heap dummies hypotheses saved) state state
    "mm0:mmb:proof-hypothesis" [stateName] hypothesisEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (hypothesis_body_returns state next arity count rest heap dummies hypotheses saved allocation expression node)
    (by decide)
  simpa [stateCaptured] using hypothesis_clause next arity count
    (expressionValue allocation expression node :: rest) heap dummies hypotheses saved

private theorem save_raw_returns (bindings : Subst) (state : State) (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (entry : Atom) (pop : Bool)
    (stateCode : Atom)
    (stateCaptured : applySubst bindings stateCode =
      stateValue next arity count (entry :: rest) heap dummies hypotheses saved)
    (reusable : ReusableEntry entry) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-save", stateCode, boolean pop]) state
      (optionValue (if pop then none else
        some (stateValue next arity count (entry :: rest) (heap ++ [entry]) dummies hypotheses saved))) := by
  apply raw_call_returns program bindings state state "mm0:mmb:proof-save" _ _ (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have positions : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases positions with rfl | rfl <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, stateCaptured,
      boolean, applySubst] using
      authored_function_arguments_return program bindings
        (saveEnvironment next arity count (entry :: rest) heap dummies hypotheses saved pop) state state
        "mm0:mmb:proof-save"
        [stateValue next arity count (entry :: rest) heap dummies hypotheses saved, boolean pop] 2
        saveEquation.body _ (by decide) (by decide)
        (save_clause next arity count (entry :: rest) heap dummies hypotheses saved pop)
        (save_body_returns state next arity count rest heap dummies hypotheses saved entry pop reusable)

/-- An independent relational specification of the supported original commands.
Byte intervals are carried by the calling `MMBCode`; these commands do not edit them. -/
inductive SupportedStep : Atom → Nat → Nat → Option Atom → Prop where
  | reference {next arity count : Nat} {stack heap dummies hypotheses saved : List Atom}
      {index : Nat} {entry : Atom}
      (found : heap[index]? = some entry) (reusable : ReusableEntry entry) :
      SupportedStep (stateValue next arity count stack heap dummies hypotheses saved) 18 index
        (some (stateValue next arity count (entry :: stack) heap dummies hypotheses saved))
  | missingReference {next arity count : Nat} {stack heap dummies hypotheses saved : List Atom}
      {index : Nat} (missing : heap[index]? = none) :
      SupportedStep (stateValue next arity count stack heap dummies hypotheses saved) 18 index none
  | save {next arity count : Nat} {rest heap dummies hypotheses saved : List Atom}
      {entry : Atom} {data : Nat} (reusable : ReusableEntry entry) :
      SupportedStep (stateValue next arity count (entry :: rest) heap dummies hypotheses saved) 31 data
        (some (stateValue next arity count (entry :: rest) (heap ++ [entry]) dummies hypotheses saved))
  | refusePop {next arity count : Nat} {rest heap dummies hypotheses saved : List Atom}
      {entry : Atom} {data : Nat} (reusable : ReusableEntry entry) :
      SupportedStep (stateValue next arity count (entry :: rest) heap dummies hypotheses saved) 30 data none
  | hypothesis {next arity count : Nat} {rest heap dummies hypotheses saved : List Atom}
      {allocation data : Nat} {expression node : Atom} :
      SupportedStep (stateValue next arity count (expressionValue allocation expression node :: rest)
          heap dummies hypotheses saved) 22 data
        (hypothesisResult next arity count rest heap dummies hypotheses saved allocation expression node)

private def stepEquation := sourceEquation "mm0:mmb:proof-step"
private def stepCondition : Atom :=
  .expression [.symbol "or", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBAssertion"],
    .expression [.symbol "and", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBDefinition"],
      .expression [.symbol "is-member", .var "opcode", .expression [natural 16, natural 17, natural 18, natural 19, natural 31]]]]
private def stepCases : SpaceSemantics.Cases :=
  match stepEquation.body with
  | .expression [_, _, .expression [_, _, .expression rows], _] => (readCases rows).getD []
  | _ => []
private theorem step_cases_shape : stepCases =
  [
    (natural 16, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean false]),
    (natural 17, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean true]),
    (natural 18, .expression [.symbol "mm0:mmb:proof-reference", .var "state", .var "data"]),
    (natural 19, .expression [.symbol "mm0:mmb:proof-dummy", .var "resolver", .var "state", .var "data"]),
    (natural 20, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean false]),
    (natural 21, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean true]),
    (natural 22, .expression [.symbol "mm0:mmb:proof-hypothesis", .var "state"]),
    (natural 23, .expression [.symbol "mm0:mmb:proof-conversion", .var "state"]),
    (natural 24, .expression [.symbol "mm0:mmb:proof-reflexivity", .var "state"]),
    (natural 25, .expression [.symbol "mm0:mmb:proof-symmetry", .var "state"]),
    (natural 26, .expression [.symbol "mm0:mmb:proof-congruence", .var "resolver", .var "state"]),
    (natural 27, .expression [.symbol "mm0:mmb:proof-unfold", .var "resolver", .var "tables", .var "formal", .var "state"]),
    (natural 28, .expression [.symbol "mm0:mmb:proof-cut", .var "state"]),
    (natural 30, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean true]),
    (natural 31, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean false]),
    (.var "bad", .symbol "None")] := by decide
private def stepEnvironment (resolver tables formal before : Atom) (opcode data start after : Nat) : Subst :=
  [("after", natural after), ("start", natural start), ("data", natural data), ("opcode", natural opcode),
    ("state", before), ("mode", .symbol "MM0:MMBAssertion"), ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem step_unique : program.equations.filter (·.head == "mm0:mmb:proof-step") =
    [stepEquation] := by decide +kernel
private theorem step_formals : stepEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"]] := by decide
private theorem step_shape : stepEquation.body =
    .expression [.symbol "if", stepCondition,
      .expression [.symbol "case", .var "opcode", .expression (stepCases.map fun row => .expression [row.1, row.2])],
      .symbol "None"] := by decide
private theorem step_clause (resolver tables formal before : Atom) (opcode data start after : Nat) :
    clauses program "mm0:mmb:proof-step"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, MMBExecution.commandValue opcode data start after] =
      [.evaluate (stepEnvironment resolver tables formal before opcode data start after) stepEquation.body] := by
  rw [clauses_use_only_the_named_equations, step_unique]
  simp [step_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, stepEnvironment, MMBExecution.commandValue]

private theorem supported_opcode {before : Atom} {opcode data : Nat} {after : Option Atom}
    (supported : SupportedStep before opcode data after) :
    opcode = 18 ∨ opcode = 22 ∨ opcode = 30 ∨ opcode = 31 := by
  cases supported <;> simp

private theorem step_condition_returns (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat)
    (supported : opcode = 18 ∨ opcode = 22 ∨ opcode = 30 ∨ opcode = 31) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after)
      state stepCondition state (boolean true) := by
  apply completed_run_has_path program 100 _ state [boolean true] [] []
  rcases supported with rfl | rfl | rfl | rfl <;> rfl

private theorem opcode_case_returns (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option Atom)
    (supported : SupportedStep before opcode data result) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state
      (.expression [.symbol "case", .var "opcode",
        .expression (stepCases.map fun row => .expression [row.1, row.2])]) state (optionValue result) := by
  let bindings := stepEnvironment resolver tables formal before opcode data start after
  cases supported with
  | @reference next arity count stack heap dummies hypotheses saved index entry found reusable =>
      apply case_returns program bindings bindings state state state (.var "opcode") (natural 18)
        (.expression [.symbol "mm0:mmb:proof-reference", .var "state", .var "data"])
        _ _ stepCases (read_cases_encoded stepCases)
      · exact variable_returns program bindings state "opcode"
      · simp [step_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact reference_returns bindings state next arity count stack heap dummies hypotheses saved data entry
          "state" "data" rfl rfl found reusable
  | @missingReference next arity count stack heap dummies hypotheses saved index missing =>
      apply case_returns program bindings bindings state state state (.var "opcode") (natural 18)
        (.expression [.symbol "mm0:mmb:proof-reference", .var "state", .var "data"])
        _ _ stepCases (read_cases_encoded stepCases)
      · exact variable_returns program bindings state "opcode"
      · simp [step_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact reference_missing_returns bindings state next arity count stack heap dummies hypotheses saved data
          "state" "data" rfl rfl missing
  | @save next arity count rest heap dummies hypotheses saved entry data reusable =>
      apply case_returns program bindings bindings state state state (.var "opcode") (natural 31)
        (.expression [.symbol "mm0:mmb:proof-save", .var "state", boolean false])
        _ _ stepCases (read_cases_encoded stepCases)
      · exact variable_returns program bindings state "opcode"
      · simp [step_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact save_raw_returns bindings state next arity count rest heap dummies hypotheses saved entry false
          (.var "state") rfl reusable
  | @refusePop next arity count rest heap dummies hypotheses saved entry data reusable =>
      apply case_returns program bindings bindings state state state (.var "opcode") (natural 30)
        (.expression [.symbol "mm0:mmb:proof-save", .var "state", boolean true])
        _ _ stepCases (read_cases_encoded stepCases)
      · exact variable_returns program bindings state "opcode"
      · simp [step_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact save_raw_returns bindings state next arity count rest heap dummies hypotheses saved entry true
          (.var "state") rfl reusable
  | @hypothesis next arity count rest heap dummies hypotheses saved allocation data expression node =>
      apply case_returns program bindings bindings state state state (.var "opcode") (natural 22)
        (.expression [.symbol "mm0:mmb:proof-hypothesis", .var "state"])
        _ _ stepCases (read_cases_encoded stepCases)
      · exact variable_returns program bindings state "opcode"
      · simp [step_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact hypothesis_returns bindings state next arity count rest heap dummies hypotheses saved allocation expression node
          "state" rfl

private theorem step_body_returns (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option Atom)
    (supported : SupportedStep before opcode data result) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after)
      state stepEquation.body state (optionValue result) := by
  rw [step_shape]
  apply if_returns program _ state state state _ (boolean true) _ _ _
    (step_condition_returns state resolver tables formal before opcode data start after (supported_opcode supported))
  simp only [boolean, beq_self_eq_true, ↓reduceIte]
  exact opcode_case_returns state resolver tables formal before opcode data start after result supported

/-- Actual source dispatch, including all original code metadata. -/
theorem step_returns (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option Atom)
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (supported : SupportedStep before opcode data result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName, .var formalName,
        .var modeName, .var stateName, .var codeName]) state (optionValue result) := by
  apply authored_variable_call_returns program bindings
    (stepEnvironment resolver tables formal before opcode data start after) state state
    "mm0:mmb:proof-step" [resolverName, tablesName, formalName, modeName, stateName, codeName]
    stepEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (step_body_returns state resolver tables formal before opcode data start after result supported) (by decide)
  simpa [resolverCaptured, tablesCaptured, formalCaptured, modeCaptured, stateCaptured, codeCaptured] using
    step_clause resolver tables formal before opcode data start after

/-- Finite source runs stop at a refused command; their remaining authored
suffix is not executed. Every successful step preserves physical occurrences. -/
inductive SupportedRun : Atom → List Atom → Option Atom → Prop where
  | done (before : Atom) : SupportedRun before [] (some before)
  | next {before middle : Atom} {opcode data start after : Nat} {rest : List Atom} {result : Option Atom}
      (advanced : SupportedStep before opcode data (some middle))
      (continued : SupportedRun middle rest result) :
      SupportedRun before (MMBExecution.commandValue opcode data start after :: rest) result
  | refused {before : Atom} {opcode data start after : Nat} (rest : List Atom)
      (stopped : SupportedStep before opcode data none) :
      SupportedRun before (MMBExecution.commandValue opcode data start after :: rest) none

private def runEquation := sourceEquation "mm0:mmb:proof-run"
private def runCases := casesOf runEquation.body
private def runCons := (runCases[1]'(by decide)).2
private def runConsCases := casesOf runCons
private def runTail := (runConsCases[0]'(by decide)).2
private def runEnvironment (resolver tables formal before : Atom) (commands : List Atom) : Subst :=
  [("codes", .expression commands), ("state", before), ("mode", .symbol "MM0:MMBAssertion"),
    ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem run_unique : program.equations.filter (·.head == "mm0:mmb:proof-run") = [runEquation] := by decide +kernel
private theorem run_formals : runEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:L", .var "codes"]] := by decide
private theorem run_shape : runEquation.body =
    .expression [.symbol "case", .var "codes",
      .expression (runCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cases_shape : runCases =
    [(.expression [], .expression [.symbol "Some", .var "state"]),
     (.expression [.symbol "cons", .var "first", .var "rest"], runCons),
     (.var "bad", .symbol "None")] := by decide
private theorem run_cons_shape : runCons =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:proof-step", .var "resolver", .var "tables", .var "formal",
      .var "mode", .var "state", .var "first"],
      .expression (runConsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cons_cases_shape : runConsCases =
    [(.expression [.symbol "Some", .var "after"], runTail), (.var "bad", .symbol "None")] := by decide
private theorem run_tail_shape : runTail =
    .expression [.symbol "mm0:mmb:proof-run", .var "resolver", .var "tables", .var "formal", .var "mode",
      .var "after", .expression [.symbol "MM0:L", .var "rest"]] := by decide
private theorem run_clause (resolver tables formal before : Atom) (commands : List Atom) :
    clauses program "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] =
      [.evaluate (runEnvironment resolver tables formal before commands) runEquation.body] := by
  rw [clauses_use_only_the_named_equations, run_unique]
  simp [run_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, runEnvironment, listValue]

private theorem raw_run_from_body (bindings : Subst) (state : State)
    (resolver tables formal before : Atom) (commands : List Atom) (result : Option Atom)
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands])
    (body : PureReturns program (runEnvironment resolver tables formal before commands)
      state runEquation.body state (optionValue result)) :
    PureReturns program bindings state (.expression (.symbol "mm0:mmb:proof-run" :: arguments))
      state (optionValue result) := by
  have length : arguments.length = 6 := by
    have sizes := congrArg List.length captured
    simpa using sizes
  apply raw_call_returns program bindings state state "mm0:mmb:proof-run" arguments _
    (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    rw [length] at bounded
    have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured, length]
    exact authored_function_arguments_return program bindings
      (runEnvironment resolver tables formal before commands) state state "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] 6
      runEquation.body _ (by decide) (by decide) (run_clause resolver tables formal before commands) body

private theorem run_body_returns (state : State) (resolver tables formal : Atom)
    {before : Atom} {commands : List Atom} {result : Option Atom}
    (supported : SupportedRun before commands result) :
    PureReturns program (runEnvironment resolver tables formal before commands)
      state runEquation.body state (optionValue result) := by
  induction supported with
  | done before =>
      let bindings := runEnvironment resolver tables formal before []
      rw [run_shape]
      apply case_returns program bindings bindings state state state (.var "codes")
        (.expression []) (.expression [.symbol "Some", .var "state"]) _ _
        runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · simpa [bindings, runEnvironment, applySubst, Subst.lookup, optionValue] using
          unary_constructor_returns program bindings state "Some" "state" (by decide +kernel) (by decide)
  | @next before middle opcode data start after rest result advanced continued ih =>
      let command := MMBExecution.commandValue opcode data start after
      let bindings := runEnvironment resolver tables formal before (command :: rest)
      let bound := ("rest", .expression rest) :: ("first", command) :: bindings
      let resumed := ("after", middle) :: bound
      rw [run_shape]
      apply case_returns program bindings bound state state state (.var "codes")
        (.expression (command :: rest)) runCons _ _ runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, bound, bindings, runEnvironment]
      · rw [run_cons_shape]
        apply case_returns program bound resumed state state state _ (optionValue (some middle)) runTail
          _ _ runConsCases (read_cases_encoded runConsCases)
        · apply step_returns bound state resolver tables formal before opcode data start after (some middle)
            "resolver" "tables" "formal" "mode" "state" "first" _ _ _ _ _ rfl advanced
          all_goals simp [bound, bindings, runEnvironment, applySubst, Subst.lookup]
        · simp [run_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, resumed, bound,
            bindings, runEnvironment, optionValue]
        · rw [run_tail_shape]
          apply raw_run_from_body resumed state resolver tables formal middle rest result _ _ ih
          simp [resumed, bound, bindings, runEnvironment, applySubst, applySubst.applySubstList,
            Subst.lookup, listValue]
  | @refused before opcode data start after rest stopped =>
      let command := MMBExecution.commandValue opcode data start after
      let bindings := runEnvironment resolver tables formal before (command :: rest)
      let bound := ("rest", .expression rest) :: ("first", command) :: bindings
      let refused := ("bad", .symbol "None") :: bound
      rw [run_shape]
      apply case_returns program bindings bound state state state (.var "codes")
        (.expression (command :: rest)) runCons _ _ runCases (read_cases_encoded runCases)
      · exact variable_returns program bindings state "codes"
      · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, bound, bindings, runEnvironment]
      · rw [run_cons_shape]
        apply case_returns program bound refused state state state _ (.symbol "None") (.symbol "None")
          _ _ runConsCases (read_cases_encoded runConsCases)
        · apply step_returns bound state resolver tables formal before opcode data start after none
            "resolver" "tables" "formal" "mode" "state" "first" _ _ _ _ _ rfl stopped
          all_goals simp [bound, bindings, runEnvironment, applySubst, Subst.lookup]
        · simp [run_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            matchAtom, Subst.lookup, refused, bound, bindings, runEnvironment]
        · exact symbol_returns program refused state "None"

/-- Complete execution of arbitrary finite supported assertion-command runs.
The proof follows the original recursive frontend, including refusal short-circuiting. -/
theorem run_returns (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (commands : List Atom) (result : Option Atom)
    (resolverName tablesName formalName modeName stateName commandsName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (commandsCaptured : applySubst bindings (.var commandsName) = listValue commands)
    (supported : SupportedRun before commands result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:proof-run", .var resolverName, .var tablesName, .var formalName,
        .var modeName, .var stateName, .var commandsName]) state (optionValue result) := by
  apply raw_run_from_body bindings state resolver tables formal before commands result _ _
    (run_body_returns state resolver tables formal supported)
  simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, formalCaptured,
    modeCaptured, stateCaptured, commandsCaptured]

/-- The supported frontend computation completes at some finite fuel, and its
ordered one-result observation is stable at every larger fuel. -/
theorem run_sufficient_fuel (state : State) (resolver tables formal before : Atom)
    (commands : List Atom) (result : Option Atom) (supported : SupportedRun before commands result) :
    ∃ fuel, ∀ extra, Eval.run program (fuel + extra)
      { state, control := .evaluate [] (.expression [.symbol "mm0:mmb:proof-run", resolver,
        tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands]) } =
      .complete state [optionValue result] [] [] := by
  have returned := raw_run_from_body [] state resolver tables formal before commands result
    [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands]
    (by simp only [List.map_cons, List.map_nil, applySubst_nil])
    (run_body_returns state resolver tables formal supported)
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program [] state state _ _ returned
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [optionValue result] [] [] completed⟩


/-- The source's expression entries project to their existing preterm atoms,
without reading or evaluating allocation and child metadata. -/
inductive ExpressionClaims : List Atom → List Atom → Prop where
  | nil : ExpressionClaims [] []
  | cons {entries claims : List Atom} (allocation : Nat) (expression node : Atom)
      (tail : ExpressionClaims entries claims) :
      ExpressionClaims (expressionValue allocation expression node :: entries) (expression :: claims)

theorem ExpressionClaims.length {entries claims : List Atom}
    (projected : ExpressionClaims entries claims) : entries.length = claims.length := by
  induction projected with
  | nil => rfl
  | cons _ _ _ _ ih => simpa using ih

theorem ExpressionClaims.append {first second values other : List Atom}
    (left : ExpressionClaims first values) (right : ExpressionClaims second other) :
    ExpressionClaims (first ++ second) (values ++ other) := by
  induction left with
  | nil => exact right
  | cons allocation expression node _ ih => exact .cons allocation expression node ih

private def valuesEquation := sourceEquation "mm0:mmb:expression-values"
private def valuesCases := casesOf valuesEquation.body
private def valuesCons := (valuesCases[1]'(by decide)).2
private def valuesConsCases := casesOf valuesCons
private def valuesTail := (valuesConsCases[0]'(by decide)).2
private def valuesEnvironment (entries : List Atom) : Subst := [("entries", .expression entries)]
private theorem values_unique : program.equations.filter (·.head == "mm0:mmb:expression-values") =
    [valuesEquation] := by decide +kernel
private theorem values_formals : valuesEquation.arguments =
    [.expression [.symbol "MM0:L", .var "entries"]] := by decide
private theorem values_shape : valuesEquation.body =
    .expression [.symbol "case", .var "entries",
      .expression (valuesCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem values_cases_shape : valuesCases =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]),
     (.expression [.symbol "cons", .expression [.symbol "MM0:MMBExpression", .var "id", .var "expression", .var "node"],
       .var "rest"], valuesCons), (.var "bad", .symbol "None")] := by decide
private theorem values_cons_shape : valuesCons =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:expression-values",
      .expression [.symbol "MM0:L", .var "rest"]],
      .expression (valuesConsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem values_cons_cases_shape : valuesConsCases =
    [(.expression [.symbol "Some", .var "tail"], valuesTail), (.var "bad", .symbol "None")] := by decide
private theorem values_tail_shape : valuesTail =
    .expression [.symbol "let", .var "values",
      .expression [.symbol "mm0:list-cons", .var "expression", .var "tail"],
      .expression [.symbol "Some", .var "values"]] := by decide
private theorem values_clause (entries : List Atom) :
    clauses program "mm0:mmb:expression-values" [listValue entries] =
      [.evaluate (valuesEnvironment entries) valuesEquation.body] := by
  rw [clauses_use_only_the_named_equations, values_unique]
  simp [values_formals, valuesEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem raw_values_from_body (bindings : Subst) (state : State)
    (entries claims : List Atom) (argument : Atom)
    (captured : applySubst bindings argument = listValue entries)
    (body : PureReturns program (valuesEnvironment entries) state valuesEquation.body state
      (optionValue (some (listValue claims)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:expression-values", argument])
      state (optionValue (some (listValue claims))) := by
  apply raw_call_returns program bindings state state "mm0:mmb:expression-values" [argument] _
    (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have eq : offset = 0 := by simpa using bounded
    subst offset
    decide +kernel
  · simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, captured]
    exact authored_function_arguments_return program bindings (valuesEnvironment entries)
      state state "mm0:mmb:expression-values" [listValue entries] 1 valuesEquation.body _
      (by decide) (by decide) (values_clause entries) body

private theorem values_body_returns (state : State) {entries claims : List Atom}
    (projected : ExpressionClaims entries claims) :
    PureReturns program (valuesEnvironment entries) state valuesEquation.body state
      (optionValue (some (listValue claims))) := by
  induction projected with
  | nil =>
      rw [values_shape]
      let bindings := valuesEnvironment []
      apply case_returns program bindings bindings state state state (.var "entries") (.expression [])
        (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]) _ _
        valuesCases (read_cases_encoded valuesCases)
      · exact variable_returns program bindings state "entries"
      · simp [values_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · have built : PureReturns program bindings state
            (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]) state
            (applySubst bindings (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]])) := by
          mmb_data
        simpa [bindings, valuesEnvironment, optionValue, listValue, applySubst,
          applySubst.applySubstList] using built
  | @cons entries claims allocation expression node projected ih =>
      let bindings := valuesEnvironment (expressionValue allocation expression node :: entries)
      let bound := ("rest", .expression entries) :: ("node", node) :: ("expression", expression) ::
        ("id", natural allocation) :: bindings
      let tailed := ("tail", listValue claims) :: bound
      let valued := ("values", listValue (expression :: claims)) :: tailed
      rw [values_shape]
      apply case_returns program bindings bound state state state (.var "entries")
        (.expression (expressionValue allocation expression node :: entries)) valuesCons _ _
        valuesCases (read_cases_encoded valuesCases)
      · exact variable_returns program bindings state "entries"
      · simp [values_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, bound,
          valuesEnvironment, expressionValue]
      · rw [values_cons_shape]
        apply case_returns program bound tailed state state state _ (optionValue (some (listValue claims)))
          valuesTail _ _ valuesConsCases (read_cases_encoded valuesConsCases)
        · apply raw_values_from_body bound state entries claims (.expression [.symbol "MM0:L", .var "rest"]) _ ih
          simp [bound, bindings, valuesEnvironment, applySubst, applySubst.applySubstList, Subst.lookup, listValue]
        · simp [values_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, bound,
            bindings, valuesEnvironment, optionValue]
        · rw [values_tail_shape]
          apply let_returns program tailed valued state state state (.var "values") _ _
            (listValue (expression :: claims)) _
          · apply cons_returns tailed state expression claims (.var "expression") (.var "tail")
            · simp [tailed, bound, bindings, valuesEnvironment, applySubst, Subst.lookup]
            · simp [tailed, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchValue, matchAtom, valued, tailed, bound, bindings,
              valuesEnvironment, Subst.lookup]
          · simpa [valued, applySubst, Subst.lookup, optionValue] using
              unary_constructor_returns program valued state "Some" "values" (by decide +kernel) (by decide)

/-- The unchanged frontend's normalization of a complete expression-entry list.
This is the operation used before comparing binary hypotheses to the specification. -/
theorem expression_values_returns (bindings : Subst) (state : State) (entries claims : List Atom)
    (argument : Atom) (captured : applySubst bindings argument = listValue entries)
    (projected : ExpressionClaims entries claims) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:expression-values", argument])
      state (optionValue (some (listValue claims))) :=
  raw_values_from_body bindings state entries claims argument captured (values_body_returns state projected)

/-- The original kernel reads the actual emitted hypothesis witness; no other
signature data is needed by this branch. Hypothesis admission remains separate. -/
theorem kernel_hypothesis_returns (bindings : Subst) (state : State)
    (table definitions theorems context : Atom) (hypotheses : List Atom) (index : Nat)
    (tableName definitionsName theoremsName contextName hypothesesName witnessName : String)
    (tableCaptured : applySubst bindings (.var tableName) = table)
    (definitionsCaptured : applySubst bindings (.var definitionsName) = definitions)
    (theoremsCaptured : applySubst bindings (.var theoremsName) = theorems)
    (contextCaptured : applySubst bindings (.var contextName) = context)
    (hypothesesCaptured : applySubst bindings (.var hypothesesName) = listValue hypotheses)
    (witnessCaptured : applySubst bindings (.var witnessName) = Hypothesis.witness index) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof", .var tableName,
      .var definitionsName, .var theoremsName, .var contextName, .var hypothesesName, .var witnessName]) state
      (optionValue (hypotheses[index]?)) := by
  let inner : Subst := [("witness", Hypothesis.witness index), ("hypotheses", listValue hypotheses),
    ("context", context), ("theorems", theorems), ("definitions", definitions), ("table", table)]
  have returned : PureReturns program inner state MeTTa.proofEquation.body state
      (optionValue (hypotheses[index]?)) :=
    checker_returns (by decide +kernel)
      (Hypothesis.proof_body_returns state table definitions theorems context hypotheses index)
  apply authored_variable_call_returns program bindings inner state state "mm0:proof"
    [tableName, definitionsName, theoremsName, contextName, hypothesesName, witnessName]
    MeTTa.proofEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _ returned (by decide)
  apply PureData.selected_clause_agreement checker_agreement (by decide +kernel)
  have original := Hypothesis.proof_clause table definitions theorems context hypotheses index
  change clauses MeTTa.program "mm0:proof"
    [table, definitions, theorems, context, listValue hypotheses, Hypothesis.witness index] =
      [.evaluate inner MeTTa.proofEquation.body] at original
  simpa only [List.map_cons, List.map_nil, tableCaptured, definitionsCaptured, theoremsCaptured,
    contextCaptured, hypothesesCaptured, witnessCaptured] using original

/-- After normalization, the original source checker accepts precisely the
preterm named by the newly emitted hypothesis witness. Captured inputs stay
inert, including arbitrary signature and provenance data. -/
theorem normalized_hypothesis_returns (bindings : Subst) (state : State)
    (table definitions theorems context : Atom) (entries : List Atom)
    (prior : List Kernel.Preterm) (conclusion : Kernel.Preterm)
    (projected : ExpressionClaims entries (prior.map Data.preterm))
    (tableName definitionsName theoremsName contextName hypothesesName witnessName : String)
    (tableCaptured : applySubst bindings (.var tableName) = table)
    (definitionsCaptured : applySubst bindings (.var definitionsName) = definitions)
    (theoremsCaptured : applySubst bindings (.var theoremsName) = theorems)
    (contextCaptured : applySubst bindings (.var contextName) = context)
    (hypothesesCaptured : applySubst bindings (.var hypothesesName) = listValue ((prior ++ [conclusion]).map Data.preterm))
    (witnessCaptured : applySubst bindings (.var witnessName) = Hypothesis.witness entries.length) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof", .var tableName,
      .var definitionsName, .var theoremsName, .var contextName, .var hypothesesName, .var witnessName]) state
      (optionValue (some (Data.preterm conclusion))) := by
  have read := kernel_hypothesis_returns bindings state table definitions theorems context
    ((prior ++ [conclusion]).map Data.preterm) entries.length tableName definitionsName theoremsName
    contextName hypothesesName witnessName tableCaptured definitionsCaptured theoremsCaptured contextCaptured
    hypothesesCaptured witnessCaptured
  have length := projected.length
  simp only [List.length_map] at length
  simpa [length, List.getElem?_map] using read

/-- The newly stored chronological witness is accepted by the existing kernel
for the newly appended hypothesis, including arbitrary prior hypotheses. -/
theorem appended_hypothesis_checked (signature : Kernel.TermSignature)
    (definitions : Kernel.Definition.Signature) (theorems : Kernel.TheoremSignature)
    (context : Kernel.Context) (prior : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Kernel.ProofWitness.check signature definitions theorems context (prior ++ [conclusion])
      (.hyp prior.length) conclusion = true := by
  apply (Kernel.ProofWitness.check_iff _ _ _ _ _ _ _).mpr
  exact .hyp (by simp)

theorem appended_hypothesis_derives (signature : Kernel.TermSignature)
    (definitions : Kernel.Definition.Signature) (theorems : Kernel.TheoremSignature)
    (context : Kernel.Context) (prior : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Kernel.Derives signature definitions theorems context (prior ++ [conclusion]) conclusion :=
  Kernel.ProofWitness.check_sound (appended_hypothesis_checked signature definitions theorems context prior conclusion)


/-- A general source run introduces a hypothesis and then references the
newly stored proof. Allocation, node data, preceding entries and saved proofs
are retained exactly, even when the same expression occurs several times. -/
theorem hypothesis_cycle_supported (next arity count : Nat)
    (rest heap dummies hypotheses saved : List Atom) (allocation index start : Nat)
    (expression node : Atom)
    (found : heap[index]? = some (expressionValue allocation expression node))
    (capacity : hypotheses.length < count) :
    SupportedRun (stateValue next arity count rest heap dummies hypotheses saved)
      [MMBExecution.commandValue 18 index start (start + 1),
       MMBExecution.commandValue 22 0 (start + 1) (start + 2),
       MMBExecution.commandValue 18 heap.length (start + 2) (start + 3)]
      (some (stateValue next arity count
        (provedValue (Hypothesis.witness hypotheses.length) (expressionValue allocation expression node) :: rest)
        (heap ++ [provedValue (Hypothesis.witness hypotheses.length) (expressionValue allocation expression node)])
        dummies (hypotheses ++ [expressionValue allocation expression node]) saved)) := by
  apply SupportedRun.next (.reference found (.expression allocation expression node))
  apply SupportedRun.next
  · simpa [hypothesisResult, capacity] using
      (SupportedStep.hypothesis (next := next) (arity := arity) (count := count)
        (rest := rest) (heap := heap) (dummies := dummies) (hypotheses := hypotheses) (saved := saved)
        (allocation := allocation) (data := 0) (expression := expression) (node := node))
  · apply SupportedRun.next
    · exact .reference (by simp)
        (.proved (Hypothesis.witness hypotheses.length) (expressionValue allocation expression node))
    · exact .done _

/-- The emitted witness has its original logical meaning after the unchanged
frontend projects the hypothesis entries. This statement does not admit the
hypotheses or resolve a theorem declaration. Those are separate source guards. -/
theorem hypothesis_cycle_qualified (state : State) (resolver tables formal : Atom)
    (next arity count : Nat) (rest heap dummies hypotheses saved : List Atom)
    (allocation index start : Nat) (node : Atom)
    (signature : Kernel.TermSignature) (definitions : Kernel.Definition.Signature)
    (theorems : Kernel.TheoremSignature) (context : Kernel.Context)
    (prior : List Kernel.Preterm) (conclusion : Kernel.Preterm)
    (found : heap[index]? = some (expressionValue allocation (Data.preterm conclusion) node))
    (capacity : hypotheses.length < count)
    (projected : ExpressionClaims hypotheses (prior.map Data.preterm)) :
    (∃ fuel, ∀ extra, Eval.run program (fuel + extra)
      { state, control := .evaluate [] (.expression [.symbol "mm0:mmb:proof-run", resolver, tables, formal,
          .symbol "MM0:MMBAssertion", stateValue next arity count rest heap dummies hypotheses saved,
          listValue [MMBExecution.commandValue 18 index start (start + 1),
            MMBExecution.commandValue 22 0 (start + 1) (start + 2),
            MMBExecution.commandValue 18 heap.length (start + 2) (start + 3)]]) } =
      .complete state [optionValue (some (stateValue next arity count
        (provedValue (Hypothesis.witness hypotheses.length) (expressionValue allocation (Data.preterm conclusion) node) :: rest)
        (heap ++ [provedValue (Hypothesis.witness hypotheses.length) (expressionValue allocation (Data.preterm conclusion) node)])
        dummies (hypotheses ++ [expressionValue allocation (Data.preterm conclusion) node]) saved))] [] []) ∧
    PureReturns program [] state
      (.expression [.symbol "mm0:mmb:expression-values",
        listValue (hypotheses ++ [expressionValue allocation (Data.preterm conclusion) node])]) state
      (optionValue (some (listValue ((prior ++ [conclusion]).map Data.preterm)))) ∧
    Kernel.ProofWitness.check signature definitions theorems context (prior ++ [conclusion])
      (.hyp hypotheses.length) conclusion = true := by
  constructor
  · exact run_sufficient_fuel state resolver tables formal _ _ _
      (hypothesis_cycle_supported next arity count rest heap dummies hypotheses saved allocation index start
        (Data.preterm conclusion) node found capacity)
  constructor
  · apply expression_values_returns [] state
        (hypotheses ++ [expressionValue allocation (Data.preterm conclusion) node])
        ((prior ++ [conclusion]).map Data.preterm) _ (by simp only [applySubst_nil])
    simpa using projected.append (.cons allocation (Data.preterm conclusion) node .nil)
  · have same := projected.length
    simp only [List.length_map] at same
    rw [same]
    exact appended_hypothesis_checked signature definitions theorems context prior conclusion

end Mettapedia.Languages.MM0.MeTTa.MMBProofRunExecution
