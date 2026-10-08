import Mettapedia.Languages.MM0.MeTTa.Formation.SortFormation

/-!
# Dummy-sort admission in the retained MM0 source

Named parameters and fresh dummies have different restrictions. This source
traversal accepts exactly the kernel's known, non-strict, non-free dummy
sorts. It retains list order, stops on refusal and changes no store or cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.DummyFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (SortInfo)
open Store (natural)
open ListAccess (listValue viewValue)
open TableAccess (tableValue)

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 103)[102]'(by decide)
private def viewEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 104)[103]'(by decide)
private def nextEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 105)[104]'(by decide)
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def cases := casesOf viewEquation.body
private def nextCases := casesOf nextEquation.body
private def consBody := (cases[1]'(by decide)).2
private def environment (handle : Handle) (dummies : List Nat) : Subst :=
  [("dummies", listValue (dummies.map natural)), ("sorts", tableValue handle)]
private def viewEnvironment (handle : Handle) (dummies : List Nat) : Subst :=
  [("sorts", tableValue handle), ("valueInput", viewValue (dummies.map natural))]
private def nextEnvironment (answer : Bool) (handle : Handle) (dummies : List Nat) : Subst :=
  [("rest", listValue (dummies.map natural)), ("sorts", tableValue handle), ("conditionInput", boolean answer)]
private theorem equation_unique : program.equations.filter (fun e => e.head == "mm0:form-dummies") = [equation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:form-dummies-view") = [viewEquation] := by decide
private theorem next_unique : program.equations.filter (fun e => e.head == "mm0:form-dummies-next") = [nextEquation] := by decide
private theorem formals : equation.arguments = [.var "sorts", .var "dummies"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "sorts"] := by decide
private theorem next_formals : nextEquation.arguments = [.var "conditionInput", .var "sorts", .var "rest"] := by decide
private theorem shape : equation.body = .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "dummies"],
    .expression [.symbol "mm0:form-dummies-view", .var "view", .var "sorts"]] := by decide
private theorem view_shape : viewEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "sort", .var "rest"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_shape : consBody = .expression [.symbol "let", .var "formSortResult",
    .expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Dummy"],
    .expression [.symbol "mm0:form-dummies-next", .var "formSortResult", .var "sorts", .var "rest"]] := by decide
private theorem next_shape : nextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (nextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem next_cases : nextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:form-dummies", .var "sorts", .var "rest"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem call_from_body (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat)
    (sortsName dummiesName : String)
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedDummies : applySubst bindings (.var dummiesName) = listValue (dummies.map natural))
    (computed : PureReturns program (environment handle dummies) state equation.body state
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies))) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-dummies", .var sortsName, .var dummiesName]) state
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies)) := by
  apply authored_variable_call_returns program bindings (environment handle dummies) state state "mm0:form-dummies"
    [sortsName, dummiesName] equation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [capturedSorts, capturedDummies, formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

private theorem next_returns (answer : Bool) (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (computed : PureReturns program (environment handle dummies) state equation.body state
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies))) :
    PureReturns program (nextEnvironment answer handle dummies) state nextEquation.body state
      (boolean (answer && Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies)) := by
  rw [next_shape]
  cases answer with
  | false =>
      apply case_returns program (nextEnvironment false handle dummies) (nextEnvironment false handle dummies) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ nextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [next_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      apply case_returns program (nextEnvironment true handle dummies) (nextEnvironment true handle dummies) state state state
        (.var "conditionInput") (boolean true) (.expression [.symbol "mm0:form-dummies", .var "sorts", .var "rest"])
        _ _ nextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [next_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact call_from_body _ state handle entries dummies "sorts" "rest" rfl rfl computed

theorem body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (environment handle dummies) state equation.body state
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies)) := by
  induction dummies with
  | nil =>
      rw [shape]
      let bindings := environment handle []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "dummies" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment handle []) state state "mm0:form-dummies-view"
          ["view", "sorts"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, view_unique]
          simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            viewed, bindings, environment, applySubst, Subst.lookup, viewEnvironment]
        · rw [view_shape]
          apply case_returns program (viewEnvironment handle []) (viewEnvironment handle []) state state state
            (.var "valueInput") (viewValue []) (boolean true) _ _ cases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · exact grounded_returns program _ state (.bool true)
  | cons sort dummies recursive =>
      rw [shape]
      let bindings := environment handle (sort :: dummies)
      let viewed := ("view", viewValue ((sort :: dummies).map natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((sort :: dummies).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "dummies" _ rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment handle (sort :: dummies)) state state "mm0:form-dummies-view"
          ["view", "sorts"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, view_unique]
          simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            viewed, bindings, environment, applySubst, Subst.lookup, viewEnvironment]
        · rw [view_shape]
          let callee := viewEnvironment handle (sort :: dummies)
          let bound := ("rest", listValue (dummies.map natural)) :: ("sort", natural sort) :: callee
          apply case_returns program callee bound state state state (.var "valueInput") (viewValue ((sort :: dummies).map natural))
            consBody _ _ cases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, viewValue, callee, bound, viewEnvironment, Subst.lookup]
          · rw [cons_shape]
            let answer := Kernel.Definition.dummySortAllowed (SortFormation.signature entries) sort
            let checked := ("formSortResult", boolean answer) :: bound
            apply let_returns program bound checked state state state (.var "formSortResult") _ _ (boolean answer) _
            · simpa only [answer, SortFormation.useValue, SortFormation.dummy_flag] using
                SortFormation.sort_use_returns bound state handle entries sort .dummy "sorts" "sort" unique allocated rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, callee, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program checked (nextEnvironment answer handle dummies) state state "mm0:form-dummies-next"
                ["formSortResult", "sorts", "rest"] nextEquation.body _ (by decide) (by decide) (by decide) _
                (next_returns answer handle entries dummies state recursive) (by decide)
              rw [clauses_use_only_the_named_equations, next_unique]
              simp [next_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                checked, bound, callee, viewEnvironment, applySubst, Subst.lookup, nextEnvironment]

theorem captured_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat)
    (sortsName dummiesName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedDummies : applySubst bindings (.var dummiesName) = listValue (dummies.map natural)) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-dummies", .var sortsName, .var dummiesName]) state
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies)) :=
  call_from_body bindings state handle entries dummies sortsName dummiesName capturedSorts capturedDummies
    (body_returns handle entries dummies state unique allocated)

def requestConfiguration (state : State) (handle : Handle) (dummies : List Nat) : Configuration :=
  { state := state, control := .evaluate (environment handle dummies)
      (.expression [.symbol "mm0:form-dummies", .var "sorts", .var "dummies"]) }

theorem sufficient_fuel (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state handle dummies) =
      .complete state [boolean (Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment handle dummies) state state _ _
    (captured_returns (environment handle dummies) state handle entries dummies "sorts" "dummies" unique allocated rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (answer : Bool) :
    Kernel.Definition.checkDummySorts (SortFormation.signature entries) dummies = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle dummies) = .complete after [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries dummies state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨state, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem allowed_iff_source_accepts (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    (∀ sort ∈ dummies, ∃ info, SortFormation.signature entries sort = some info ∧ info.strict = false ∧ info.free = false) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle dummies) = .complete after [boolean true] [] [] :=
  (Kernel.Definition.checkDummySorts_iff (SortFormation.signature entries) dummies).symm.trans
    (result_iff_source_returns handle entries dummies state unique allocated true)

theorem refused_iff_source_refuses (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    (¬ ∀ sort ∈ dummies, ∃ info, SortFormation.signature entries sort = some info ∧ info.strict = false ∧ info.free = false) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle dummies) = .complete after [boolean false] [] [] := by
  rw [← Kernel.Definition.checkDummySorts_iff]
  exact (Bool.eq_false_iff).symm.trans (result_iff_source_returns handle entries dummies state unique allocated false)

theorem allowed_iff_gslt_path (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    (∀ sort ∈ dummies, ∃ info, SortFormation.signature entries sort = some info ∧ info.strict = false ∧ info.free = false) ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state handle dummies) (finished after [boolean true] [] []) := by
  rw [allowed_iff_source_accepts handle entries dummies state unique allocated]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_state_unchanged (handle : Handle) (entries : List (Nat × SortInfo)) (dummies : List Nat) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration state handle dummies) = .complete after answers [] []) : after = state := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries dummies state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  exact (completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned).1.symm

end Mettapedia.Languages.MM0.MeTTa.DummyFormation
