import Mettapedia.Languages.MM0.MeTTa.Formation.ContextFormation

/-!
# Term declaration formation in the retained MM0 source

The source admits a payload only after checking its context, result sort and
return dependencies. Formation is read-only. Fresh identifiers and sequential
publication are separate admission obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TermFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context SortInfo TermDecl)
open Store (natural)
open ListAccess (listValue)
open TableAccess (tableValue)

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 100)[99]'(by decide)
private def contextEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 101)[100]'(by decide)
private def resultEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 102)[101]'(by decide)
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def cases := casesOf equation.body
private def contextCases := casesOf contextEquation.body
private def resultCases := casesOf resultEquation.body
private def declarationBody := (cases[0]'(by decide)).2
private def admittedContextBody := (contextCases[1]'(by decide)).2
private def environment (handle : Handle) (declaration : TermDecl) : Subst :=
  [("valueInput", Data.declaration declaration), ("sorts", tableValue handle)]
private def resultEnvironment (answer : Bool) (context : Context) (deps : Finset Nat) : Subst :=
  [("deps", Data.dependencies deps), ("context", Data.context context), ("conditionInput", boolean answer)]
private def contextEnvironment (answer : Bool) (handle : Handle) (declaration : TermDecl) : Subst :=
  [("deps", Data.dependencies declaration.dependencies), ("sort", natural declaration.resultSort),
    ("context", Data.context declaration.arguments), ("sorts", tableValue handle), ("conditionInput", boolean answer)]
private theorem unique_equation : program.equations.filter (fun e => e.head == "mm0:form-term") = [equation] := by decide
private theorem context_unique : program.equations.filter (fun e => e.head == "mm0:form-term-context") = [contextEquation] := by decide
private theorem result_unique : program.equations.filter (fun e => e.head == "mm0:form-term-result") = [resultEquation] := by decide
private theorem formals : equation.arguments = [.var "sorts", .var "valueInput"] := by decide
private theorem context_formals : contextEquation.arguments = [.var "conditionInput", .var "sorts", .var "context", .var "sort", .var "deps"] := by decide
private theorem result_formals : resultEquation.arguments = [.var "conditionInput", .var "context", .var "deps"] := by decide
private theorem shape : equation.body = .expression [.symbol "case", .var "valueInput",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (listValue [.symbol "MM0:TermDecl", .var "context", .var "sort", .var "deps"], declarationBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem declaration_shape : declarationBody = .expression [.symbol "let", .var "formContextResult",
    .expression [.symbol "mm0:form-context", .var "sorts", .var "context"],
    .expression [.symbol "mm0:form-term-context", .var "formContextResult", .var "sorts", .var "context", .var "sort", .var "deps"]] := by decide
private theorem context_shape : contextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (contextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_cases : contextCases = [(boolean false, boolean false), (boolean true, admittedContextBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem admitted_context_shape : admittedContextBody = .expression [.symbol "let", .var "formSortResult",
    .expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Result"],
    .expression [.symbol "mm0:form-term-result", .var "formSortResult", .var "context", .var "deps"]] := by decide
private theorem result_shape : resultEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (resultCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem result_cases : resultCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:form-bound-indices", .var "context", .var "deps"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem result_body_returns (answer : Bool) (context : Context) (deps : Finset Nat) (state : State) :
    PureReturns program (resultEnvironment answer context deps) state resultEquation.body state
      (boolean (answer && (deps.sort (· ≤ ·)).all (Kernel.Context.isBound context))) := by
  rw [result_shape]
  cases answer with
  | false =>
      apply case_returns program (resultEnvironment false context deps) (resultEnvironment false context deps) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ resultCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [result_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      apply case_returns program (resultEnvironment true context deps) (resultEnvironment true context deps) state state state
        (.var "conditionInput") (boolean true) (.expression [.symbol "mm0:form-bound-indices", .var "context", .var "deps"])
        _ _ resultCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [result_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact ContextFormation.indices_captured_returns _ state context (deps.sort (· ≤ ·)) "context" "deps" rfl rfl

private theorem context_body_returns (answer : Bool) (handle : Handle) (entries : List (Nat × SortInfo))
    (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (contextEnvironment answer handle declaration) state contextEquation.body state
      (boolean (answer && (SortFormation.flag (SortFormation.signature entries declaration.resultSort) .result &&
        (declaration.dependencies.sort (· ≤ ·)).all (Kernel.Context.isBound declaration.arguments)))) := by
  rw [context_shape]
  cases answer with
  | false =>
      apply case_returns program (contextEnvironment false handle declaration) (contextEnvironment false handle declaration) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ contextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [context_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      let bindings := contextEnvironment true handle declaration
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        admittedContextBody _ _ contextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [context_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [admitted_context_shape]
        let result := SortFormation.flag (SortFormation.signature entries declaration.resultSort) .result
        let checked := ("formSortResult", boolean result) :: bindings
        apply let_returns program bindings checked state state state (.var "formSortResult") _ _ (boolean result) _
        · exact SortFormation.sort_use_returns bindings state handle entries declaration.resultSort .result "sorts" "sort" unique allocated rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, checked, bindings, contextEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program checked (resultEnvironment result declaration.arguments declaration.dependencies) state state "mm0:form-term-result"
            ["formSortResult", "context", "deps"] resultEquation.body _ (by decide) (by decide) (by decide) _
            (result_body_returns result declaration.arguments declaration.dependencies state) (by decide)
          rw [clauses_use_only_the_named_equations, result_unique]
          simp [result_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            checked, bindings, contextEnvironment, applySubst, Subst.lookup, resultEnvironment]

private theorem payload_check (sorts : Kernel.SortSignature) (declaration : TermDecl) :
    Kernel.TermDecl.check sorts declaration =
      (Kernel.Context.check sorts declaration.arguments && (SortFormation.flag (sorts declaration.resultSort) .result &&
        (declaration.dependencies.sort (· ≤ ·)).all (Kernel.Context.isBound declaration.arguments))) := by
  rw [ContextFormation.dependency_check]
  cases known : sorts declaration.resultSort <;> simp [Kernel.TermDecl.check, SortFormation.flag, known, Bool.and_assoc]

theorem body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (environment handle declaration) state equation.body state
      (boolean (Kernel.TermDecl.check (SortFormation.signature entries) declaration)) := by
  rw [shape]
  let bindings := environment handle declaration
  let bound := ("deps", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) ::
    ("context", Data.context declaration.arguments) :: bindings
  apply case_returns program bindings bound state state state (.var "valueInput") (Data.declaration declaration)
    declarationBody _ _ cases (read_cases_encoded _)
  · exact variable_returns program _ state "valueInput"
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      Data.declaration, bindings, bound, environment, listValue, Subst.lookup]
  · rw [declaration_shape, payload_check]
    let answer := Kernel.Context.check (SortFormation.signature entries) declaration.arguments
    let checked := ("formContextResult", boolean answer) :: bound
    apply let_returns program bound checked state state state (.var "formContextResult") _ _ (boolean answer) _
    · exact ContextFormation.context_captured_returns bound state handle entries declaration.arguments "sorts" "context" unique allocated rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program checked (contextEnvironment answer handle declaration) state state "mm0:form-term-context"
        ["formContextResult", "sorts", "context", "sort", "deps"] contextEquation.body _ (by decide) (by decide) (by decide) _
        (context_body_returns answer handle entries declaration state unique allocated) (by decide)
      rw [clauses_use_only_the_named_equations, context_unique]
      simp [context_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        checked, bound, bindings, environment, applySubst, Subst.lookup, contextEnvironment]

theorem captured_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (declaration : TermDecl) (sortsName declarationName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedDeclaration : applySubst bindings (.var declarationName) = Data.declaration declaration) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-term", .var sortsName, .var declarationName]) state
      (boolean (Kernel.TermDecl.check (SortFormation.signature entries) declaration)) := by
  apply authored_variable_call_returns program bindings (environment handle declaration) state state "mm0:form-term"
    [sortsName, declarationName] equation.body _ (by decide) (by decide) (by decide) _ (body_returns handle entries declaration state unique allocated) (by decide)
  rw [clauses_use_only_the_named_equations, unique_equation]
  simp [capturedSorts, capturedDeclaration, formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

theorem pure_result_refuses (sorts : Kernel.SortSignature) (declaration : TermDecl) (info : SortInfo)
    (known : sorts declaration.resultSort = some info) (pure : info.pure = true) :
    ¬ Kernel.TermDecl.Admissible sorts declaration := by
  intro admitted
  obtain ⟨other, returned, allowed⟩ := admitted.result
  have same := Option.some.inj (known.symm.trans returned)
  subst other
  simp [pure] at allowed

theorem regular_return_dependency_refuses (sorts : Kernel.SortSignature) (declaration : TermDecl)
    (index sort : Nat) (deps : Finset Nat)
    (known : declaration.arguments[index]? = some (.regular sort deps)) (used : index ∈ declaration.dependencies) :
    ¬ Kernel.TermDecl.Admissible sorts declaration := by
  intro admitted
  obtain ⟨_, bound⟩ := admitted.dependencies index used
  rw [known] at bound
  cases bound

def requestConfiguration (state : State) (handle : Handle) (declaration : TermDecl) : Configuration :=
  { state := state, control := .evaluate (environment handle declaration)
      (.expression [.symbol "mm0:form-term", .var "sorts", .var "valueInput"]) }

theorem sufficient_fuel (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state handle declaration) =
      .complete state [boolean (Kernel.TermDecl.check (SortFormation.signature entries) declaration)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment handle declaration) state state _ _
    (captured_returns (environment handle declaration) state handle entries declaration "sorts" "valueInput" unique allocated rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (answer : Bool) :
    Kernel.TermDecl.check (SortFormation.signature entries) declaration = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle declaration) = .complete after [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries declaration state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨state, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem admissible_iff_source_accepts (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    Kernel.TermDecl.Admissible (SortFormation.signature entries) declaration ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle declaration) = .complete after [boolean true] [] [] :=
  (Kernel.TermDecl.check_iff (SortFormation.signature entries) declaration).symm.trans
    (result_iff_source_returns handle entries declaration state unique allocated true)

theorem refused_iff_source_refuses (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    (¬ Kernel.TermDecl.Admissible (SortFormation.signature entries) declaration) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle declaration) = .complete after [boolean false] [] [] := by
  rw [← Kernel.TermDecl.check_iff]
  exact (Bool.eq_false_iff).symm.trans (result_iff_source_returns handle entries declaration state unique allocated false)

theorem admissible_iff_gslt_path (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    Kernel.TermDecl.Admissible (SortFormation.signature entries) declaration ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state handle declaration) (finished after [boolean true] [] []) := by
  rw [admissible_iff_source_accepts handle entries declaration state unique allocated]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_state_unchanged (handle : Handle) (entries : List (Nat × SortInfo)) (declaration : TermDecl) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration state handle declaration) = .complete after answers [] []) : after = state := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries declaration state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  exact (completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned).1.symm

end Mettapedia.Languages.MM0.MeTTa.TermFormation
