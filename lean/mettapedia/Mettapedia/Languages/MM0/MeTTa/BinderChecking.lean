import Mettapedia.Languages.MM0.MeTTa.Inference
import Mettapedia.Languages.MM0.MeTTa.Scalar

/-!
# Argument binders checked by the retained MM0 source

A bound slot requires a bound context variable of its declared sort. A regular
slot requires a saturated expression of its declared sort. Dependency safety
is a separate substitution obligation. Source inference may populate its cache;
these paths retain its coherence and all other table readings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.BinderChecking

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm Binder ExpressionType)
open Store (natural)
open ListAccess (optionValue viewValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 39)[38]'(by decide)
private def sortEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 40)[39]'(by decide)
private def typeEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 41)[40]'(by decide)
private def saturatedEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 42)[41]'(by decide)

private def environment (terms : Atom) (context : Context) (expression : Preterm) (binder : Binder) : Subst :=
  [("valueInput", Data.binder binder), ("expression", Data.preterm expression),
    ("target", Data.context context), ("table", terms)]
private def sortEnvironment (result : Option Nat) (expected : Nat) : Subst :=
  [("expected", natural expected), ("valueInput", optionValue (result.map natural))]
private def typeEnvironment (result : Option ExpressionType) (expected : Nat) : Subst :=
  [("expected", natural expected), ("valueInput", Data.inferred result)]
private def saturatedEnvironment (remaining : Context) (actual expected : Nat) : Subst :=
  [("expected", natural expected), ("actual", natural actual),
    ("valueInput", viewValue (remaining.map Data.binder))]

private def sourceCases (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := sourceCases equation.body
private def sortCases := sourceCases sortEquation.body
private def typeCases := sourceCases typeEquation.body
private def saturatedCases := sourceCases saturatedEquation.body
private def boundBody : Atom := (cases[0]'(by decide)).2
private def regularBody : Atom := (cases[1]'(by decide)).2
private def inferredBody : Atom := (typeCases[1]'(by decide)).2

private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-binder") = [equation] := by decide
private theorem sort_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-sort") = [sortEquation] := by decide
private theorem type_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-type") = [typeEquation] := by decide
private theorem saturated_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-saturated") = [saturatedEquation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "target", .var "expression", .var "valueInput"] := by decide
private theorem sort_formals : sortEquation.arguments = [.var "valueInput", .var "expected"] := by decide
private theorem type_formals : typeEquation.arguments = [.var "valueInput", .var "expected"] := by decide
private theorem saturated_formals :
    saturatedEquation.arguments = [.var "valueInput", .var "actual", .var "expected"] := by decide

private theorem body_shape :
    equation.body = .expression [.symbol "case", .var "valueInput",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]], boundBody),
      (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]], regularBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem bound_body_shape :
    boundBody = .expression [.symbol "let", .var "boundSortResult",
      .expression [.symbol "mm0:bound-sort", .var "target", .var "expression"],
      .expression [.symbol "mm0:check-sort", .var "boundSortResult", .var "sort"]] := by decide
private theorem regular_body_shape :
    regularBody = .expression [.symbol "let", .var "inferred",
      .expression [.symbol "mm0:infer", .var "table", .var "target", .var "expression"],
      .expression [.symbol "mm0:check-type", .var "inferred", .var "sort"]] := by decide
private theorem sort_body_shape :
    sortEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (sortCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem sort_cases_shape :
    sortCases = [(.symbol "None", boolean false),
      (.expression [.symbol "Some", .var "actual"],
        .expression [.symbol "mm0:nat-eq", .var "actual", .var "expected"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem type_body_shape :
    typeEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (typeCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem type_cases_shape :
    typeCases = [(.symbol "None", boolean false),
      (.expression [.symbol "MM0:Inferred", .var "remaining", .var "actual"], inferredBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem inferred_body_shape :
    inferredBody = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "remaining"],
      .expression [.symbol "mm0:check-saturated", .var "view", .var "actual", .var "expected"]] := by decide
private theorem saturated_body_shape :
    saturatedEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (saturatedCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem saturated_cases_shape :
    saturatedCases = [(.symbol "List:Nil", .expression [.symbol "mm0:nat-eq", .var "actual", .var "expected"]),
      (.expression [.symbol "List:Cons", .var "first", .var "rest"], boolean false),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem sort_clause (result : Option Nat) (expected : Nat) :
    clauses program "mm0:check-sort" [optionValue (result.map natural), natural expected] =
      [.evaluate (sortEnvironment result expected) sortEquation.body] := by
  rw [clauses_use_only_the_named_equations, sort_unique]
  simp [sort_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, sortEnvironment]
private theorem type_clause (result : Option ExpressionType) (expected : Nat) :
    clauses program "mm0:check-type" [Data.inferred result, natural expected] =
      [.evaluate (typeEnvironment result expected) typeEquation.body] := by
  rw [clauses_use_only_the_named_equations, type_unique]
  simp [type_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, typeEnvironment]
private theorem saturated_clause (remaining : Context) (actual expected : Nat) :
    clauses program "mm0:check-saturated" [viewValue (remaining.map Data.binder), natural actual, natural expected] =
      [.evaluate (saturatedEnvironment remaining actual expected) saturatedEquation.body] := by
  rw [clauses_use_only_the_named_equations, saturated_unique]
  simp [saturated_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, saturatedEnvironment]

theorem sort_body_returns (state : State) (result : Option Nat) (expected : Nat) :
    PureReturns program (sortEnvironment result expected) state sortEquation.body state
      (boolean (decide (result = some expected))) := by
  rw [sort_body_shape]
  let bindings := sortEnvironment result expected
  have input : PureReturns program bindings state (.var "valueInput") state (optionValue (result.map natural)) := by
    simpa [bindings, sortEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (boolean false) _ _ sortCases (read_cases_encoded sortCases) input
      · simp [sort_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | some actual =>
      let bound := ("actual", natural actual) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (optionValue (some (natural actual))) (.expression [.symbol "mm0:nat-eq", .var "actual", .var "expected"])
        _ _ sortCases (read_cases_encoded sortCases) input
      · simp [sort_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, optionValue, bound, bindings, sortEnvironment, Subst.lookup]
      · simpa using Scalar.equality_captured_returns bound state "actual" "expected" actual expected (by rfl)
          (by simp [bound, bindings, sortEnvironment, applySubst, Subst.lookup])

private theorem saturated_body_returns (state : State) (remaining : Context) (actual expected : Nat) :
    PureReturns program (saturatedEnvironment remaining actual expected) state saturatedEquation.body state
      (boolean (decide ((remaining, actual) = ([], expected)))) := by
  rw [saturated_body_shape]
  let bindings := saturatedEnvironment remaining actual expected
  have input : PureReturns program bindings state (.var "valueInput") state (viewValue (remaining.map Data.binder)) := by
    simpa [bindings, saturatedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  cases remaining with
  | nil =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (viewValue []) (.expression [.symbol "mm0:nat-eq", .var "actual", .var "expected"])
        _ _ saturatedCases (read_cases_encoded saturatedCases) input
      · simp [saturated_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, viewValue]
      · simpa using Scalar.equality_captured_returns bindings state "actual" "expected" actual expected
          (by rfl) (by rfl)
  | cons first rest =>
      let bound := ("rest", Data.context rest) :: ("first", Data.binder first) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (viewValue ((first :: rest).map Data.binder)) (boolean false)
        _ _ saturatedCases (read_cases_encoded saturatedCases) input
      · simp [saturated_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, viewValue, Data.context, bound,
          bindings, saturatedEnvironment, Subst.lookup]
      · exact grounded_returns program bound state (.bool false)

theorem type_body_returns (state : State) (result : Option ExpressionType) (expected : Nat) :
    PureReturns program (typeEnvironment result expected) state typeEquation.body state
      (boolean (decide (result = some ([], expected)))) := by
  rw [type_body_shape]
  let bindings := typeEnvironment result expected
  have input : PureReturns program bindings state (.var "valueInput") state (Data.inferred result) := by
    simpa [bindings, typeEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (boolean false) _ _ typeCases (read_cases_encoded typeCases) input
      · simp [type_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | some result =>
      rcases result with ⟨remaining, actual⟩
      let bound := ("actual", natural actual) :: ("remaining", Data.context remaining) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.inferred (some (remaining, actual))) inferredBody _ _ typeCases (read_cases_encoded typeCases) input
      · simp [type_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, Data.inferred, bound, bindings, typeEnvironment, Subst.lookup]
      · rw [inferred_body_shape]
        let viewed := ("view", viewValue (remaining.map Data.binder)) :: bound
        apply let_returns program bound viewed state state state (.var "view") _ _
          (viewValue (remaining.map Data.binder)) _
        · exact ListAccess.view_captured_returns bound state "remaining" (remaining.map Data.binder) (by rfl)
        · simp [SourceProgram.matchValue, matchAtom, viewed, bound, bindings, typeEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program viewed (saturatedEnvironment remaining actual expected) state state
            "mm0:check-saturated" ["view", "actual", "expected"] saturatedEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [viewed, bound, bindings, typeEnvironment, applySubst, Subst.lookup] using
              saturated_clause remaining actual expected
          · simpa using saturated_body_returns state remaining actual expected

private theorem clause (terms : Atom) (context : Context) (expression : Preterm) (binder : Binder) :
    clauses program "mm0:check-binder" [terms, Data.context context, Data.preterm expression, Data.binder binder] =
      [.evaluate (environment terms context expression binder) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

/-- Bound slots only read the context, regardless of the term-table argument. -/
theorem bound_body_returns (terms : Atom) (state : State) (context : Context) (expression : Preterm) (sort : Nat) :
    PureReturns program (environment terms context expression (.bound sort)) state equation.body state
      (boolean (decide (Preterm.boundSort? context expression = some sort))) := by
  let bindings := environment terms context expression (.bound sort)
  let bound := ("sort", natural sort) :: bindings
  rw [body_shape]
  apply case_returns program bindings bound state state state (.var "valueInput") (Data.binder (.bound sort))
    boundBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Data.binder, ListAccess.listValue,
      bound, bindings, environment, Subst.lookup]
  · rw [bound_body_shape]
    let computed := ("boundSortResult", optionValue ((Preterm.boundSort? context expression).map natural)) :: bound
    apply let_returns program bound computed state state state (.var "boundSortResult") _ _
      (optionValue ((Preterm.boundSort? context expression).map natural)) _
    · exact BoundTyping.bound_sort_captured_returns bound state context expression "target" "expression"
        (by simp [bound, bindings, environment, applySubst, Subst.lookup])
        (by simp [bound, bindings, environment, applySubst, Subst.lookup])
    · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program computed (sortEnvironment (Preterm.boundSort? context expression) sort)
        state state "mm0:check-sort" ["boundSortResult", "sort"] sortEquation.body _
        (by decide) (by decide) (by decide) _ (sort_body_returns state (Preterm.boundSort? context expression) sort) (by decide)
      simpa [computed, bound, bindings, environment, applySubst, Subst.lookup] using
        sort_clause (Preterm.boundSort? context expression) sort

theorem bound_captured_returns (bindings : Subst) (state : State) (terms : Atom) (context : Context)
    (expression : Preterm) (sort : Nat) (termsName contextName expressionName binderName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression)
    (capturedBinder : applySubst bindings (.var binderName) = Data.binder (.bound sort)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:check-binder", .var termsName, .var contextName, .var expressionName, .var binderName]) state
      (boolean (decide (Preterm.boundSort? context expression = some sort))) := by
  apply authored_variable_call_returns program bindings (environment terms context expression (.bound sort)) state state
    "mm0:check-binder" [termsName, contextName, expressionName, binderName] equation.body _
    (by decide) (by decide) (by decide) _ (bound_body_returns terms state context expression sort) (by decide)
  simpa [capturedTerms, capturedContext, capturedExpression, capturedBinder] using clause terms context expression (.bound sort)

theorem body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (binder : Binder) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (environment (tableValue handle) context expression binder) before equation.body after
        (boolean (Preterm.checkBinder (signatureOf entries) context expression binder)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) before after := by
  cases binder with
  | bound sort =>
      refine ⟨before, ?_, ready, InferenceCache.Frame.refl cache (tableValue handle) (sizeOf expression) before⟩
      simpa [Preterm.checkBinder] using bound_body_returns (tableValue handle) before context expression sort
  | regular sort values =>
      obtain ⟨after, inferred, readyAfter, frame⟩ :=
        Inference.returns handle cache entries uniqueRows separate context expression before allocated ready
      refine ⟨after, ?_, readyAfter, frame⟩
      let bindings := environment (tableValue handle) context expression (.regular sort values)
      let bound := ("dependencies", Data.dependencies values) :: ("sort", natural sort) :: bindings
      rw [body_shape]
      apply case_returns program bindings bound before before after (.var "valueInput")
        (Data.binder (.regular sort values)) regularBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, Data.binder, ListAccess.listValue,
          bound, bindings, environment, Subst.lookup]
      · rw [regular_body_shape]
        let result := Preterm.infer (signatureOf entries) context expression
        let computed := ("inferred", Data.inferred result) :: bound
        apply let_returns program bound computed before after after (.var "inferred") _ _ (Data.inferred result) _
        · exact inferred bound "table" "target" "expression"
            (by simp [bound, bindings, environment, applySubst, Subst.lookup])
            (by simp [bound, bindings, environment, applySubst, Subst.lookup])
            (by simp [bound, bindings, environment, applySubst, Subst.lookup])
        · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, environment, Subst.lookup]
        · apply authored_variable_call_returns program computed (typeEnvironment result sort) after after
            "mm0:check-type" ["inferred", "sort"] typeEquation.body _
            (by decide) (by decide) (by decide) _ (type_body_returns after result sort) (by decide)
          simpa [computed, bound, bindings, environment, applySubst, Subst.lookup] using type_clause result sort

theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (binder : Binder) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName contextName expressionName binderName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionName) = Data.preterm expression →
        applySubst bindings (.var binderName) = Data.binder binder →
        PureReturns program bindings before
          (.expression [.symbol "mm0:check-binder", .var termsName, .var contextName,
            .var expressionName, .var binderName]) after
          (boolean (Preterm.checkBinder (signatureOf entries) context expression binder))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle cache entries uniqueRows separate
    context expression binder before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings termsName contextName expressionName binderName termsCaptured contextCaptured expressionCaptured binderCaptured
  apply authored_variable_call_returns program bindings (environment (tableValue handle) context expression binder)
    before after "mm0:check-binder" [termsName, contextName, expressionName, binderName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [termsCaptured, contextCaptured, expressionCaptured, binderCaptured] using
    clause (tableValue handle) context expression binder

def requestConfiguration (state : State) (handle : Handle) (context : Context)
    (expression : Preterm) (binder : Binder) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) context expression binder)
      (.expression [.symbol "mm0:check-binder", .var "table", .var "target", .var "expression", .var "valueInput"]) }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (binder : Binder) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle context expression binder) =
        .complete after [boolean (Preterm.checkBinder (signatureOf entries) context expression binder)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate context expression binder
    state allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) context expression binder) state after _ _
    (path _ "table" "target" "expression" "valueInput" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (binder : Binder) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Bool) :
    Preterm.checkBinder (signatureOf entries) context expression binder = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context expression binder) =
        .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle cache entries uniqueRows separate
    context expression binder state allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] []
      referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem fits_iff_source_accepts (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (binder : Binder) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    Preterm.FitsBinder (signatureOf entries) context expression binder ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context expression binder) =
        .complete after [boolean true] [] [] :=
  (Preterm.checkBinder_iff (signatureOf entries) context expression binder).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate context expression binder state allocated ready true)

end Mettapedia.Languages.MM0.MeTTa.BinderChecking
