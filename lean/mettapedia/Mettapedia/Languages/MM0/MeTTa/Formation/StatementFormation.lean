import Mettapedia.Languages.MM0.MeTTa.Formation.ContextFormation
import Mettapedia.Languages.MM0.MeTTa.Kernel.Inference
import Mettapedia.Languages.MM0.MeTTa.Kernel.ListSubstitution

/-!
# Statement formation by the retained MM0 program

The retained source first infers an expression, then requires saturation and
a declared provable sort. These proofs execute those source equations and
retain the inference cache's current-signature contract. Other tables and
state cells are preserved; a completed `False` remains distinct from a fault
or an exhausted run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.StatementFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm SortInfo)
open Store (natural)
open ListAccess (listValue viewValue)
open ListSubstitution (expressionsValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 106)[105]'(by decide)
private def typeEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 107)[106]'(by decide)
private def saturatedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 108)[107]'(by decide)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def typeCases := casesOf typeEquation.body
private def saturatedCases := casesOf saturatedEquation.body
private def inferredBody : Atom := (typeCases[1]'(by decide)).2

private def environment (sorts terms : Handle) (context : Context) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("context", Data.context context),
    ("table", tableValue terms), ("sorts", tableValue sorts)]
private def typeEnvironment (sorts : Handle) (inferred : Option Kernel.ExpressionType) : Subst :=
  [("sorts", tableValue sorts), ("valueInput", Data.inferred inferred)]
private def saturatedEnvironment (sorts : Handle) (remaining : Context) (sort : Nat) : Subst :=
  [("sort", natural sort), ("sorts", tableValue sorts),
    ("valueInput", viewValue (remaining.map Data.binder))]

private def typeAnswer (sorts : Kernel.SortSignature) : Option Kernel.ExpressionType → Bool
  | some ([], sort) => SortFormation.flag (sorts sort) .statement
  | _ => false

private theorem unique : program.equations.filter (fun e => e.head == "mm0:form-statement") = [equation] := by decide
private theorem type_unique : program.equations.filter (fun e => e.head == "mm0:form-statement-type") = [typeEquation] := by decide
private theorem saturated_unique : program.equations.filter (fun e => e.head == "mm0:form-statement-saturated") = [saturatedEquation] := by decide
private theorem formals : equation.arguments = [.var "sorts", .var "table", .var "context", .var "expression"] := by decide
private theorem type_formals : typeEquation.arguments = [.var "valueInput", .var "sorts"] := by decide
private theorem saturated_formals : saturatedEquation.arguments = [.var "valueInput", .var "sorts", .var "sort"] := by decide
private theorem shape : equation.body = .expression [.symbol "let", .var "inferred",
    .expression [.symbol "mm0:infer", .var "table", .var "context", .var "expression"],
    .expression [.symbol "mm0:form-statement-type", .var "inferred", .var "sorts"]] := by decide
private theorem type_shape : typeEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (typeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem type_cases : typeCases = [(.symbol "None", boolean false),
    (.expression [.symbol "MM0:Inferred", .var "remaining", .var "sort"], inferredBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem inferred_shape : inferredBody = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "remaining"],
    .expression [.symbol "mm0:form-statement-saturated", .var "view", .var "sorts", .var "sort"]] := by decide
private theorem saturated_shape : saturatedEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (saturatedCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem saturated_cases : saturatedCases = [(.symbol "List:Nil",
      .expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Statement"]),
    (.expression [.symbol "List:Cons", .var "binder", .var "remaining"], boolean false),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem saturated_body_returns (sorts : Handle) (entries : List (Nat × SortInfo))
    (remaining : Context) (sort : Nat) (state : State)
    (uniqueSorts : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows entries)) :
    PureReturns program (saturatedEnvironment sorts remaining sort) state saturatedEquation.body state
      (boolean (typeAnswer (SortFormation.signature entries) (some (remaining, sort)))) := by
  rw [saturated_shape]
  cases remaining with
  | nil =>
      let bindings := saturatedEnvironment sorts [] sort
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "List:Nil") (.expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Statement"])
        _ _ saturatedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [saturated_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact SortFormation.sort_use_returns bindings state sorts entries sort .statement "sorts" "sort"
          uniqueSorts allocatedSorts rfl rfl
  | cons binder remaining =>
      let bindings := saturatedEnvironment sorts (binder :: remaining) sort
      let bound := ("remaining", listValue (remaining.map Data.binder)) :: ("binder", Data.binder binder) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (viewValue ((binder :: remaining).map Data.binder)) (boolean false) _ _ saturatedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [saturated_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, bound, bindings,
          saturatedEnvironment, listValue, Subst.lookup]
      · exact grounded_returns program bound state (.bool false)

private theorem saturated_captured_returns (bindings : Subst) (state : State) (sorts : Handle)
    (entries : List (Nat × SortInfo)) (remaining : Context) (sort : Nat)
    (viewName sortsName sortName : String)
    (uniqueSorts : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows entries))
    (capturedView : applySubst bindings (.var viewName) = viewValue (remaining.map Data.binder))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue sorts)
    (capturedSort : applySubst bindings (.var sortName) = natural sort) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:form-statement-saturated", .var viewName, .var sortsName, .var sortName]) state
      (boolean (typeAnswer (SortFormation.signature entries) (some (remaining, sort)))) := by
  apply authored_variable_call_returns program bindings (saturatedEnvironment sorts remaining sort)
    state state "mm0:form-statement-saturated" [viewName, sortsName, sortName]
    saturatedEquation.body _ (by decide) (by decide) (by decide) _
    (saturated_body_returns sorts entries remaining sort state uniqueSorts allocatedSorts) (by decide)
  rw [clauses_use_only_the_named_equations, saturated_unique]
  simp [capturedView, capturedSorts, capturedSort, saturated_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, saturatedEnvironment]

private theorem type_body_returns (sorts : Handle) (entries : List (Nat × SortInfo))
    (inferred : Option Kernel.ExpressionType) (state : State)
    (uniqueSorts : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows entries)) :
    PureReturns program (typeEnvironment sorts inferred) state typeEquation.body state
      (boolean (typeAnswer (SortFormation.signature entries) inferred)) := by
  rw [type_shape]
  cases inferred with
  | none =>
      let bindings := typeEnvironment sorts none
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (boolean false) _ _ typeCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [type_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | some inferred =>
      rcases inferred with ⟨remaining, sort⟩
      let bindings := typeEnvironment sorts (some (remaining, sort))
      let bound := ("sort", natural sort) :: ("remaining", Data.context remaining) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.inferred (some (remaining, sort))) inferredBody _ _ typeCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [type_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.inferred, bound, bindings,
          typeEnvironment, Subst.lookup]
      · rw [inferred_shape]
        let viewed := ("view", viewValue (remaining.map Data.binder)) :: bound
        apply let_returns program bound viewed state state state (.var "view") _ _
          (viewValue (remaining.map Data.binder)) _
        · exact ListAccess.view_captured_returns bound state "remaining" (remaining.map Data.binder) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bound, bindings, typeEnvironment, Subst.lookup]
        · exact saturated_captured_returns viewed state sorts entries remaining sort "view" "sorts" "sort"
            uniqueSorts allocatedSorts rfl rfl rfl

private theorem type_captured_returns (bindings : Subst) (state : State) (sorts : Handle)
    (entries : List (Nat × SortInfo)) (inferred : Option Kernel.ExpressionType) (valueName sortsName : String)
    (uniqueSorts : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows entries))
    (capturedValue : applySubst bindings (.var valueName) = Data.inferred inferred)
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue sorts) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:form-statement-type", .var valueName, .var sortsName]) state
      (boolean (typeAnswer (SortFormation.signature entries) inferred)) := by
  apply authored_variable_call_returns program bindings (typeEnvironment sorts inferred) state state
    "mm0:form-statement-type" [valueName, sortsName] typeEquation.body _
    (by decide) (by decide) (by decide) _ (type_body_returns sorts entries inferred state uniqueSorts allocatedSorts) (by decide)
  rw [clauses_use_only_the_named_equations, type_unique]
  simp [capturedValue, capturedSorts, type_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, typeEnvironment]

private theorem answer_eq_check (sorts : Kernel.SortSignature) (signature : Kernel.TermSignature)
    (context : Context) (expression : Preterm) :
    typeAnswer sorts (Preterm.infer signature context expression) =
      Preterm.checkStatement sorts signature context expression := by
  cases computed : Preterm.infer signature context expression with
  | none => simp [typeAnswer, Preterm.checkStatement, computed]
  | some inferred =>
      rcases inferred with ⟨remaining, sort⟩
      cases remaining with
      | cons binder remaining => simp [typeAnswer, Preterm.checkStatement, computed]
      | nil => cases known : sorts sort <;> simp [typeAnswer, Preterm.checkStatement, SortFormation.flag, computed, known]

theorem body_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      PureReturns program (environment sorts terms context expression) state equation.body after
        (boolean (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression)) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expression) state after := by
  obtain ⟨after, inferred, readyAfter, frame⟩ :=
    Inference.returns terms cache termEntries uniqueTerms termsSeparate context expression state allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [shape, ← answer_eq_check]
  let bindings := environment sorts terms context expression
  let bound := ("inferred", Data.inferred (Preterm.infer (signatureOf termEntries) context expression)) :: bindings
  apply let_returns program bindings bound state after after (.var "inferred") _ _
    (Data.inferred (Preterm.infer (signatureOf termEntries) context expression)) _
  · exact inferred bindings "table" "context" "expression" rfl rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, environment, Subst.lookup]
  · apply type_captured_returns bound after sorts sortEntries _ "inferred" "sorts" uniqueSorts
    · rw [frame.other sorts sortsSeparate]; exact allocatedSorts
    · rfl
    · rfl

theorem captured_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      (∀ bindings sortsName termsName contextName expressionName,
        applySubst bindings (.var sortsName) = tableValue sorts →
        applySubst bindings (.var termsName) = tableValue terms →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionName) = Data.preterm expression →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-statement", .var sortsName, .var termsName, .var contextName, .var expressionName]) after
          (boolean (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expression) state after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate context expression state allocatedSorts allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings sortsName termsName contextName expressionName capturedSorts capturedTerms capturedContext capturedExpression
  apply authored_variable_call_returns program bindings (environment sorts terms context expression) state after
    "mm0:form-statement" [sortsName, termsName, contextName, expressionName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, unique]
  simp [capturedSorts, capturedTerms, capturedContext, capturedExpression, formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

/-! ## Ordered lists of statements -/

private def listEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 109)[108]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 110)[109]'(by decide)
private def nextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 111)[110]'(by decide)
private def viewCases := casesOf viewEquation.body
private def nextCases := casesOf nextEquation.body
private def consBody : Atom := (viewCases[1]'(by decide)).2

private def listEnvironment (sorts terms : Handle) (context : Context) (expressions : List Preterm) : Subst :=
  [("expressions", expressionsValue expressions), ("context", Data.context context),
    ("table", tableValue terms), ("sorts", tableValue sorts)]
private def viewEnvironment (sorts terms : Handle) (context : Context) (expressions : List Preterm) : Subst :=
  [("context", Data.context context), ("table", tableValue terms), ("sorts", tableValue sorts),
    ("valueInput", viewValue (expressions.map Data.preterm))]
private def nextEnvironment (answer : Bool) (sorts terms : Handle) (context : Context) (rest : List Preterm) : Subst :=
  [("rest", expressionsValue rest), ("context", Data.context context),
    ("table", tableValue terms), ("sorts", tableValue sorts), ("conditionInput", boolean answer)]

private theorem list_unique : program.equations.filter (fun e => e.head == "mm0:form-statements") = [listEquation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:form-statements-view") = [viewEquation] := by decide
private theorem next_unique : program.equations.filter (fun e => e.head == "mm0:form-statements-next") = [nextEquation] := by decide
private theorem list_formals : listEquation.arguments = [.var "sorts", .var "table", .var "context", .var "expressions"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "sorts", .var "table", .var "context"] := by decide
private theorem next_formals : nextEquation.arguments = [.var "conditionInput", .var "sorts", .var "table", .var "context", .var "rest"] := by decide
private theorem list_shape : listEquation.body = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "expressions"],
    .expression [.symbol "mm0:form-statements-view", .var "view", .var "sorts", .var "table", .var "context"]] := by decide
private theorem view_shape : viewEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem view_cases : viewCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "expression", .var "rest"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_shape : consBody = .expression [.symbol "let", .var "formStatementResult",
    .expression [.symbol "mm0:form-statement", .var "sorts", .var "table", .var "context", .var "expression"],
    .expression [.symbol "mm0:form-statements-next", .var "formStatementResult", .var "sorts", .var "table", .var "context", .var "rest"]] := by decide
private theorem next_shape : nextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (nextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem next_cases : nextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:form-statements", .var "sorts", .var "table", .var "context", .var "rest"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem list_call_from_body (bindings : Subst) (before after : State) (sorts terms : Handle)
    (context : Context) (expressions : List Preterm) (answer : Bool)
    (sortsName termsName contextName expressionsName : String)
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue sorts)
    (capturedTerms : applySubst bindings (.var termsName) = tableValue terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpressions : applySubst bindings (.var expressionsName) = expressionsValue expressions)
    (computed : PureReturns program (listEnvironment sorts terms context expressions) before listEquation.body after (boolean answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:form-statements", .var sortsName, .var termsName, .var contextName, .var expressionsName])
      after (boolean answer) := by
  apply authored_variable_call_returns program bindings (listEnvironment sorts terms context expressions) before after
    "mm0:form-statements" [sortsName, termsName, contextName, expressionsName] listEquation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, list_unique]
  simp [capturedSorts, capturedTerms, capturedContext, capturedExpressions, list_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, listEnvironment]

private theorem list_body_of_view (before after : State) (sorts terms : Handle) (context : Context)
    (expressions : List Preterm) (answer : Bool)
    (viewReturned : PureReturns program (viewEnvironment sorts terms context expressions) before viewEquation.body after (boolean answer)) :
    PureReturns program (listEnvironment sorts terms context expressions) before listEquation.body after (boolean answer) := by
  rw [list_shape]
  let bindings := listEnvironment sorts terms context expressions
  let viewed := ("view", viewValue (expressions.map Data.preterm)) :: bindings
  apply let_returns program bindings viewed before before after (.var "view") _ _ (viewValue (expressions.map Data.preterm)) _
  · exact ListAccess.view_captured_returns bindings before "expressions" (expressions.map Data.preterm) rfl
  · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, listEnvironment, Subst.lookup]
  · apply authored_variable_call_returns program viewed (viewEnvironment sorts terms context expressions) before after
      "mm0:form-statements-view" ["view", "sorts", "table", "context"] viewEquation.body _
      (by decide) (by decide) (by decide) _ viewReturned (by decide)
    rw [clauses_use_only_the_named_equations, view_unique]
    simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      viewed, bindings, listEnvironment, applySubst, Subst.lookup, viewEnvironment]

private theorem next_call_from_body (bindings : Subst) (before after : State) (sorts terms : Handle)
    (context : Context) (rest : List Preterm) (headAnswer answer : Bool)
    (capturedAnswer : applySubst bindings (.var "formStatementResult") = boolean headAnswer)
    (capturedSorts : applySubst bindings (.var "sorts") = tableValue sorts)
    (capturedTerms : applySubst bindings (.var "table") = tableValue terms)
    (capturedContext : applySubst bindings (.var "context") = Data.context context)
    (capturedRest : applySubst bindings (.var "rest") = expressionsValue rest)
    (computed : PureReturns program (nextEnvironment headAnswer sorts terms context rest) before nextEquation.body after (boolean answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:form-statements-next", .var "formStatementResult", .var "sorts", .var "table", .var "context", .var "rest"])
      after (boolean answer) := by
  apply authored_variable_call_returns program bindings (nextEnvironment headAnswer sorts terms context rest) before after
    "mm0:form-statements-next" ["formStatementResult", "sorts", "table", "context", "rest"] nextEquation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, next_unique]
  simp [capturedAnswer, capturedSorts, capturedTerms, capturedContext, capturedRest, next_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, nextEnvironment]

/-- Traversal is in source order and stops at the first refused statement.
The child inference contracts are obtained by induction on the supplied list. -/
theorem list_body_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      PureReturns program (listEnvironment sorts terms context expressions) state listEquation.body after
        (boolean (expressions.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expressions) state after := by
  induction expressions generalizing state with
  | nil =>
      refine ⟨state, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      apply list_body_of_view
      rw [view_shape]
      let bindings := viewEnvironment sorts terms context []
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "List:Nil") (boolean true) _ _ viewCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [view_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool true)
  | cons expression rest ih =>
      obtain ⟨middle, headReturned, readyMiddle, frameHead⟩ := captured_returns sorts terms cache sortEntries termEntries
        uniqueSorts uniqueTerms sortsSeparate termsSeparate context expression state allocatedSorts allocatedTerms ready
      let checked := Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression
      have frameFirst : InferenceCache.Frame cache (tableValue terms) (sizeOf (expression :: rest)) state middle :=
        frameHead.weaken (by change sizeOf expression ≤ 1 + sizeOf expression + sizeOf rest; omega)
      have lift (after : State) (answer : Bool)
          (answerEq : (checked && rest.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context)) = answer)
          (nextReturned : PureReturns program (nextEnvironment checked sorts terms context rest) middle nextEquation.body after (boolean answer))
          (readyAfter : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after)
          (frame : InferenceCache.Frame cache (tableValue terms) (sizeOf (expression :: rest)) state after) :
          ∃ after,
            PureReturns program (listEnvironment sorts terms context (expression :: rest)) state listEquation.body after
              (boolean ((expression :: rest).all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context))) ∧
            InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
            InferenceCache.Frame cache (tableValue terms) (sizeOf (expression :: rest)) state after := by
        refine ⟨after, ?_, readyAfter, frame⟩
        change PureReturns program (listEnvironment sorts terms context (expression :: rest)) state
          listEquation.body after (boolean (checked && rest.all
            (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context)))
        rw [answerEq]
        apply list_body_of_view
        rw [view_shape]
        let bindings := viewEnvironment sorts terms context (expression :: rest)
        let bound := ("rest", expressionsValue rest) :: ("expression", Data.preterm expression) :: bindings
        apply case_returns program bindings bound state state after (.var "valueInput")
          (viewValue ((expression :: rest).map Data.preterm)) consBody _ _ viewCases (read_cases_encoded _)
        · exact variable_returns program bindings state "valueInput"
        · simp [view_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, bound, bindings, viewEnvironment, viewValue, expressionsValue, listValue, Subst.lookup]
        · rw [cons_shape]
          let checkedBindings := ("formStatementResult", boolean checked) :: bound
          apply let_returns program bound checkedBindings state middle after (.var "formStatementResult") _ _ (boolean checked) _
          · exact headReturned bound "sorts" "table" "context" "expression" rfl rfl rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, checkedBindings, bound, bindings, viewEnvironment, Subst.lookup]
          · exact next_call_from_body checkedBindings middle after sorts terms context rest checked answer
              rfl rfl rfl rfl rfl nextReturned
      cases computed : checked with
      | false =>
          apply lift middle false (by simp [computed]) _ readyMiddle frameFirst
          rw [computed, next_shape]
          let bindings := nextEnvironment false sorts terms context rest
          apply case_returns program bindings bindings middle middle middle (.var "conditionInput")
            (boolean false) (boolean false) _ _ nextCases (read_cases_encoded _)
          · exact variable_returns program bindings middle "conditionInput"
          · simp [next_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
          · exact grounded_returns program bindings middle (.bool false)
      | true =>
          obtain ⟨after, tailReturned, readyAfter, frameTail⟩ := ih middle
            (by rw [frameHead.other sorts sortsSeparate]; exact allocatedSorts)
            (by rw [frameHead.other terms termsSeparate]; exact allocatedTerms) readyMiddle
          apply lift after (rest.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context))
            (by simp [computed]) _ readyAfter
            (frameFirst.trans (frameTail.weaken (by change sizeOf rest ≤ 1 + sizeOf expression + sizeOf rest; omega)))
          rw [computed, next_shape]
          let bindings := nextEnvironment true sorts terms context rest
          apply case_returns program bindings bindings middle middle after (.var "conditionInput")
            (boolean true) (.expression [.symbol "mm0:form-statements", .var "sorts", .var "table", .var "context", .var "rest"])
            _ _ nextCases (read_cases_encoded _)
          · exact variable_returns program bindings middle "conditionInput"
          · simp [next_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
          · exact list_call_from_body bindings middle after sorts terms context rest _ "sorts" "table" "context" "rest"
              rfl rfl rfl rfl tailReturned

theorem list_captured_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      (∀ bindings sortsName termsName contextName expressionsName,
        applySubst bindings (.var sortsName) = tableValue sorts →
        applySubst bindings (.var termsName) = tableValue terms →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionsName) = expressionsValue expressions →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-statements", .var sortsName, .var termsName, .var contextName, .var expressionsName]) after
          (boolean (expressions.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context)))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expressions) state after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := list_body_returns sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate context expressions state allocatedSorts allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings sortsName termsName contextName expressionsName capturedSorts capturedTerms capturedContext capturedExpressions
  exact list_call_from_body bindings state after sorts terms context expressions _
    sortsName termsName contextName expressionsName capturedSorts capturedTerms capturedContext capturedExpressions computed

/-! ## Completed observations and admission judgments -/

def requestConfiguration (state : State) (sorts terms : Handle) (context : Context) (expression : Preterm) : Configuration :=
  { state, control := .evaluate (environment sorts terms context expression)
      (.expression [.symbol "mm0:form-statement", .var "sorts", .var "table", .var "context", .var "expression"]) }

theorem sufficient_fuel (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state sorts terms context expression) =
        .complete after [boolean (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression)] [] []) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expression) state after := by
  obtain ⟨after, returned, readyAfter, frame⟩ := captured_returns sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate context expression state allocatedSorts allocatedTerms ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment sorts terms context expression)
    state after _ _ (returned _ "sorts" "table" "context" "expression" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (answer : Bool) :
    Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate context expression state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem statement_iff_source_accepts (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean true] [] [] :=
  (Preterm.checkStatement_iff _ _ _ _).symm.trans
    (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
      context expression state allocatedSorts allocatedTerms ready true)

theorem refused_iff_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    (¬ Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression) ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean false] [] [] := by
  rw [← Preterm.checkStatement_iff]
  exact Bool.eq_false_iff.symm.trans
    (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
      context expression state allocatedSorts allocatedTerms ready false)

theorem statement_iff_gslt_path (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state sorts terms context expression) (finished after [boolean true] [] []) := by
  rw [statement_iff_source_accepts sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_frame (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration state sorts terms context expression) = .complete after answers [] []) :
    InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expression) state after := by
  obtain ⟨reference, referenceFuel, completed, readyReference, frame⟩ := sufficient_fuel sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, frame⟩

def listRequestConfiguration (state : State) (sorts terms : Handle) (context : Context) (expressions : List Preterm) : Configuration :=
  { state, control := .evaluate (listEnvironment sorts terms context expressions)
      (.expression [.symbol "mm0:form-statements", .var "sorts", .var "table", .var "context", .var "expressions"]) }

theorem list_sufficient_fuel (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (listRequestConfiguration state sorts terms context expressions) =
        .complete after [boolean (expressions.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context))] [] []) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expressions) state after := by
  obtain ⟨after, returned, readyAfter, frame⟩ := list_captured_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (listEnvironment sorts terms context expressions)
    state after _ _ (returned _ "sorts" "table" "context" "expressions" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem list_result_iff_source_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (answer : Bool) :
    expressions.all (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context) = answer ↔
      ∃ after fuel, run program fuel (listRequestConfiguration state sorts terms context expressions) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := list_sufficient_fuel sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem list_statements_iff_source_accepts (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    (∀ expression ∈ expressions, Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression) ↔
      ∃ after fuel, run program fuel (listRequestConfiguration state sorts terms context expressions) = .complete after [boolean true] [] [] := by
  rw [← list_result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready true]
  simp only [List.all_eq_true, Preterm.checkStatement_iff]

theorem list_refused_iff_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    (¬ ∀ expression ∈ expressions, Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression) ↔
      ∃ after fuel, run program fuel (listRequestConfiguration state sorts terms context expressions) = .complete after [boolean false] [] [] := by
  rw [← list_result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready false]
  simpa only [ne_eq, List.all_eq_true, Preterm.checkStatement_iff] using
    (Bool.eq_false_iff (b := expressions.all
      (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context))).symm

theorem list_statements_iff_gslt_path (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    (∀ expression ∈ expressions, Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) context expression) ↔
      ∃ after, (theory program).MultiStep (listRequestConfiguration state sorts terms context expressions) (finished after [boolean true] [] []) := by
  rw [list_statements_iff_source_accepts sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem list_completed_frame (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expressions : List Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (listRequestConfiguration state sorts terms context expressions) = .complete after answers [] []) :
    InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms) (sizeOf expressions) state after := by
  obtain ⟨reference, referenceFuel, completed, readyReference, frame⟩ := list_sufficient_fuel sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expressions state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, frame⟩

/-! ## Positive and negative statement boundaries -/

theorem saturated_provable_source_accepts (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (sort : Nat) (info : SortInfo)
    (inferred : Preterm.infer (signatureOf termEntries) context expression = some ([], sort))
    (known : SortFormation.signature sortEntries sort = some info) (provable : info.provable = true) :
    ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean true] [] [] := by
  apply (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready true).mp
  simp [Preterm.checkStatement, inferred, known, provable]

theorem unsaturated_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (binder : Kernel.Binder) (remaining : Context) (sort : Nat)
    (inferred : Preterm.infer (signatureOf termEntries) context expression = some (binder :: remaining, sort)) :
    ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready false).mp
  simp [Preterm.checkStatement, inferred]

theorem nonprovable_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (sort : Nat) (info : SortInfo)
    (inferred : Preterm.infer (signatureOf termEntries) context expression = some ([], sort))
    (known : SortFormation.signature sortEntries sort = some info) (nonprovable : info.provable = false) :
    ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready false).mp
  simp [Preterm.checkStatement, inferred, known, nonprovable]

theorem undeclared_sort_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (sort : Nat)
    (inferred : Preterm.infer (signatureOf termEntries) context expression = some ([], sort))
    (unknown : SortFormation.signature sortEntries sort = none) :
    ∃ after fuel, run program fuel (requestConfiguration state sorts terms context expression) = .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    context expression state allocatedSorts allocatedTerms ready false).mp
  simp [Preterm.checkStatement, inferred, unknown]

end Mettapedia.Languages.MM0.MeTTa.StatementFormation
