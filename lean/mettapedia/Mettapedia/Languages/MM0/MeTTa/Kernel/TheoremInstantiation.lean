import Mettapedia.Languages.MM0.MeTTa.Kernel.AdmissibleSubstitution
import Mettapedia.Languages.MM0.MeTTa.Kernel.SubstitutionValues
import Mettapedia.Languages.MM0.MeTTa.Kernel.ListSubstitution

/-!
# Theorem instances computed by the retained MM0 source

Admissible arguments are substituted simultaneously into the declared premises
and conclusion. A missing image refuses the instance. The source does not
search for premises or select a different theorem declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TheoremInstantiation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm TheoremDecl TheoremInstance)
open ListAccess (listValue linkedValue optionValue)
open ListSubstitution (expressionsValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

def declarationValue (declaration : TheoremDecl) : Atom :=
  listValue [.symbol "MM0:Theorem", Data.context declaration.arguments,
    expressionsValue declaration.hypotheses, Data.preterm declaration.conclusion]

def instanceValue : Option TheoremInstance → Atom
  | none => .symbol "None"
  | some instantiation => .expression [.symbol "MM0:Instance", expressionsValue instantiation.hypotheses, Data.preterm instantiation.conclusion]

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 158)[157]'(by decide +kernel)
private def admissibleEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 81)[80]'(by decide)
private def preparedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 82)[81]'(by decide)
private def hypothesesEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 83)[82]'(by decide)
private def conclusionEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 84)[83]'(by decide)
private def imageValue (values : List Preterm) : Atom := linkedValue (values.map Data.preterm)
private def environment (terms : Atom) (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) : Subst :=
  [("arguments", expressionsValue arguments), ("valueInput", declarationValue declaration),
    ("context", Data.context context), ("table", terms)]
private def admissibleEnvironment (answer : Bool) (hypotheses : List Preterm) (conclusion : Preterm) (arguments : List Preterm) : Subst :=
  [("arguments", expressionsValue arguments), ("conclusion", Data.preterm conclusion),
    ("hypotheses", expressionsValue hypotheses), ("conditionInput", boolean answer)]
private def preparedEnvironment (hypotheses : List Preterm) (conclusion : Preterm) (values : List Preterm) : Subst :=
  [("values", imageValue values), ("conclusion", Data.preterm conclusion), ("hypotheses", expressionsValue hypotheses)]
private def hypothesesEnvironment (hypotheses : Option (List Preterm)) (conclusion : Preterm) (values : List Preterm) : Subst :=
  [("values", imageValue values), ("conclusion", Data.preterm conclusion), ("valueInput", ListSubstitution.resultValue hypotheses)]
private def conclusionEnvironment (conclusion : Option Preterm) (hypotheses : List Preterm) : Subst :=
  [("hypotheses", expressionsValue hypotheses), ("valueInput", optionValue (conclusion.map Data.preterm))]
private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := sourceCases equation.body
private def admissibleCases := sourceCases admissibleEquation.body
private def hypothesesCases := sourceCases hypothesesEquation.body
private def conclusionCases := sourceCases conclusionEquation.body
private def admittedBody : Atom := (admissibleCases[1]'(by decide)).2
private def hypothesesBody : Atom := (hypothesesCases[1]'(by decide)).2
private def theoremBody : Atom := (cases[0]'(by decide)).2

private theorem unique : program.equations.filter (fun e => e.head == "mm0:instantiate-theorem") = [equation] := by decide
private theorem admissible_unique : program.equations.filter (fun e => e.head == "mm0:theorem-admissible") = [admissibleEquation] := by decide
private theorem prepared_unique : program.equations.filter (fun e => e.head == "mm0:theorem-prepared") = [preparedEquation] := by decide
private theorem hypotheses_unique : program.equations.filter (fun e => e.head == "mm0:theorem-hypotheses") = [hypothesesEquation] := by decide
private theorem conclusion_unique : program.equations.filter (fun e => e.head == "mm0:theorem-conclusion") = [conclusionEquation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "context", .var "valueInput", .var "arguments"] := by decide
private theorem admissible_formals : admissibleEquation.arguments = [.var "conditionInput", .var "hypotheses", .var "conclusion", .var "arguments"] := by decide
private theorem prepared_formals : preparedEquation.arguments = [.var "hypotheses", .var "conclusion", .var "values"] := by decide
private theorem hypotheses_formals : hypothesesEquation.arguments = [.var "valueInput", .var "conclusion", .var "values"] := by decide
private theorem conclusion_formals : conclusionEquation.arguments = [.var "valueInput", .var "hypotheses"] := by decide
private theorem admissible_body_shape : admissibleEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (admissibleCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem admissible_cases_shape : admissibleCases = [(boolean false, .symbol "None"), (boolean true, admittedBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem admitted_body_shape : admittedBody =
    .expression [.symbol "let", .var "substitutionValuesResult", .expression [.symbol "mm0:substitution-values", .var "arguments"],
      .expression [.symbol "mm0:theorem-prepared", .var "hypotheses", .var "conclusion", .var "substitutionValuesResult"]] := by decide
private theorem prepared_body_shape : preparedEquation.body =
    .expression [.symbol "let", .var "substListResult", .expression [.symbol "mm0:subst-list", .var "hypotheses", .var "values"],
      .expression [.symbol "mm0:theorem-hypotheses", .var "substListResult", .var "conclusion", .var "values"]] := by decide
private theorem hypotheses_body_shape : hypothesesEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (hypothesesCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem hypotheses_cases_shape : hypothesesCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Expressions", .var "hypotheses"], hypothesesBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem hypotheses_some_body_shape : hypothesesBody =
    .expression [.symbol "let", .var "substituted", .expression [.symbol "mm0:subst", .var "conclusion", .var "values"],
      .expression [.symbol "mm0:theorem-conclusion", .var "substituted", .var "hypotheses"]] := by decide
private theorem conclusion_body_shape : conclusionEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (conclusionCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem conclusion_cases_shape : conclusionCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "conclusion"], .expression [.symbol "MM0:Instance", .var "hypotheses", .var "conclusion"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun e => .expression [e.1, e.2])] := by decide
private theorem cases_shape : cases =
    [(.expression [.symbol "MM0:L", .expression [.symbol "MM0:Theorem", .var "formal", .var "hypotheses", .var "conclusion"]], theoremBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem theorem_body_shape : theoremBody =
    .expression [.symbol "let", .var "admissible", .expression [.symbol "mm0:check-admissible", .var "table", .var "formal", .var "context", .var "arguments"],
      .expression [.symbol "mm0:theorem-admissible", .var "admissible", .var "hypotheses", .var "conclusion", .var "arguments"]] := by decide

private theorem clause (terms : Atom) (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) :
    clauses program "mm0:instantiate-theorem" [terms, Data.context context, declarationValue declaration, expressionsValue arguments] =
      [.evaluate (environment terms context declaration arguments) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem admissible_clause (answer : Bool) (hypotheses : List Preterm) (conclusion : Preterm) (arguments : List Preterm) :
    clauses program "mm0:theorem-admissible" [boolean answer, expressionsValue hypotheses, Data.preterm conclusion, expressionsValue arguments] =
      [.evaluate (admissibleEnvironment answer hypotheses conclusion arguments) admissibleEquation.body] := by
  rw [clauses_use_only_the_named_equations, admissible_unique]
  simp [admissible_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, admissibleEnvironment]

private theorem prepared_clause (hypotheses : List Preterm) (conclusion : Preterm) (values : List Preterm) :
    clauses program "mm0:theorem-prepared" [expressionsValue hypotheses, Data.preterm conclusion, imageValue values] =
      [.evaluate (preparedEnvironment hypotheses conclusion values) preparedEquation.body] := by
  rw [clauses_use_only_the_named_equations, prepared_unique]
  simp [prepared_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, preparedEnvironment]
private theorem hypotheses_clause (hypotheses : Option (List Preterm)) (conclusion : Preterm) (values : List Preterm) :
    clauses program "mm0:theorem-hypotheses" [ListSubstitution.resultValue hypotheses, Data.preterm conclusion, imageValue values] =
      [.evaluate (hypothesesEnvironment hypotheses conclusion values) hypothesesEquation.body] := by
  rw [clauses_use_only_the_named_equations, hypotheses_unique]
  simp [hypotheses_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, hypothesesEnvironment]
private theorem conclusion_clause (conclusion : Option Preterm) (hypotheses : List Preterm) :
    clauses program "mm0:theorem-conclusion" [optionValue (conclusion.map Data.preterm), expressionsValue hypotheses] =
      [.evaluate (conclusionEnvironment conclusion hypotheses) conclusionEquation.body] := by
  rw [clauses_use_only_the_named_equations, conclusion_unique]
  simp [conclusion_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, conclusionEnvironment]

private theorem conclusion_body_returns (state : State) (conclusion : Option Preterm) (hypotheses : List Preterm) :
    PureReturns program (conclusionEnvironment conclusion hypotheses) state conclusionEquation.body state
      (instanceValue (conclusion.map fun conclusion => ⟨hypotheses, conclusion⟩)) := by
  rw [conclusion_body_shape]
  cases conclusion with
  | none =>
      let bindings := conclusionEnvironment none hypotheses
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ conclusionCases (read_cases_encoded conclusionCases)
      · simpa [bindings, conclusionEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [conclusion_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some conclusion =>
      let bindings := conclusionEnvironment (some conclusion) hypotheses
      let bound := ("conclusion", Data.preterm conclusion) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (optionValue (some (Data.preterm conclusion)))
        (.expression [.symbol "MM0:Instance", .var "hypotheses", .var "conclusion"]) _ _ conclusionCases (read_cases_encoded conclusionCases)
      · simpa [bindings, conclusionEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [conclusion_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, optionValue, bound, bindings, conclusionEnvironment, Subst.lookup]
      · simpa [instanceValue, bound, bindings, conclusionEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program bound state "MM0:Instance" ["hypotheses", "conclusion"] (by decide +kernel) (by decide)

private theorem hypotheses_body_returns (state : State) (hypotheses : Option (List Preterm)) (conclusion : Preterm) (values : List Preterm) :
    PureReturns program (hypothesesEnvironment hypotheses conclusion values) state hypothesesEquation.body state
      (instanceValue (hypotheses.bind fun hypotheses => (conclusion.substitute (Kernel.Substitution.ofList values)).map fun conclusion => ⟨hypotheses, conclusion⟩)) := by
  rw [hypotheses_body_shape]
  cases hypotheses with
  | none =>
      let bindings := hypothesesEnvironment none conclusion values
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ hypothesesCases (read_cases_encoded hypothesesCases)
      · simpa [bindings, hypothesesEnvironment, ListSubstitution.resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [hypotheses_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some hypotheses =>
      let bindings := hypothesesEnvironment (some hypotheses) conclusion values
      let bound := ("hypotheses", expressionsValue hypotheses) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (ListSubstitution.resultValue (some hypotheses)) hypothesesBody
        _ _ hypothesesCases (read_cases_encoded hypothesesCases)
      · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [hypotheses_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, ListSubstitution.resultValue, bound, bindings, hypothesesEnvironment, Subst.lookup]
      · rw [hypotheses_some_body_shape]
        let result := conclusion.substitute (Kernel.Substitution.ofList values)
        let substituted := ("substituted", optionValue (result.map Data.preterm)) :: bound
        apply let_returns program bound substituted state state state (.var "substituted") _ _ (optionValue (result.map Data.preterm)) _
        · exact Substitution.subst_captured_returns bound state conclusion values "conclusion" "values" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, substituted, bound, bindings, hypothesesEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program substituted (conclusionEnvironment result hypotheses) state state
            "mm0:theorem-conclusion" ["substituted", "hypotheses"] conclusionEquation.body _
            (by decide) (by decide) (by decide) _ (conclusion_body_returns state result hypotheses) (by decide)
          simpa [substituted, bound, bindings, hypothesesEnvironment, applySubst, Subst.lookup] using conclusion_clause result hypotheses

private theorem prepared_body_returns (state : State) (hypotheses : List Preterm) (conclusion : Preterm) (values : List Preterm) :
    PureReturns program (preparedEnvironment hypotheses conclusion values) state preparedEquation.body state
      (instanceValue ((Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) hypotheses).bind fun hypotheses =>
        (conclusion.substitute (Kernel.Substitution.ofList values)).map fun conclusion => ⟨hypotheses, conclusion⟩)) := by
  rw [prepared_body_shape]
  let bindings := preparedEnvironment hypotheses conclusion values
  let result := Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) hypotheses
  let substituted := ("substListResult", ListSubstitution.resultValue result) :: bindings
  apply let_returns program bindings substituted state state state (.var "substListResult") _ _ (ListSubstitution.resultValue result) _
  · exact ListSubstitution.captured_returns bindings state hypotheses values "hypotheses" "values" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, substituted, bindings, preparedEnvironment, Subst.lookup]
  · apply authored_variable_call_returns program substituted (hypothesesEnvironment result conclusion values) state state
      "mm0:theorem-hypotheses" ["substListResult", "conclusion", "values"] hypothesesEquation.body _
      (by decide) (by decide) (by decide) _ (hypotheses_body_returns state result conclusion values) (by decide)
    simpa [substituted, bindings, preparedEnvironment, applySubst, Subst.lookup] using hypotheses_clause result conclusion values

private theorem admissible_body_returns (state : State) (answer : Bool) (hypotheses : List Preterm)
    (conclusion : Preterm) (arguments : List Preterm) :
    PureReturns program (admissibleEnvironment answer hypotheses conclusion arguments) state admissibleEquation.body state
      (instanceValue (if answer then
        (Kernel.Substitution.substituteList (Kernel.Substitution.ofList arguments) hypotheses).bind fun hypotheses =>
          (conclusion.substitute (Kernel.Substitution.ofList arguments)).map fun conclusion => ⟨hypotheses, conclusion⟩
        else none)) := by
  rw [admissible_body_shape]
  cases answer with
  | false =>
      let bindings := admissibleEnvironment false hypotheses conclusion arguments
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None")
        _ _ admissibleCases (read_cases_encoded admissibleCases)
      · simpa [bindings, admissibleEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [admissible_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      let bindings := admissibleEnvironment true hypotheses conclusion arguments
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) admittedBody
        _ _ admissibleCases (read_cases_encoded admissibleCases)
      · simpa [bindings, admissibleEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [admissible_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [admitted_body_shape]
        let prepared := ("substitutionValuesResult", imageValue arguments) :: bindings
        apply let_returns program bindings prepared state state state (.var "substitutionValuesResult") _ _ (imageValue arguments) _
        · exact SubstitutionValues.captured_returns bindings state (arguments.map Data.preterm) "arguments" rfl
        · simp [SpaceSemantics.matchValue, matchAtom, prepared, bindings, admissibleEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program prepared (preparedEnvironment hypotheses conclusion arguments) state state
            "mm0:theorem-prepared" ["hypotheses", "conclusion", "substitutionValuesResult"] preparedEquation.body _
            (by decide) (by decide) (by decide) _ (prepared_body_returns state hypotheses conclusion arguments) (by decide)
          simpa [prepared, bindings, admissibleEnvironment, applySubst, Subst.lookup] using prepared_clause hypotheses conclusion arguments

/-- The actual theorem-instantiation body, including the computed dependency
check and its scoped cache writes. Substitution itself leaves the state alone. -/
theorem body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (environment (tableValue handle) context declaration arguments) before equation.body after
        (instanceValue (declaration.instantiate? (signatureOf entries) context arguments)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  obtain ⟨after, checked, readyAfter, frame⟩ := AdmissibleSubstitution.returns handle cache entries uniqueRows separate
    declaration.arguments context arguments before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [body_shape]
  let bindings := environment (tableValue handle) context declaration arguments
  let bound := ("conclusion", Data.preterm declaration.conclusion) ::
    ("hypotheses", expressionsValue declaration.hypotheses) :: ("formal", Data.context declaration.arguments) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (declarationValue declaration)
    theoremBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, declarationValue, listValue, bound, bindings, environment, Subst.lookup]
  · rw [theorem_body_shape]
    let answer := Kernel.Substitution.checkAdmissible (signatureOf entries) declaration.arguments context arguments
    let tested := ("admissible", boolean answer) :: bound
    apply let_returns program bound tested before after after (.var "admissible") _ _ (boolean answer) _
    · exact checked bound "table" "formal" "context" "arguments" rfl rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, tested, bound, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program tested
        (admissibleEnvironment answer declaration.hypotheses declaration.conclusion arguments) after after
        "mm0:theorem-admissible" ["admissible", "hypotheses", "conclusion", "arguments"] admissibleEquation.body _
        (by decide) (by decide) (by decide) _ _ (by decide)
      · simpa [tested, bound, bindings, environment, applySubst, Subst.lookup] using
          admissible_clause answer declaration.hypotheses declaration.conclusion arguments
      · simpa [Kernel.TheoremDecl.instantiate?, Option.map_eq_bind, answer] using
          admissible_body_returns after answer declaration.hypotheses declaration.conclusion arguments

theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName contextName declarationName argumentsName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var declarationName) = declarationValue declaration →
        applySubst bindings (.var argumentsName) = expressionsValue arguments →
        PureReturns program bindings before
          (.expression [.symbol "mm0:instantiate-theorem", .var termsName, .var contextName, .var declarationName, .var argumentsName]) after
          (instanceValue (declaration.instantiate? (signatureOf entries) context arguments))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle cache entries uniqueRows separate context declaration arguments before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings termsName contextName declarationName argumentsName capturedTerms capturedContext capturedDeclaration capturedArguments
  apply authored_variable_call_returns program bindings (environment (tableValue handle) context declaration arguments) before after
    "mm0:instantiate-theorem" [termsName, contextName, declarationName, argumentsName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedContext, capturedDeclaration, capturedArguments] using
    clause (tableValue handle) context declaration arguments

theorem instanceValue_injective : Function.Injective instanceValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [instanceValue]
  | some first =>
      cases second with
      | none => simp [instanceValue] at same
      | some second =>
          have parts : expressionsValue first.hypotheses = expressionsValue second.hypotheses ∧
              Data.preterm first.conclusion = Data.preterm second.conclusion := by
            simpa [instanceValue] using same
          have hypotheses : first.hypotheses = second.hypotheses :=
            (List.map_injective_iff.mpr Data.preterm_injective) (by simpa [expressionsValue, listValue] using parts.1)
          have conclusion := Data.preterm_injective parts.2
          exact congrArg some (by cases first; cases second; simp_all)

def requestConfiguration (state : State) (handle : Handle) (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) context declaration arguments)
      (.expression [.symbol "mm0:instantiate-theorem", .var "table", .var "context", .var "valueInput", .var "arguments"]) }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle context declaration arguments) =
        .complete after [instanceValue (declaration.instantiate? (signatureOf entries) context arguments)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate context declaration arguments state allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment (tableValue handle) context declaration arguments) state after _ _
    (path _ "table" "context" "valueInput" "arguments" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Option TheoremInstance) :
    declaration.instantiate? (signatureOf entries) context arguments = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context declaration arguments) = .complete after [instanceValue answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle cache entries uniqueRows separate context declaration arguments state allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact instanceValue_injective (List.singleton_inj.mp same.2.1)

theorem instantiates_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (instantiation : TheoremInstance) :
    declaration.Instantiates (signatureOf entries) context arguments instantiation ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context declaration arguments) =
        .complete after [instanceValue (some instantiation)] [] [] :=
  (Kernel.TheoremDecl.instantiate_eq_some_iff (signatureOf entries) context declaration arguments instantiation).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate context declaration arguments state allocated ready (some instantiation))

theorem refusal_iff_source_returns_none (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ ∃ instantiation, declaration.Instantiates (signatureOf entries) context arguments instantiation) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context declaration arguments) = .complete after [.symbol "None"] [] [] :=
  (Kernel.TheoremDecl.instantiate_none_iff (signatureOf entries) context declaration arguments).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate context declaration arguments state allocated ready none)

end Mettapedia.Languages.MM0.MeTTa.TheoremInstantiation
