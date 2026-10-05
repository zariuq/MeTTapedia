import Mettapedia.Languages.MM0.MeTTa.Substitution
import Mettapedia.Languages.MM0.Kernel.Proof

/-!
# Simultaneous substitution of premises by the retained MM0 source

Each premise uses the same captured image list. Missing images produce a
completed absence, not an exhausted computation. Source traversal preserves
the order and multiplicity of premises and leaves the store unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ListSubstitution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State)
open Kernel (Preterm)
open ListAccess (listValue linkedValue optionValue viewValue)

def expressionsValue (values : List Preterm) : Atom := listValue (values.map Data.preterm)
def resultValue : Option (List Preterm) → Atom
  | none => .symbol "None"
  | some values => .expression [.symbol "MM0:Expressions", expressionsValue values]
private def imageValue (values : List Preterm) : Atom := linkedValue (values.map Data.preterm)

private def equation : SourceProgram.Equation := (kernelSource.program.equations.take 75)[74]'(by decide)
private def viewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 76)[75]'(by decide)
private def headEquation : SourceProgram.Equation := (kernelSource.program.equations.take 77)[76]'(by decide)
private def tailEquation : SourceProgram.Equation := (kernelSource.program.equations.take 78)[77]'(by decide)
private def environment (sources values : List Preterm) : Subst :=
  [("values", imageValue values), ("sources", expressionsValue sources)]
private def viewEnvironment (sources values : List Preterm) : Subst :=
  [("values", imageValue values), ("valueInput", viewValue (sources.map Data.preterm))]
private def headEnvironment (first : Option Preterm) (rest values : List Preterm) : Subst :=
  [("values", imageValue values), ("rest", expressionsValue rest), ("valueInput", optionValue (first.map Data.preterm))]
private def tailEnvironment (rest : Option (List Preterm)) (first : Preterm) : Subst :=
  [("first", Data.preterm first), ("valueInput", resultValue rest)]
private def sourceCases (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := sourceCases viewEquation.body
private def headCases := sourceCases headEquation.body
private def tailCases := sourceCases tailEquation.body
private def nilBody : Atom := (cases[0]'(by decide)).2
private def consBody : Atom := (cases[1]'(by decide)).2
private def headBody : Atom := (headCases[1]'(by decide)).2
private def tailBody : Atom := (tailCases[1]'(by decide)).2

private theorem unique : program.equations.filter (fun e => e.head == "mm0:subst-list") = [equation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:subst-list-view") = [viewEquation] := by decide
private theorem head_unique : program.equations.filter (fun e => e.head == "mm0:subst-list-head") = [headEquation] := by decide
private theorem tail_unique : program.equations.filter (fun e => e.head == "mm0:subst-list-tail") = [tailEquation] := by decide
private theorem formals : equation.arguments = [.var "sources", .var "values"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "values"] := by decide
private theorem head_formals : headEquation.arguments = [.var "valueInput", .var "rest", .var "values"] := by decide
private theorem tail_formals : tailEquation.arguments = [.var "valueInput", .var "first"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "sources"],
      .expression [.symbol "mm0:subst-list-view", .var "view", .var "values"]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem cases_shape : cases = [(.symbol "List:Nil", nilBody),
    (.expression [.symbol "List:Cons", .var "first", .var "rest"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem nil_body_shape : nilBody =
    .expression [.symbol "let", .var "items", listValue [], .expression [.symbol "MM0:Expressions", .var "items"]] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "substituted", .expression [.symbol "mm0:subst", .var "first", .var "values"],
      .expression [.symbol "mm0:subst-list-head", .var "substituted", .var "rest", .var "values"]] := by decide
private theorem head_body_shape : headEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (headCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem head_cases_shape : headCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "first"], headBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem head_some_body_shape : headBody =
    .expression [.symbol "let", .var "substListResult", .expression [.symbol "mm0:subst-list", .var "rest", .var "values"],
      .expression [.symbol "mm0:subst-list-tail", .var "substListResult", .var "first"]] := by decide
private theorem tail_body_shape : tailEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (tailCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem tail_cases_shape : tailCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Expressions", .var "rest"], tailBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem tail_some_body_shape : tailBody =
    .expression [.symbol "let", .var "extended", .expression [.symbol "mm0:list-cons", .var "first", .var "rest"],
      .expression [.symbol "MM0:Expressions", .var "extended"]] := by decide

private theorem clause (sources values : List Preterm) : clauses program "mm0:subst-list" [expressionsValue sources, imageValue values] =
    [.evaluate (environment sources values) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (sources values : List Preterm) : clauses program "mm0:subst-list-view" [viewValue (sources.map Data.preterm), imageValue values] =
    [.evaluate (viewEnvironment sources values) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]
private theorem head_clause (first : Option Preterm) (rest values : List Preterm) :
    clauses program "mm0:subst-list-head" [optionValue (first.map Data.preterm), expressionsValue rest, imageValue values] =
      [.evaluate (headEnvironment first rest values) headEquation.body] := by
  rw [clauses_use_only_the_named_equations, head_unique]
  simp [head_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, headEnvironment]
private theorem tail_clause (rest : Option (List Preterm)) (first : Preterm) :
    clauses program "mm0:subst-list-tail" [resultValue rest, Data.preterm first] =
      [.evaluate (tailEnvironment rest first) tailEquation.body] := by
  rw [clauses_use_only_the_named_equations, tail_unique]
  simp [tail_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, tailEnvironment]

private theorem call_from_body (bindings : Subst) (state : State) (sources values : List Preterm) (sourcesName valuesName : String)
    (capturedSources : applySubst bindings (.var sourcesName) = expressionsValue sources)
    (capturedValues : applySubst bindings (.var valuesName) = imageValue values)
    (computed : PureReturns program (environment sources values) state equation.body state
      (resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources))) :
    PureReturns program bindings state (.expression [.symbol "mm0:subst-list", .var sourcesName, .var valuesName]) state
      (resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources)) := by
  apply authored_variable_call_returns program bindings (environment sources values) state state
    "mm0:subst-list" [sourcesName, valuesName] equation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedSources, capturedValues] using clause sources values

theorem tail_body_returns (state : State) (rest : Option (List Preterm)) (first : Preterm) :
    PureReturns program (tailEnvironment rest first) state tailEquation.body state (resultValue (rest.map (first :: ·))) := by
  rw [tail_body_shape]
  cases rest with
  | none =>
      let bindings := tailEnvironment none first
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ tailCases (read_cases_encoded tailCases)
      · simpa [bindings, tailEnvironment, resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [tail_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some rest =>
      let bindings := tailEnvironment (some rest) first
      let bound := ("rest", expressionsValue rest) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some rest)) tailBody
        _ _ tailCases (read_cases_encoded tailCases)
      · simpa [bindings, tailEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [tail_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, resultValue, bound, bindings, tailEnvironment, Subst.lookup]
      · rw [tail_some_body_shape]
        let extended := ("extended", expressionsValue (first :: rest)) :: bound
        apply let_returns program bound extended state state state (.var "extended") _ _ (expressionsValue (first :: rest)) _
        · exact ListAccess.cons_captured_returns bound state (Data.preterm first) (rest.map Data.preterm) "first" "rest" rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, extended, bound, bindings, tailEnvironment, Subst.lookup]
        · simpa [extended, resultValue, applySubst, Subst.lookup] using
            unary_constructor_returns program extended state "MM0:Expressions" "extended" (by decide +kernel) (by decide)

private theorem head_body_returns (state : State) (first : Option Preterm) (rest values : List Preterm)
    (child : PureReturns program (environment rest values) state equation.body state
      (resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) rest))) :
    PureReturns program (headEnvironment first rest values) state headEquation.body state
      (resultValue (first.bind fun first => (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) rest).map (first :: ·))) := by
  rw [head_body_shape]
  cases first with
  | none =>
      let bindings := headEnvironment none rest values
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ headCases (read_cases_encoded headCases)
      · simpa [bindings, headEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [head_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some first =>
      let bindings := headEnvironment (some first) rest values
      let bound := ("first", Data.preterm first) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (optionValue (some (Data.preterm first))) headBody
        _ _ headCases (read_cases_encoded headCases)
      · simpa [bindings, headEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [head_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, optionValue, bound, bindings, headEnvironment, Subst.lookup]
      · rw [head_some_body_shape]
        let result := Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) rest
        let computed := ("substListResult", resultValue result) :: bound
        apply let_returns program bound computed state state state (.var "substListResult") _ _ (resultValue result) _
        · exact call_from_body bound state rest values "rest" "values" rfl rfl child
        · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, headEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program computed (tailEnvironment result first) state state
            "mm0:subst-list-tail" ["substListResult", "first"] tailEquation.body _ (by decide) (by decide) (by decide)
            _ (tail_body_returns state result first) (by decide)
          simpa [computed, bound, bindings, headEnvironment, applySubst, Subst.lookup] using tail_clause result first

theorem body_returns (state : State) (sources values : List Preterm) :
    PureReturns program (environment sources values) state equation.body state
      (resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources)) := by
  induction sources with
  | nil =>
      rw [body_shape]
      let bindings := environment [] values
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "sources" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment [] values) state state
          "mm0:subst-list-view" ["view", "values"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause [] values
        · rw [view_body_shape]
          let callee := viewEnvironment [] values
          apply case_returns program callee callee state state state (.var "valueInput") (viewValue []) nilBody
            _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, viewValue]
          · rw [nil_body_shape]
            let wrapped := ("items", listValue []) :: callee
            apply let_returns program callee wrapped state state state (.var "items") _ _ (listValue []) _
            · exact empty_constructor_returns program callee state "MM0:L" list_is_data_constructor (by decide)
            · simp [SourceProgram.matchValue, matchAtom, wrapped, callee, viewEnvironment, Subst.lookup]
            · simpa [wrapped, resultValue, expressionsValue, Kernel.Substitution.substituteList, applySubst, Subst.lookup] using
                unary_constructor_returns program wrapped state "MM0:Expressions" "items" (by decide +kernel) (by decide)
  | cons first rest ih =>
      rw [body_shape]
      let bindings := environment (first :: rest) values
      let viewed := ("view", viewValue ((first :: rest).map Data.preterm)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((first :: rest).map Data.preterm)) _
      · exact ListAccess.view_captured_returns bindings state "sources" _ rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment (first :: rest) values) state state
          "mm0:subst-list-view" ["view", "values"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause (first :: rest) values
        · rw [view_body_shape]
          let callee := viewEnvironment (first :: rest) values
          let bound := ("rest", expressionsValue rest) :: ("first", Data.preterm first) :: callee
          apply case_returns program callee bound state state state (.var "valueInput")
            (viewValue ((first :: rest).map Data.preterm)) consBody _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, expressionsValue, bound, callee, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let result := first.substitute (Kernel.Substitution.ofList values)
            let substituted := ("substituted", optionValue (result.map Data.preterm)) :: bound
            apply let_returns program bound substituted state state state (.var "substituted") _ _ (optionValue (result.map Data.preterm)) _
            · exact Substitution.subst_captured_returns bound state first values "first" "values" rfl rfl
            · simp [SourceProgram.matchValue, matchAtom, substituted, bound, callee, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program substituted (headEnvironment result rest values) state state
                "mm0:subst-list-head" ["substituted", "rest", "values"] headEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
              · simpa [substituted, bound, callee, viewEnvironment, applySubst, Subst.lookup] using head_clause result rest values
              · simpa [Kernel.Substitution.substituteList, result, Option.map_eq_bind, Function.comp_def] using head_body_returns state result rest values ih

theorem captured_returns (bindings : Subst) (state : State) (sources values : List Preterm) (sourcesName valuesName : String)
    (capturedSources : applySubst bindings (.var sourcesName) = expressionsValue sources)
    (capturedValues : applySubst bindings (.var valuesName) = imageValue values) :
    PureReturns program bindings state (.expression [.symbol "mm0:subst-list", .var sourcesName, .var valuesName]) state
      (resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources)) :=
  call_from_body bindings state sources values sourcesName valuesName capturedSources capturedValues (body_returns state sources values)

theorem resultValue_injective : Function.Injective resultValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [resultValue]
  | some first =>
      cases second with
      | none => simp [resultValue] at same
      | some second =>
          have encoded : first.map Data.preterm = second.map Data.preterm := by
            simpa [resultValue, expressionsValue, listValue] using same
          exact congrArg some ((List.map_injective_iff.mpr Data.preterm_injective) encoded)

def requestConfiguration (state : State) (sources values : List Preterm) : Configuration :=
  { state, control := .evaluate (environment sources values)
      (.expression [.symbol "mm0:subst-list", .var "sources", .var "values"]) }

theorem sufficient_fuel (state : State) (sources values : List Preterm) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state sources values) =
      .complete state [resultValue (Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment sources values) state state _ _
    (captured_returns _ state sources values "sources" "values" rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (state : State) (sources values : List Preterm) (answer : Option (List Preterm)) :
    Kernel.Substitution.substituteList (Kernel.Substitution.ofList values) sources = answer ↔
      ∃ fuel, run program fuel (requestConfiguration state sources values) = .complete state [resultValue answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state sources values
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same; exact ⟨referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference returned
    exact resultValue_injective (List.singleton_inj.mp same.2.1)

theorem substitutes_iff_source_returns (state : State) (sources values results : List Preterm) :
    List.Forall₂ (Preterm.Substitutes (Kernel.Substitution.ofList values)) sources results ↔
      ∃ fuel, run program fuel (requestConfiguration state sources values) = .complete state [resultValue (some results)] [] [] :=
  (Kernel.Substitution.substituteList_eq_some_iff (Kernel.Substitution.ofList values) sources results).symm.trans
    (result_iff_source_returns state sources values (some results))

theorem refusal_iff_source_returns_none (state : State) (sources values : List Preterm) :
    (¬ ∃ results, List.Forall₂ (Preterm.Substitutes (Kernel.Substitution.ofList values)) sources results) ↔
      ∃ fuel, run program fuel (requestConfiguration state sources values) = .complete state [.symbol "None"] [] [] :=
  (Kernel.Substitution.substituteList_none_iff (Kernel.Substitution.ofList values) sources).symm.trans
    (result_iff_source_returns state sources values none)

theorem repetitions_are_preserved (state : State) :
    ∃ fuel, run program fuel (requestConfiguration state [.var 0, .var 0] [.var 1, .term 2]) =
      .complete state [resultValue (some [.var 1, .var 1])] [] [] := by
  apply (result_iff_source_returns state [.var 0, .var 0] [.var 1, .term 2] (some [.var 1, .var 1])).mp
  rfl

theorem missing_later_image_refuses (state : State) :
    ∃ fuel, run program fuel (requestConfiguration state [.var 0, .var 1] [.term 2]) =
      .complete state [.symbol "None"] [] [] := by
  apply (result_iff_source_returns state [.var 0, .var 1] [.term 2] none).mp
  rfl

end Mettapedia.Languages.MM0.MeTTa.ListSubstitution
