import Mettapedia.Languages.MM0.MeTTa.Kernel.ArgumentChecking
import Mettapedia.Languages.MM0.MeTTa.Kernel.DependencyMatrix

/-!
# Complete admissible substitution in the retained MM0 source

Exact argument typing precedes the full dependency matrix. This composition
supplies the defined-support premises of independence automatically. Source
checking computes both Boolean results, retains the scoped inference cache,
and leaves every other table unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.AdmissibleSubstitution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm)
open ListAccess (listValue)
open TableAccess (tableValue declarationRows)
open SubstitutionEntries (entriesValue)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 55)[54]'(by decide)
private def typedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 56)[55]'(by decide)
private def entriesEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 57)[56]'(by decide)
private def expressionsValue (expressions : List Preterm) : Atom := listValue (expressions.map Data.preterm)
private def environment (terms : Atom) (formal target : Context) (expressions : List Preterm) : Subst :=
  [("expressions", expressionsValue expressions), ("target", Data.context target), ("formal", Data.context formal), ("table", terms)]
private def typedEnvironment (answer : Bool) (formal target : Context) (expressions : List Preterm) : Subst :=
  [("expressions", expressionsValue expressions), ("formal", Data.context formal), ("target", Data.context target), ("conditionInput", boolean answer)]
private def entriesEnvironment (target : Context) (entries : List Kernel.Substitution.Entry) : Subst :=
  [("entries", entriesValue entries), ("target", Data.context target)]
private def typedCases : SpaceSemantics.Cases :=
  match typedEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def typedBody : Atom := (typedCases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:check-admissible") = [equation] := by decide
private theorem typed_unique : program.equations.filter (fun e => e.head == "mm0:admissible-typed") = [typedEquation] := by decide
private theorem entries_unique : program.equations.filter (fun e => e.head == "mm0:admissible-entries") = [entriesEquation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "formal", .var "target", .var "expressions"] := by decide
private theorem typed_formals : typedEquation.arguments = [.var "conditionInput", .var "target", .var "formal", .var "expressions"] := by decide
private theorem entries_formals : entriesEquation.arguments = [.var "target", .var "entries"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "argumentsFit", .expression [.symbol "mm0:check-arguments", .var "table", .var "target", .var "expressions", .var "formal"],
      .expression [.symbol "mm0:admissible-typed", .var "argumentsFit", .var "target", .var "formal", .var "expressions"]] := by decide
private theorem typed_body_shape : typedEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (typedCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem typed_cases_shape : typedCases = [(boolean false, boolean false), (boolean true, typedBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem typed_true_body_shape : typedBody =
    .expression [.symbol "let", .var "entriesResult", .expression [.symbol "mm0:entries", .var "formal", .var "expressions", Store.natural 0],
      .expression [.symbol "mm0:admissible-entries", .var "target", .var "entriesResult"]] := by decide
private theorem entries_body_shape : entriesEquation.body =
    .expression [.symbol "mm0:check-rows", .var "target", .var "entries", .var "entries"] := by decide

private theorem clause (terms : Atom) (formal target : Context) (expressions : List Preterm) :
    clauses program "mm0:check-admissible" [terms, Data.context formal, Data.context target, expressionsValue expressions] =
      [.evaluate (environment terms formal target expressions) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem typed_clause (answer : Bool) (formal target : Context) (expressions : List Preterm) :
    clauses program "mm0:admissible-typed" [boolean answer, Data.context target, Data.context formal, expressionsValue expressions] =
      [.evaluate (typedEnvironment answer formal target expressions) typedEquation.body] := by
  rw [clauses_use_only_the_named_equations, typed_unique]
  simp [typed_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, typedEnvironment]
private theorem entries_clause (target : Context) (entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:admissible-entries" [Data.context target, entriesValue entries] =
      [.evaluate (entriesEnvironment target entries) entriesEquation.body] := by
  rw [clauses_use_only_the_named_equations, entries_unique]
  simp [entries_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, entriesEnvironment]

private theorem entries_body_returns (state : State) (target : Context) (entries : List Kernel.Substitution.Entry) :
    PureReturns program (entriesEnvironment target entries) state entriesEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkRow target entries))) := by
  rw [entries_body_shape]
  exact DependencyMatrix.rows_captured_returns _ state target entries entries "target" "entries" "entries" rfl rfl rfl

private theorem typed_body_returns (state : State) (answer : Bool) (formal target : Context) (expressions : List Preterm) :
    PureReturns program (typedEnvironment answer formal target expressions) state typedEquation.body state
      (boolean (answer && (Kernel.Substitution.entries formal expressions).all
        (Kernel.Substitution.checkRow target (Kernel.Substitution.entries formal expressions)))) := by
  rw [typed_body_shape]
  cases answer with
  | false =>
      let bindings := typedEnvironment false formal target expressions
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ typedCases (read_cases_encoded typedCases)
      · simpa [bindings, typedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := typedEnvironment true formal target expressions
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) typedBody
        _ _ typedCases (read_cases_encoded typedCases)
      · simpa [bindings, typedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [typed_true_body_shape]
        let entries := Kernel.Substitution.entries formal expressions
        let indexed := ("entriesResult", entriesValue entries) :: bindings
        apply let_returns program bindings indexed state state state (.var "entriesResult") _ _ (entriesValue entries) _
        · exact SubstitutionEntries.literal_index_captured_returns bindings state formal expressions 0 "formal" "expressions" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, indexed, bindings, typedEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program indexed (entriesEnvironment target entries) state state
            "mm0:admissible-entries" ["target", "entriesResult"] entriesEquation.body _
            (by decide) (by decide) (by decide) _ (entries_body_returns state target entries) (by decide)
          simpa [indexed, bindings, typedEnvironment, applySubst, Subst.lookup] using entries_clause target entries

theorem body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (formal target : Context) (expressions : List Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (environment (tableValue handle) formal target expressions) before equation.body after
        (boolean (Kernel.Substitution.checkAdmissible (signatureOf entries) formal target expressions)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) before after := by
  obtain ⟨after, checked, readyAfter, frame⟩ := ArgumentChecking.returns handle cache entries uniqueRows separate
    target expressions formal before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [body_shape]
  let bindings := environment (tableValue handle) formal target expressions
  let answer := Kernel.Substitution.checkArguments (signatureOf entries) target expressions formal
  let typed := ("argumentsFit", boolean answer) :: bindings
  apply let_returns program bindings typed before after after (.var "argumentsFit") _ _ (boolean answer) _
  · exact checked bindings "table" "target" "expressions" "formal" rfl rfl rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, typed, bindings, environment, Subst.lookup]
  · apply authored_variable_call_returns program typed (typedEnvironment answer formal target expressions) after after
      "mm0:admissible-typed" ["argumentsFit", "target", "formal", "expressions"] typedEquation.body _
      (by decide) (by decide) (by decide) _ (typed_body_returns after answer formal target expressions) (by decide)
    simpa [typed, bindings, environment, applySubst, Subst.lookup] using typed_clause answer formal target expressions

theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (formal target : Context) (expressions : List Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName formalName targetName expressionsName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var formalName) = Data.context formal →
        applySubst bindings (.var targetName) = Data.context target →
        applySubst bindings (.var expressionsName) = expressionsValue expressions →
        PureReturns program bindings before
          (.expression [.symbol "mm0:check-admissible", .var termsName, .var formalName, .var targetName, .var expressionsName]) after
          (boolean (Kernel.Substitution.checkAdmissible (signatureOf entries) formal target expressions))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle cache entries uniqueRows separate formal target expressions before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings termsName formalName targetName expressionsName capturedTerms capturedFormal capturedTarget capturedExpressions
  apply authored_variable_call_returns program bindings (environment (tableValue handle) formal target expressions) before after
    "mm0:check-admissible" [termsName, formalName, targetName, expressionsName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedFormal, capturedTarget, capturedExpressions] using clause (tableValue handle) formal target expressions

def requestConfiguration (state : State) (handle : Handle) (formal target : Context) (expressions : List Preterm) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) formal target expressions)
      (.expression [.symbol "mm0:check-admissible", .var "table", .var "formal", .var "target", .var "expressions"]) }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (formal target : Context) (expressions : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle formal target expressions) =
        .complete after [boolean (Kernel.Substitution.checkAdmissible (signatureOf entries) formal target expressions)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate formal target expressions state allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment (tableValue handle) formal target expressions) state after _ _
    (path _ "table" "formal" "target" "expressions" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (formal target : Context) (expressions : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Bool) :
    Kernel.Substitution.checkAdmissible (signatureOf entries) formal target expressions = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle formal target expressions) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle cache entries uniqueRows separate formal target expressions state allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem admissible_iff_source_accepts (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (formal target : Context) (expressions : List Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    Kernel.Substitution.Admissible (signatureOf entries) formal target expressions ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle formal target expressions) = .complete after [boolean true] [] [] :=
  (Kernel.Substitution.checkAdmissible_iff (signatureOf entries) formal target expressions).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate formal target expressions state allocated ready true)

end Mettapedia.Languages.MM0.MeTTa.AdmissibleSubstitution
