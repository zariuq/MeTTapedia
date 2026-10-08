import Mettapedia.Languages.MM0.MeTTa.Kernel.BinderChecking

/-!
# Exact argument checking in the retained MM0 source

The source checks exact arity and each binder in order, stopping at the first
refusal. Successful inference writes only its scoped cache. The term table and
all other spaces remain unchanged throughout the argument list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ArgumentChecking

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm Binder)
open ListAccess (listValue viewValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 43)[42]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 44)[43]'(by decide)
private def nextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 45)[44]'(by decide)

private def expressionsValue (expressions : List Preterm) : Atom :=
  listValue (expressions.map Data.preterm)
private def environment (terms : Atom) (target : Context) (expressions : List Preterm) (formal : Context) : Subst :=
  [("formal", Data.context formal), ("expressions", expressionsValue expressions),
    ("target", Data.context target), ("table", terms)]
private def viewEnvironment (terms : Atom) (target : Context) (expressions : List Preterm) (formal : Context) : Subst :=
  [("target", Data.context target), ("table", terms),
    ("valueInputValue", viewValue (formal.map Data.binder)),
    ("valueInput", viewValue (expressions.map Data.preterm))]
private def nextEnvironment (answer : Bool) (terms : Atom) (target : Context)
    (expressions : List Preterm) (formal : Context) : Subst :=
  [("formal", Data.context formal), ("expressions", expressionsValue expressions),
    ("target", Data.context target), ("table", terms), ("conditionInput", boolean answer)]

private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := sourceCases viewEquation.body
private def nextCases := sourceCases nextEquation.body
private def nonemptyBody : Atom := (cases[3]'(by decide)).2

private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-arguments") = [equation] := by decide
private theorem view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-arguments-view") = [viewEquation] := by decide
private theorem next_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-arguments-next") = [nextEquation] := by decide
private theorem formals :
    equation.arguments = [.var "table", .var "target", .var "expressions", .var "formal"] := by decide
private theorem view_formals :
    viewEquation.arguments = [.var "valueInput", .var "valueInputValue", .var "table", .var "target"] := by decide
private theorem next_formals :
    nextEquation.arguments = [.var "conditionInput", .var "table", .var "target", .var "expressions", .var "formal"] := by decide
private theorem body_shape :
    equation.body = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "expressions"],
      .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "formal"],
        .expression [.symbol "mm0:check-arguments-view", .var "view", .var "view2", .var "table", .var "target"]]] := by decide
private theorem view_body_shape :
    viewEquation.body = .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem cases_shape :
    cases = [(.expression [.symbol "List:Nil", .symbol "List:Nil"], boolean true),
      (.expression [.symbol "List:Nil", .expression [.symbol "List:Cons", .var "binder", .var "formal"]], boolean false),
      (.expression [.expression [.symbol "List:Cons", .var "expression", .var "expressions"], .symbol "List:Nil"], boolean false),
      (.expression [.expression [.symbol "List:Cons", .var "expression", .var "expressions"],
        .expression [.symbol "List:Cons", .var "binder", .var "formal"]], nonemptyBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem nonempty_body_shape :
    nonemptyBody = .expression [.symbol "let", .var "binderFits",
      .expression [.symbol "mm0:check-binder", .var "table", .var "target", .var "expression", .var "binder"],
      .expression [.symbol "mm0:check-arguments-next", .var "binderFits", .var "table", .var "target",
        .var "expressions", .var "formal"]] := by decide
private theorem next_body_shape :
    nextEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (nextCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem next_cases_shape :
    nextCases = [(boolean false, boolean false),
      (boolean true, .expression [.symbol "mm0:check-arguments", .var "table", .var "target", .var "expressions", .var "formal"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem clause (terms : Atom) (target : Context) (expressions : List Preterm) (formal : Context) :
    clauses program "mm0:check-arguments" [terms, Data.context target, expressionsValue expressions, Data.context formal] =
      [.evaluate (environment terms target expressions formal) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (terms : Atom) (target : Context) (expressions : List Preterm) (formal : Context) :
    clauses program "mm0:check-arguments-view"
      [viewValue (expressions.map Data.preterm), viewValue (formal.map Data.binder), terms, Data.context target] =
      [.evaluate (viewEnvironment terms target expressions formal) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]
private theorem next_clause (answer : Bool) (terms : Atom) (target : Context)
    (expressions : List Preterm) (formal : Context) :
    clauses program "mm0:check-arguments-next"
      [boolean answer, terms, Data.context target, expressionsValue expressions, Data.context formal] =
      [.evaluate (nextEnvironment answer terms target expressions formal) nextEquation.body] := by
  rw [clauses_use_only_the_named_equations, next_unique]
  simp [next_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, nextEnvironment]

private theorem call_from_body (bindings : Subst) (terms : Atom) (target : Context)
    (expressions : List Preterm) (formal : Context) (before after : State) (answer : Atom)
    (termsName targetName expressionsName formalName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedExpressions : applySubst bindings (.var expressionsName) = expressionsValue expressions)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (computed : PureReturns program (environment terms target expressions formal) before equation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:check-arguments", .var termsName, .var targetName,
        .var expressionsName, .var formalName]) after answer := by
  apply authored_variable_call_returns program bindings (environment terms target expressions formal) before after
    "mm0:check-arguments" [termsName, targetName, expressionsName, formalName] equation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedTarget, capturedExpressions, capturedFormal] using clause terms target expressions formal

private theorem body_from_view (terms : Atom) (target : Context) (expressions : List Preterm) (formal : Context)
    (before after : State) (answer : Atom)
    (computed : PureReturns program (viewEnvironment terms target expressions formal) before viewEquation.body after answer) :
    PureReturns program (environment terms target expressions formal) before equation.body after answer := by
  rw [body_shape]
  let bindings := environment terms target expressions formal
  let viewed := ("view", viewValue (expressions.map Data.preterm)) :: bindings
  let both := ("view2", viewValue (formal.map Data.binder)) :: viewed
  apply let_returns program bindings viewed before before after (.var "view") _ _
    (viewValue (expressions.map Data.preterm)) _
  · exact ListAccess.view_captured_returns bindings before "expressions" (expressions.map Data.preterm) (by rfl)
  · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
  · apply let_returns program viewed both before before after (.var "view2") _ _ (viewValue (formal.map Data.binder)) _
    · exact ListAccess.view_captured_returns viewed before "formal" (formal.map Data.binder) (by rfl)
    · simp [SpaceSemantics.matchValue, matchAtom, both, viewed, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program both (viewEnvironment terms target expressions formal) before after
        "mm0:check-arguments-view" ["view", "view2", "table", "target"] viewEquation.body answer
        (by decide) (by decide) (by decide) _ computed (by decide)
      simpa [both, viewed, bindings, environment, applySubst, Subst.lookup] using view_clause terms target expressions formal

theorem body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target : Context) (expressions : List Preterm) (formal : Context) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (environment (tableValue handle) target expressions formal) before equation.body after
        (boolean (Kernel.Substitution.checkArguments (signatureOf entries) target expressions formal)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) before after := by
  induction expressions generalizing formal before with
  | nil =>
      refine ⟨before, body_from_view _ _ _ _ _ _ _ ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := viewEnvironment (tableValue handle) target [] formal
      rw [view_body_shape]
      cases formal with
      | nil =>
          apply case_returns program bindings bindings before before before _
            (.expression [viewValue [], viewValue []]) (boolean true) _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
          · exact grounded_returns program bindings before (.bool true)
      | cons binder binders =>
          let bound := ("formal", Data.context binders) :: ("binder", Data.binder binder) :: bindings
          apply case_returns program bindings bound before before before _
            (.expression [viewValue [], viewValue ((binder :: binders).map Data.binder)]) (boolean false)
            _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.context,
              bound, bindings, viewEnvironment, Subst.lookup]
          · exact grounded_returns program bound before (.bool false)
  | cons expression expressions ih =>
      cases formal with
      | nil =>
          refine ⟨before, body_from_view _ _ _ _ _ _ _ ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
          let bindings := viewEnvironment (tableValue handle) target (expression :: expressions) []
          let bound := ("expressions", expressionsValue expressions) :: ("expression", Data.preterm expression) :: bindings
          rw [view_body_shape]
          apply case_returns program bindings bound before before before _
            (.expression [viewValue ((expression :: expressions).map Data.preterm), viewValue []]) (boolean false)
            _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, expressionsValue,
              bound, bindings, viewEnvironment, Subst.lookup]
          · exact grounded_returns program bound before (.bool false)
      | cons binder binders =>
          obtain ⟨middle, checked, readyMiddle, frameFirst⟩ :=
            BinderChecking.returns handle cache entries uniqueRows separate target expression binder before allocated ready
          let fits := Preterm.checkBinder (signatureOf entries) target expression binder
          have tail : ∃ after,
              PureReturns program (nextEnvironment fits (tableValue handle) target expressions binders) middle
                nextEquation.body after
                (boolean (fits && Kernel.Substitution.checkArguments (signatureOf entries) target expressions binders)) ∧
              InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
              InferenceCache.Frame cache (tableValue handle) (sizeOf (expression :: expressions)) middle after := by
            rw [next_body_shape]
            cases condition : fits with
            | false =>
                refine ⟨middle, ?_, readyMiddle, InferenceCache.Frame.refl _ _ _ _⟩
                let bindings := nextEnvironment false (tableValue handle) target expressions binders
                apply case_returns program bindings bindings middle middle middle (.var "conditionInput")
                  (boolean false) (boolean false) _ _ nextCases (read_cases_encoded nextCases)
                · simpa [bindings, nextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings middle "conditionInput"
                · simp [next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
                · exact grounded_returns program bindings middle (.bool false)
            | true =>
                obtain ⟨after, computed, readyAfter, frameTail⟩ := ih binders middle
                  (by rw [frameFirst.other handle separate]; exact allocated) readyMiddle
                refine ⟨after, ?_, readyAfter, frameTail.weaken (by simp)⟩
                let bindings := nextEnvironment true (tableValue handle) target expressions binders
                apply case_returns program bindings bindings middle middle after (.var "conditionInput")
                  (boolean true) (.expression [.symbol "mm0:check-arguments", .var "table", .var "target", .var "expressions", .var "formal"])
                  _ _ nextCases (read_cases_encoded nextCases)
                · simpa [bindings, nextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings middle "conditionInput"
                · simp [next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
                · exact call_from_body bindings _ _ _ _ _ _ _ "table" "target" "expressions" "formal" rfl rfl rfl rfl computed
          obtain ⟨after, continued, readyAfter, frameLast⟩ := tail
          refine ⟨after, body_from_view _ _ _ _ _ _ _ ?_, readyAfter,
            (frameFirst.weaken (by simp; omega)).trans frameLast⟩
          let bindings := viewEnvironment (tableValue handle) target (expression :: expressions) (binder :: binders)
          let bound := ("formal", Data.context binders) :: ("binder", Data.binder binder) ::
            ("expressions", expressionsValue expressions) :: ("expression", Data.preterm expression) :: bindings
          rw [view_body_shape]
          apply case_returns program bindings bound before before after _
            (.expression [viewValue ((expression :: expressions).map Data.preterm), viewValue ((binder :: binders).map Data.binder)])
            nonemptyBody _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, expressionsValue, Data.context,
              bound, bindings, viewEnvironment, Subst.lookup]
          · rw [nonempty_body_shape]
            let computed := ("binderFits", boolean fits) :: bound
            apply let_returns program bound computed before middle after (.var "binderFits") _ _ (boolean fits) _
            · exact checked bound "table" "target" "expression" "binder" rfl rfl rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, computed, bound, bindings, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program computed (nextEnvironment fits (tableValue handle) target expressions binders)
                middle after "mm0:check-arguments-next" ["binderFits", "table", "target", "expressions", "formal"]
                nextEquation.body _ (by decide) (by decide) (by decide) _ continued (by decide)
              simpa [computed, bound, bindings, viewEnvironment, applySubst, Subst.lookup] using
                next_clause fits (tableValue handle) target expressions binders

theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target : Context) (expressions : List Preterm) (formal : Context) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName targetName expressionsName formalName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var targetName) = Data.context target →
        applySubst bindings (.var expressionsName) = expressionsValue expressions →
        applySubst bindings (.var formalName) = Data.context formal →
        PureReturns program bindings before
          (.expression [.symbol "mm0:check-arguments", .var termsName, .var targetName,
            .var expressionsName, .var formalName]) after
          (boolean (Kernel.Substitution.checkArguments (signatureOf entries) target expressions formal))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle cache entries uniqueRows separate
    target expressions formal before allocated ready
  exact ⟨after, fun bindings termsName targetName expressionsName formalName a b c d =>
    call_from_body bindings _ _ _ _ _ _ _ termsName targetName expressionsName formalName a b c d computed,
    readyAfter, frame⟩

def requestConfiguration (state : State) (handle : Handle) (target : Context)
    (expressions : List Preterm) (formal : Context) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) target expressions formal)
      (.expression [.symbol "mm0:check-arguments", .var "table", .var "target", .var "expressions", .var "formal"]) }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target : Context) (expressions : List Preterm) (formal : Context) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle target expressions formal) =
        .complete after [boolean (Kernel.Substitution.checkArguments (signatureOf entries) target expressions formal)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expressions) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate target expressions formal state allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) target expressions formal) state after _ _
    (path _ "table" "target" "expressions" "formal" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target : Context) (expressions : List Preterm) (formal : Context) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Bool) :
    Kernel.Substitution.checkArguments (signatureOf entries) target expressions formal = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle target expressions formal) =
        .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle cache entries uniqueRows separate
    target expressions formal state allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem fits_iff_source_accepts (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target : Context) (expressions : List Preterm) (formal : Context) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    List.Forall₂ (Preterm.FitsBinder (signatureOf entries) target) expressions formal ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle target expressions formal) =
        .complete after [boolean true] [] [] :=
  (Kernel.Substitution.checkArguments_iff (signatureOf entries) target expressions formal).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate target expressions formal state allocated ready true)

end Mettapedia.Languages.MM0.MeTTa.ArgumentChecking
