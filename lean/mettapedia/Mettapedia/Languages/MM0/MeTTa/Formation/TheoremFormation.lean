import Mettapedia.Languages.MM0.MeTTa.Formation.StatementFormation
import Mettapedia.Languages.MM0.MeTTa.Kernel.TheoremInstantiation

/-!
# Theorem payload formation by the retained MM0 source

A formed theorem payload has a valid preceding context, provable saturated
hypotheses and a provable saturated conclusion. This does not establish a
proof or publish a theorem. The source checks the conclusion even when a
hypothesis is refused, and the execution proofs retain that order and the
resulting coherent inference cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TheoremFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm SortInfo TheoremDecl)
open ListAccess (listValue)
open ListSubstitution (expressionsValue)
open TheoremInstantiation (declarationValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 112)[111]'(by decide)
private def contextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 113)[112]'(by decide)
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def cases := casesOf equation.body
private def contextCases := casesOf contextEquation.body
private def theoremBody : Atom := (cases[0]'(by decide)).2
private def admittedContextBody : Atom := (contextCases[1]'(by decide)).2
private def environment (sorts terms : Handle) (declaration : TheoremDecl) : Subst :=
  [("valueInput", declarationValue declaration), ("table", tableValue terms), ("sorts", tableValue sorts)]
private def contextEnvironment (answer : Bool) (sorts terms : Handle) (declaration : TheoremDecl) : Subst :=
  [("conclusion", Data.preterm declaration.conclusion), ("hypotheses", expressionsValue declaration.hypotheses),
    ("context", Data.context declaration.arguments), ("table", tableValue terms),
    ("sorts", tableValue sorts), ("conditionInput", boolean answer)]

private theorem unique : program.equations.filter (fun e => e.head == "mm0:form-theorem") = [equation] := by decide
private theorem context_unique : program.equations.filter (fun e => e.head == "mm0:form-theorem-context") = [contextEquation] := by decide
private theorem formals : equation.arguments = [.var "sorts", .var "table", .var "valueInput"] := by decide
private theorem context_formals : contextEquation.arguments =
    [.var "conditionInput", .var "sorts", .var "table", .var "context", .var "hypotheses", .var "conclusion"] := by decide
private theorem shape : equation.body = .expression [.symbol "case", .var "valueInput",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [(.expression [.symbol "MM0:L",
      .expression [.symbol "MM0:Theorem", .var "context", .var "hypotheses", .var "conclusion"]], theoremBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem theorem_shape : theoremBody = .expression [.symbol "let", .var "formContextResult",
    .expression [.symbol "mm0:form-context", .var "sorts", .var "context"],
    .expression [.symbol "mm0:form-theorem-context", .var "formContextResult", .var "sorts", .var "table",
      .var "context", .var "hypotheses", .var "conclusion"]] := by decide
private theorem context_shape : contextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (contextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_cases : contextCases = [(boolean false, boolean false), (boolean true, admittedContextBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem admitted_context_shape : admittedContextBody = .expression [.symbol "let", .var "formStatementsResult",
    .expression [.symbol "mm0:form-statements", .var "sorts", .var "table", .var "context", .var "hypotheses"],
    .expression [.symbol "let", .var "formStatementResult",
      .expression [.symbol "mm0:form-statement", .var "sorts", .var "table", .var "context", .var "conclusion"],
      .expression [.symbol "mm0:form-and", .var "formStatementsResult", .var "formStatementResult"]]] := by decide

private theorem context_body_returns (answer : Bool) (sorts terms cache : Handle)
    (sortEntries : List (Nat × SortInfo)) (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      PureReturns program (contextEnvironment answer sorts terms declaration) state contextEquation.body after
        (boolean (answer && (declaration.hypotheses.all
          (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) declaration.arguments) &&
          Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) declaration.arguments declaration.conclusion))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  rw [context_shape]
  cases answer with
  | false =>
      refine ⟨state, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := contextEnvironment false sorts terms declaration
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean false) (boolean false) _ _ contextCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [context_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      obtain ⟨middle, hypothesesReturned, readyMiddle, frameHypotheses⟩ :=
        StatementFormation.list_captured_returns sorts terms cache sortEntries termEntries
          uniqueSorts uniqueTerms sortsSeparate termsSeparate declaration.arguments declaration.hypotheses state
          allocatedSorts allocatedTerms ready
      obtain ⟨after, conclusionReturned, readyAfter, frameConclusion⟩ :=
        StatementFormation.captured_returns sorts terms cache sortEntries termEntries
          uniqueSorts uniqueTerms sortsSeparate termsSeparate declaration.arguments declaration.conclusion middle
          (by rw [frameHypotheses.other sorts sortsSeparate]; exact allocatedSorts)
          (by rw [frameHypotheses.other terms termsSeparate]; exact allocatedTerms) readyMiddle
      refine ⟨after, ?_, readyAfter,
        (frameHypotheses.weaken (Nat.le_max_left _ _)).trans
          (frameConclusion.weaken (Nat.le_max_right _ _))⟩
      let bindings := contextEnvironment true sorts terms declaration
      apply case_returns program bindings bindings state state after (.var "conditionInput")
        (boolean true) admittedContextBody _ _ contextCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [context_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [admitted_context_shape]
        let hypothesesAnswer := declaration.hypotheses.all
          (Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries) declaration.arguments)
        let conclusionAnswer := Preterm.checkStatement (SortFormation.signature sortEntries) (signatureOf termEntries)
          declaration.arguments declaration.conclusion
        let checkedHypotheses := ("formStatementsResult", boolean hypothesesAnswer) :: bindings
        let checkedConclusion := ("formStatementResult", boolean conclusionAnswer) :: checkedHypotheses
        apply let_returns program bindings checkedHypotheses state middle after (.var "formStatementsResult") _ _ (boolean hypothesesAnswer) _
        · exact hypothesesReturned bindings "sorts" "table" "context" "hypotheses" rfl rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, checkedHypotheses, bindings, contextEnvironment, Subst.lookup]
        · apply let_returns program checkedHypotheses checkedConclusion middle after after (.var "formStatementResult") _ _ (boolean conclusionAnswer) _
          · exact conclusionReturned checkedHypotheses "sorts" "table" "context" "conclusion" rfl rfl rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, checkedConclusion, checkedHypotheses, bindings, contextEnvironment, Subst.lookup]
          · exact SortFormation.and_returns checkedConclusion after hypothesesAnswer conclusionAnswer
              "formStatementsResult" "formStatementResult" rfl rfl

private theorem check_shape (sorts : Kernel.SortSignature) (signature : Kernel.TermSignature) (declaration : TheoremDecl) :
    TheoremDecl.check sorts signature declaration =
      (Kernel.Context.check sorts declaration.arguments && (declaration.hypotheses.all
        (Preterm.checkStatement sorts signature declaration.arguments) &&
        Preterm.checkStatement sorts signature declaration.arguments declaration.conclusion)) := by
  simp [TheoremDecl.check, Bool.and_assoc]

theorem body_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      PureReturns program (environment sorts terms declaration) state equation.body after
        (boolean (TheoremDecl.check (SortFormation.signature sortEntries) (signatureOf termEntries) declaration)) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  let answer := Kernel.Context.check (SortFormation.signature sortEntries) declaration.arguments
  obtain ⟨after, contextReturned, readyAfter, frame⟩ := context_body_returns answer sorts terms cache
    sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate declaration state allocatedSorts allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [shape, check_shape]
  let bindings := environment sorts terms declaration
  let bound := ("conclusion", Data.preterm declaration.conclusion) ::
    ("hypotheses", expressionsValue declaration.hypotheses) :: ("context", Data.context declaration.arguments) :: bindings
  apply case_returns program bindings bound state state after (.var "valueInput")
    (declarationValue declaration) theoremBody _ _ cases (read_cases_encoded _)
  · exact variable_returns program bindings state "valueInput"
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, declarationValue, listValue,
      bound, bindings, environment, Subst.lookup]
  · rw [theorem_shape]
    let checked := ("formContextResult", boolean answer) :: bound
    apply let_returns program bound checked state state after (.var "formContextResult") _ _ (boolean answer) _
    · exact ContextFormation.context_captured_returns bound state sorts sortEntries declaration.arguments
        "sorts" "context" uniqueSorts allocatedSorts rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program checked (contextEnvironment answer sorts terms declaration) state after
        "mm0:form-theorem-context" ["formContextResult", "sorts", "table", "context", "hypotheses", "conclusion"]
        contextEquation.body _ (by decide) (by decide) (by decide) _ contextReturned (by decide)
      rw [clauses_use_only_the_named_equations, context_unique]
      simp [context_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        checked, bound, bindings, environment, applySubst, Subst.lookup, contextEnvironment]

/-- Literal constructor arguments and variable arguments use the same raw
call semantics; the retained equation's body is checked only once. -/
theorem atom_captured_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      (∀ bindings sortsArgument termsArgument declarationArgument,
        applySubst bindings sortsArgument = tableValue sorts →
        applySubst bindings termsArgument = tableValue terms →
        applySubst bindings declarationArgument = declarationValue declaration →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-theorem", sortsArgument, termsArgument, declarationArgument]) after
          (boolean (TheoremDecl.check (SortFormation.signature sortEntries) (signatureOf termEntries) declaration))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate declaration state allocatedSorts allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings sortsArgument termsArgument declarationArgument capturedSorts capturedTerms capturedDeclaration
  apply raw_call_returns program bindings state after "mm0:form-theorem"
    [sortsArgument, termsArgument, declarationArgument] _ (by decide)
    (by change ∀ index < 3, argumentIsRaw program "mm0:form-theorem" index = true; decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedSorts, capturedTerms, capturedDeclaration]
  apply authored_function_arguments_return program bindings (environment sorts terms declaration) state after
    "mm0:form-theorem" [tableValue sorts, tableValue terms, declarationValue declaration] 3
    equation.body _ (by decide) (by decide) _ computed
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

theorem captured_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after,
      (∀ bindings sortsName termsName declarationName,
        applySubst bindings (.var sortsName) = tableValue sorts →
        applySubst bindings (.var termsName) = tableValue terms →
        applySubst bindings (.var declarationName) = declarationValue declaration →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-theorem", .var sortsName, .var termsName, .var declarationName]) after
          (boolean (TheoremDecl.check (SortFormation.signature sortEntries) (signatureOf termEntries) declaration))) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := atom_captured_returns sorts terms cache sortEntries termEntries
    uniqueSorts uniqueTerms sortsSeparate termsSeparate declaration state allocatedSorts allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings sortsName termsName declarationName capturedSorts capturedTerms capturedDeclaration
  exact computed bindings (.var sortsName) (.var termsName) (.var declarationName)
    capturedSorts capturedTerms capturedDeclaration

/-! ## Completed source observations and the kernel judgment -/

def requestConfiguration (state : State) (sorts terms : Handle) (declaration : TheoremDecl) : Configuration :=
  { state, control := .evaluate (environment sorts terms declaration)
      (.expression [.symbol "mm0:form-theorem", .var "sorts", .var "table", .var "valueInput"]) }

theorem sufficient_fuel (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state sorts terms declaration) =
        .complete after [boolean (TheoremDecl.check (SortFormation.signature sortEntries) (signatureOf termEntries) declaration)] [] []) ∧
      InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  obtain ⟨after, returned, readyAfter, frame⟩ := captured_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment sorts terms declaration)
    state after _ _ (returned _ "sorts" "table" "valueInput" rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (answer : Bool) :
    TheoremDecl.check (SortFormation.signature sortEntries) (signatureOf termEntries) declaration = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms declaration) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem admissible_iff_source_accepts (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    TheoremDecl.Admissible (SortFormation.signature sortEntries) (signatureOf termEntries) declaration ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms declaration) = .complete after [boolean true] [] [] :=
  (TheoremDecl.check_iff _ _ _).symm.trans
    (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
      declaration state allocatedSorts allocatedTerms ready true)

theorem refused_iff_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    (¬ TheoremDecl.Admissible (SortFormation.signature sortEntries) (signatureOf termEntries) declaration) ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts terms declaration) = .complete after [boolean false] [] [] := by
  rw [← TheoremDecl.check_iff]
  exact Bool.eq_false_iff.symm.trans
    (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
      declaration state allocatedSorts allocatedTerms ready false)

theorem admissible_iff_gslt_path (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) :
    TheoremDecl.Admissible (SortFormation.signature sortEntries) (signatureOf termEntries) declaration ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state sorts terms declaration) (finished after [boolean true] [] []) := by
  rw [admissible_iff_source_accepts sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_frame (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration state sorts terms declaration) = .complete after answers [] []) :
    InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache after ∧
      InferenceCache.Frame cache (tableValue terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) state after := by
  obtain ⟨reference, referenceFuel, completed, readyReference, frame⟩ := sufficient_fuel sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, frame⟩

/-- An invalid preceding context refuses formation without publishing or
checking the payload's statements. -/
theorem invalid_context_source_refuses (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state)
    (invalid : ¬ Kernel.Context.WellFormed (SortFormation.signature sortEntries) declaration.arguments) :
    ∃ after fuel, run program fuel (requestConfiguration state sorts terms declaration) = .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready false).mp
  have refused : Kernel.Context.check (SortFormation.signature sortEntries) declaration.arguments = false := by
    exact Bool.eq_false_iff.mpr (fun formed => invalid ((Kernel.Context.check_iff _ _).mp formed))
  simp [TheoremDecl.check, refused]

/-- Every accepted payload meets all three declaration conditions; no proof
claim is inferred from formation. -/
theorem accepted_payload_conditions (sorts terms cache : Handle) (sortEntries : List (Nat × SortInfo))
    (termEntries : List ServiceInferenceCache.Row)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique termEntries) (sortsSeparate : sorts ≠ cache) (termsSeparate : terms ≠ cache)
    (declaration : TheoremDecl) (state : State)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read terms = some (declarationRows termEntries))
    (ready : InferenceCache.Ready (signatureOf termEntries) (tableValue terms) cache state) (after : State) (fuel : Nat)
    (returned : run program fuel (requestConfiguration state sorts terms declaration) = .complete after [boolean true] [] []) :
    Kernel.Context.WellFormed (SortFormation.signature sortEntries) declaration.arguments ∧
      (∀ expression ∈ declaration.hypotheses,
        Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) declaration.arguments expression) ∧
      Preterm.IsStatement (SortFormation.signature sortEntries) (signatureOf termEntries) declaration.arguments declaration.conclusion := by
  have admitted := (admissible_iff_source_accepts sorts terms cache sortEntries termEntries uniqueSorts uniqueTerms sortsSeparate termsSeparate
    declaration state allocatedSorts allocatedTerms ready).mpr ⟨after, fuel, returned⟩
  exact ⟨admitted.context, admitted.hypotheses, admitted.conclusion⟩

namespace Controls

private def propositionSort : SortInfo :=
  { pure := false, strict := false, provable := true, free := false }
private def sorts : List (Nat × SortInfo) := [(0, propositionSort)]
private def initial : State :=
  { core := [], next := 3,
    spaces := fun index => if index = 0 then SortFormation.rows sorts else [],
    cells := fun name => if name = InferenceCache.cell then some (Effects.handleValue (.privateSpace 2)) else none }
private def repeatedHypotheses : TheoremDecl :=
  { arguments := [.bound 0], hypotheses := [.var 0, .var 0], conclusion := .var 0 }
private def missingHypothesis : TheoremDecl :=
  { arguments := [.bound 0], hypotheses := [.var 1], conclusion := .var 0 }

private theorem unique_sorts : ∀ key, (sorts.filter fun entry => entry.1 = key).length ≤ 1 := by
  intro key
  by_cases same : 0 = key <;> simp [sorts, same]
private theorem sorts_allocated : initial.read (.privateSpace 0) = some (SortFormation.rows sorts) := by
  simp [initial, NamedSpaces.Store.read]
private theorem terms_allocated : initial.read (.privateSpace 1) = some (declarationRows []) := by
  simp [initial, NamedSpaces.Store.read, declarationRows, Store.rows]
private theorem ready : InferenceCache.Ready (signatureOf []) (tableValue (.privateSpace 1)) (.privateSpace 2) initial := by
  refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;>
    simp [initial, NamedSpaces.Store.read]

/-- Repeated assumptions remain ordered source inputs; a coherent cache may
reuse the inference result without removing either assumption. -/
theorem repeated_hypotheses_source_accepts :
    ∃ after fuel, run program fuel
      (requestConfiguration initial (.privateSpace 0) (.privateSpace 1) repeatedHypotheses) =
        .complete after [boolean true] [] [] := by
  apply (result_iff_source_returns (.privateSpace 0) (.privateSpace 1) (.privateSpace 2) sorts []
    unique_sorts (by intro key; simp) (by decide) (by decide) repeatedHypotheses initial
    sorts_allocated terms_allocated ready true).mp
  decide +kernel

/-- A declared provable conclusion does not repair an absent hypothesis
variable. The actual source completes with `False`. -/
theorem missing_hypothesis_source_refuses :
    ∃ after fuel, run program fuel
      (requestConfiguration initial (.privateSpace 0) (.privateSpace 1) missingHypothesis) =
        .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns (.privateSpace 0) (.privateSpace 1) (.privateSpace 2) sorts []
    unique_sorts (by intro key; simp) (by decide) (by decide) missingHypothesis initial
    sorts_allocated terms_allocated ready false).mp
  decide +kernel

end Controls

end Mettapedia.Languages.MM0.MeTTa.TheoremFormation
