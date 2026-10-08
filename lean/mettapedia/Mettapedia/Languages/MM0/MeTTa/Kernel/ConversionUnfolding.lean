import Mettapedia.Languages.MM0.MeTTa.Kernel.ConversionResults
import Mettapedia.Languages.MM0.MeTTa.Kernel.Unfolding

/-!
# Typed definition conversion in the retained MM0 source

An unfolded body is not yet a conversion result. The source infers its actual
type and requires saturation at the declared result sort. The definition and
term rows are frozen; the concrete cache remains coherent across both checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ConversionUnfolding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm TermDecl)
open Store (natural)
open ListAccess (listValue optionValue)
open ListSubstitution (expressionsValue)
open Support (indicesValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open ConversionResults (resultValue)

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 28)[27]'(by decide)
private def resultEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 29)[28]'(by decide)
private def environment (declaration : Option TermDecl) (terms definitions : Atom) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Subst :=
  [("images", indicesValue images), ("arguments", expressionsValue arguments), ("symbol", natural symbol),
    ("context", Data.context context), ("definitions", definitions), ("table", terms),
    ("valueInput", optionValue (declaration.map Data.declaration))]
private def resultEnvironment (unfolded : Option Preterm) (terms : Atom) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (sort : Nat) : Subst :=
  [("sort", natural sort), ("arguments", expressionsValue arguments), ("symbol", natural symbol),
    ("context", Data.context context), ("table", terms), ("valueInput", optionValue (unfolded.map Data.preterm))]
private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := sourceCases equation.body
private def resultCases := sourceCases resultEquation.body
private def declaredBody : Atom := (cases[1]'(by decide)).2
private def unfoldedBody : Atom := (resultCases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:conversion-unfold-declaration") = [equation] := by decide
private theorem result_unique : program.equations.filter (fun e => e.head == "mm0:conversion-unfold-result") = [resultEquation] := by decide
private theorem formals : equation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "context", .var "symbol", .var "arguments", .var "images"] := by decide
private theorem result_formals : resultEquation.arguments = [.var "valueInput", .var "table", .var "context", .var "symbol", .var "arguments", .var "sort"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun e => .expression [e.1,e.2])] := by decide
private theorem cases_shape : cases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", listValue [.symbol "MM0:TermDecl", .var "formal", .var "sort", .var "dependencies"]], declaredBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem declared_body_shape : declaredBody =
    .expression [.symbol "let", .var "unfoldResult", .expression [.symbol "mm0:unfold", .var "table", .var "definitions", .var "context", .var "symbol", .var "arguments", .var "images"],
      .expression [.symbol "mm0:conversion-unfold-result", .var "unfoldResult", .var "table", .var "context", .var "symbol", .var "arguments", .var "sort"]] := by decide
private theorem result_body_shape : resultEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (resultCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem result_cases_shape : resultCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "result"], unfoldedBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem unfolded_body_shape : unfoldedBody =
    .expression [.symbol "let", .var "equal", .expression [.symbol "let", .var "inferred", .expression [.symbol "mm0:infer", .var "table", .var "context", .var "result"],
      .expression [.symbol "let", .var "inferred2", .expression [.symbol "let", .var "items", listValue [], .expression [.symbol "MM0:Inferred", .var "items", .var "sort"]],
        .expression [.symbol "mm0:data-eq", .var "inferred", .var "inferred2"]]],
      .expression [.symbol "mm0:conversion-unfold-typed", .var "equal", .var "symbol", .var "arguments", .var "result", .var "sort"]] := by decide
private theorem clause (declaration : Option TermDecl) (terms definitions : Atom) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    clauses program "mm0:conversion-unfold-declaration" [optionValue (declaration.map Data.declaration), terms, definitions, Data.context context,
      natural symbol, expressionsValue arguments, indicesValue images] =
      [.evaluate (environment declaration terms definitions context symbol arguments images) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem result_clause (unfolded : Option Preterm) (terms : Atom) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (sort : Nat) :
    clauses program "mm0:conversion-unfold-result" [optionValue (unfolded.map Data.preterm), terms, Data.context context,
      natural symbol, expressionsValue arguments, natural sort] =
      [.evaluate (resultEnvironment unfolded terms context symbol arguments sort) resultEquation.body] := by
  rw [clauses_use_only_the_named_equations, result_unique]
  simp [result_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, resultEnvironment]

private theorem result_body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (symbol : Nat) (arguments : List Preterm) (sort : Nat) (unfolded : Option Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound, PureReturns program (resultEnvironment unfolded (tableValue handle) context symbol arguments sort)
      before resultEquation.body after
        (resultValue (unfolded.bind fun result => if Preterm.infer (signatureOf entries) context result = some ([], sort) then
          some ⟨Preterm.applyArgs (.term symbol) arguments, result, sort⟩ else none)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  rw [result_body_shape]
  cases unfolded with
  | none =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := resultEnvironment none (tableValue handle) context symbol arguments sort
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None") (.symbol "None") _ _ resultCases (read_cases_encoded resultCases)
      · simpa [bindings, resultEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [result_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some result =>
      obtain ⟨after, inferred, readyAfter, frame⟩ := Inference.returns handle cache entries uniqueRows separate context result before allocated ready
      refine ⟨after, sizeOf result, ?_, readyAfter, frame⟩
      let bindings := resultEnvironment (some result) (tableValue handle) context symbol arguments sort
      let bound := ("result", Data.preterm result) :: bindings
      apply case_returns program bindings bound before before after (.var "valueInput") (optionValue (some (Data.preterm result))) unfoldedBody _ _ resultCases (read_cases_encoded resultCases)
      · simpa [bindings, resultEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [result_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, optionValue, bound, bindings, resultEnvironment, Subst.lookup]
      · rw [unfolded_body_shape]
        let answer := decide (Preterm.infer (signatureOf entries) context result = some ([], sort))
        let tested := ("equal", boolean answer) :: bound
        apply let_returns program bound tested before after after (.var "equal") _ _ (boolean answer) _
        · let actual := Data.inferred (Preterm.infer (signatureOf entries) context result)
          let withActual := ("inferred", actual) :: bound
          let expected := Data.inferred (some ([], sort))
          let withExpected := ("inferred2", expected) :: withActual
          apply let_returns program bound withActual before after after (.var "inferred") _ _ actual _
          · exact inferred bound "table" "context" "result" rfl rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, withActual, bound, bindings, resultEnvironment, Subst.lookup]
          · apply let_returns program withActual withExpected after after after (.var "inferred2") _ _ expected _
            · let withItems := ("items", listValue []) :: withActual
              apply let_returns program withActual withItems after after after (.var "items") _ _ (listValue []) _
              · exact empty_constructor_returns program withActual after "MM0:L" (by decide +kernel) (by decide)
              · simp [SpaceSemantics.matchValue, matchAtom, withItems, withActual, bound, bindings, resultEnvironment, Subst.lookup]
              · simpa [expected, Data.inferred, Data.context, withItems, withActual, bound, bindings, resultEnvironment, applySubst, Subst.lookup] using
                  constructor_variables_return program withItems after "MM0:Inferred" ["items", "sort"] (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, withExpected, withActual, bound, bindings, resultEnvironment, Subst.lookup]
            · simpa [actual, expected, answer, Data.inferred_injective.eq_iff] using
                Scalar.data_equality_captured_returns withExpected after actual expected "inferred" "inferred2" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, tested, bound, bindings, resultEnvironment, Subst.lookup]
        · simpa [answer] using ConversionResults.typed_captured_returns tested after answer symbol arguments result sort
            "equal" "symbol" "arguments" "result" "sort" rfl rfl rfl rfl rfl

theorem body_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound, PureReturns program
      (environment (signatureOf entries symbol) (tableValue handle) (tableValue definitions) context symbol arguments images)
      before equation.body after
        (resultValue (Kernel.ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  rw [body_shape]
  cases lookup : signatureOf entries symbol with
  | none =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := environment none (tableValue handle) (tableValue definitions) context symbol arguments images
      simp only [Kernel.ConvWitness.conversion?, lookup, resultValue]
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None") (.symbol "None") _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some declaration =>
      obtain ⟨middle, unfolded, readyMiddle, frameUnfold⟩ := Unfolding.returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
        context symbol arguments images before allocated bodiesAllocated ready
      have middleAllocated : middle.read handle = some (declarationRows entries) := by
        rw [frameUnfold.other handle separate]; exact allocated
      let result := Kernel.Definition.unfold? (signatureOf entries) (Unfolding.definitionSignature bodies) context symbol arguments images
      obtain ⟨after, bound, converted, readyAfter, frameConvert⟩ := result_body_returns handle cache entries uniqueRows separate context symbol arguments declaration.resultSort result
        middle middleAllocated readyMiddle
      refine ⟨after, max (sizeOf arguments) bound, ?_, readyAfter,
        (frameUnfold.weaken (Nat.le_max_left _ _)).trans (frameConvert.weaken (Nat.le_max_right _ _))⟩
      let bindings := environment (some declaration) (tableValue handle) (tableValue definitions) context symbol arguments images
      let boundBindings := ("dependencies", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) ::
        ("formal", Data.context declaration.arguments) :: bindings
      simp only [Kernel.ConvWitness.conversion?, lookup]
      apply case_returns program bindings boundBindings before before after (.var "valueInput") (optionValue (some (Data.declaration declaration))) declaredBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          Data.declaration, listValue, optionValue, matchAtom, boundBindings, bindings, environment, Subst.lookup]
      · rw [declared_body_shape]
        let withResult := ("unfoldResult", optionValue (result.map Data.preterm)) :: boundBindings
        apply let_returns program boundBindings withResult before middle after (.var "unfoldResult") _ _ (optionValue (result.map Data.preterm)) _
        · exact unfolded boundBindings "table" "definitions" "context" "symbol" "arguments" "images" rfl rfl rfl rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, withResult, boundBindings, bindings, environment, Subst.lookup]
        · apply authored_variable_call_returns program withResult (resultEnvironment result (tableValue handle) context symbol arguments declaration.resultSort) middle after
            "mm0:conversion-unfold-result" ["unfoldResult", "table", "context", "symbol", "arguments", "sort"] resultEquation.body _
            (by decide) (by decide) (by decide) _ converted (by decide)
          simpa [withResult, boundBindings, bindings, environment, applySubst, Subst.lookup] using
            result_clause result (tableValue handle) context symbol arguments declaration.resultSort

theorem captured_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound,
      (∀ bindings declarationName termsName definitionsName contextName symbolName argumentsName imagesName,
        applySubst bindings (.var declarationName) = optionValue ((signatureOf entries symbol).map Data.declaration) →
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var definitionsName) = tableValue definitions →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var symbolName) = natural symbol →
        applySubst bindings (.var argumentsName) = expressionsValue arguments →
        applySubst bindings (.var imagesName) = indicesValue images →
        PureReturns program bindings before
          (.expression [.symbol "mm0:conversion-unfold-declaration", .var declarationName, .var termsName, .var definitionsName, .var contextName,
            .var symbolName, .var argumentsName, .var imagesName]) after
          (resultValue (Kernel.ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images)))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  obtain ⟨after, bound, computed, readyAfter, frame⟩ := body_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images before allocated bodiesAllocated ready
  refine ⟨after, bound, ?_, readyAfter, frame⟩
  intro bindings declarationName termsName definitionsName contextName symbolName argumentsName imagesName capturedDeclaration capturedTerms capturedDefinitions capturedContext capturedSymbol capturedArguments capturedImages
  apply authored_variable_call_returns program bindings
    (environment (signatureOf entries symbol) (tableValue handle) (tableValue definitions) context symbol arguments images) before after
    "mm0:conversion-unfold-declaration" [declarationName, termsName, definitionsName, contextName, symbolName, argumentsName, imagesName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedDeclaration, capturedTerms, capturedDefinitions, capturedContext, capturedSymbol, capturedArguments, capturedImages] using
    clause (signatureOf entries symbol) (tableValue handle) (tableValue definitions) context symbol arguments images

def requestConfiguration (state : State) (handle definitions : Handle) (entries : List ServiceInferenceCache.Row)
    (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Configuration :=
  { state, control := .evaluate
      (environment (signatureOf entries symbol) (tableValue handle) (tableValue definitions) context symbol arguments images)
      (.expression [.symbol "mm0:conversion-unfold-declaration", .var "valueInput", .var "table", .var "definitions", .var "context",
        .var "symbol", .var "arguments", .var "images"]) }

theorem sufficient_fuel (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle definitions entries context symbol arguments images) =
        .complete after [resultValue (Kernel.ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images))] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound state after := by
  obtain ⟨after, bound, path, readyAfter, frame⟩ := captured_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images state allocated bodiesAllocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (signatureOf entries symbol) (tableValue handle) (tableValue definitions) context symbol arguments images) state after _ _
    (path _ "valueInput" "table" "definitions" "context" "symbol" "arguments" "images" rfl rfl rfl rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Option Kernel.ConversionResult) :
    Kernel.ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images) = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions entries context symbol arguments images) =
        .complete after [resultValue answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := sufficient_fuel handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images state allocated bodiesAllocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact ConversionResults.resultValue_injective (List.singleton_inj.mp same.2.1)

theorem checks_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (result : Kernel.ConversionResult) :
    Kernel.ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images)
      result.left result.right result.sort ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions entries context symbol arguments images) =
        .complete after [resultValue (some result)] [] [] := by
  cases result with
  | mk left right sort =>
      exact (Kernel.ConvWitness.conversion_eq_some_iff (signatureOf entries) (Unfolding.definitionSignature bodies)
        context (.unfold symbol arguments images) left right sort).symm.trans
        (result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
          context symbol arguments images state allocated bodiesAllocated ready (some ⟨left, right, sort⟩))

end Mettapedia.Languages.MM0.MeTTa.ConversionUnfolding
