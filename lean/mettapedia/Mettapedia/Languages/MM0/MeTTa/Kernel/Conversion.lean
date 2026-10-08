import Mettapedia.Languages.MM0.MeTTa.Kernel.ConversionUnfolding
import Mettapedia.Languages.MM0.MeTTa.Kernel.ConversionArguments

/-!
# Supplied conversion witnesses in the retained MM0 source

Witnesses are ordinary data. The structural witness/list proof enters the
actual conversion function, including declaration lookup, cache-aware inference
and both endpoints' binder checks. It preserves and reflects the independent
MM0 witness judgment, including completed refusals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Conversion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open NamedSpaces (Handle)
open Kernel (Context Preterm ConvWitness)
open Store (natural)
open ListAccess (listValue optionValue)
open ListSubstitution (expressionsValue)
open Support (indicesValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open ConversionResults (resultValue)

def witnessValue : ConvWitness → Atom
  | .refl expression => listValue [.symbol "MM0:ConvRefl", Data.preterm expression]
  | .symm child => listValue [.symbol "MM0:ConvSymm", witnessValue child]
  | .trans first second => listValue [.symbol "MM0:ConvTrans", witnessValue first, witnessValue second]
  | .congruence symbol children => listValue [.symbol "MM0:ConvCongruence", natural symbol, listValue (children.map witnessValue)]
  | .unfold symbol arguments images => listValue [.symbol "MM0:ConvUnfold", natural symbol, expressionsValue arguments, indicesValue images]
termination_by witness => sizeOf witness

/-- A source call with the caller's names and environment retained. -/
def Call (terms definitions : Atom) (context : Context) (witness : ConvWitness)
    (before after : State) (result : Option Kernel.ConversionResult) : Prop :=
  ∀ bindings termsName definitionsName contextName witnessName,
    applySubst bindings (.var termsName) = terms →
    applySubst bindings (.var definitionsName) = definitions →
    applySubst bindings (.var contextName) = Data.context context →
    applySubst bindings (.var witnessName) = witnessValue witness →
    PureReturns program bindings before
      (.expression [.symbol "mm0:conversion", .var termsName, .var definitionsName, .var contextName, .var witnessName]) after (resultValue result)

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 19)[18]'(by decide)
private def environment (terms definitions : Atom) (context : Context) (witness : ConvWitness) : Subst :=
  [("witness", witnessValue witness), ("context", Data.context context), ("definitions", definitions), ("table", terms)]
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def reflexivityBody : Atom := (cases[0]'(by decide)).2
private def symmetryBody : Atom := (cases[1]'(by decide)).2
private def transitivityBody : Atom := (cases[2]'(by decide)).2
private def congruenceBody : Atom := (cases[3]'(by decide)).2
private def unfoldingBody : Atom := (cases[4]'(by decide)).2
private def firstEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 23)[22]'(by decide)
private def declarationEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 26)[25]'(by decide)
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def firstCases := casesOf firstEquation.body
private def declarationCases := casesOf declarationEquation.body
private def firstSomeBody : Atom := (firstCases[1]'(by decide)).2
private def declarationSomeBody : Atom := (declarationCases[1]'(by decide)).2
private def firstEnvironment (result : Option Kernel.ConversionResult) (terms definitions : Atom) (context : Context) (second : ConvWitness) : Subst :=
  [("second", witnessValue second), ("context", Data.context context), ("definitions", definitions), ("table", terms), ("valueInput", resultValue result)]
private def declarationEnvironment (found : Option Kernel.TermDecl) (terms definitions : Atom) (context : Context) (symbol : Nat) (children : List ConvWitness) : Subst :=
  [("children", listValue (children.map witnessValue)), ("symbol", natural symbol), ("context", Data.context context), ("definitions", definitions),
    ("table", terms), ("valueInput", optionValue (found.map Data.declaration))]
private theorem first_unique : program.equations.filter (fun e => e.head == "mm0:conversion-first") = [firstEquation] := by decide
private theorem declaration_unique : program.equations.filter (fun e => e.head == "mm0:conversion-declaration") = [declarationEquation] := by decide
private theorem first_formals : firstEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "context", .var "second"] := by decide
private theorem declaration_formals : declarationEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "context", .var "symbol", .var "children"] := by decide
private theorem first_body_shape : firstEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (firstCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem first_cases_shape : firstCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Converted", .var "left", .var "middle", .var "sort"], firstSomeBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem first_some_shape : firstSomeBody =
    .expression [.symbol "let", .var "converted", .expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "second"],
      .expression [.symbol "mm0:conversion-join", .var "left", .var "middle", .var "sort", .var "converted"]] := by decide
private theorem declaration_body_shape : declarationEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (declarationCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem declaration_cases_shape : declarationCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", listValue [.symbol "MM0:TermDecl", .var "formal", .var "sort", .var "dependencies"]], declarationSomeBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem declaration_some_shape : declarationSomeBody =
    .expression [.symbol "let", .var "conversionArgumentsResult", .expression [.symbol "mm0:conversion-arguments", .var "table", .var "definitions", .var "context", .var "children", .var "formal"],
      .expression [.symbol "mm0:conversion-congruent", .var "conversionArgumentsResult", .var "symbol", .var "sort"]] := by decide
private theorem first_clause (result : Option Kernel.ConversionResult) (terms definitions : Atom) (context : Context) (second : ConvWitness) :
    clauses program "mm0:conversion-first" [resultValue result, terms, definitions, Data.context context, witnessValue second] =
      [.evaluate (firstEnvironment result terms definitions context second) firstEquation.body] := by
  rw [clauses_use_only_the_named_equations, first_unique]
  simp [first_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, firstEnvironment]
private theorem declaration_clause (found : Option Kernel.TermDecl) (terms definitions : Atom) (context : Context) (symbol : Nat) (children : List ConvWitness) :
    clauses program "mm0:conversion-declaration" [optionValue (found.map Data.declaration), terms, definitions, Data.context context, natural symbol, listValue (children.map witnessValue)] =
      [.evaluate (declarationEnvironment found terms definitions context symbol children) declarationEquation.body] := by
  rw [clauses_use_only_the_named_equations, declaration_unique]
  simp [declaration_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, declarationEnvironment]
private theorem unique : program.equations.filter (fun e => e.head == "mm0:conversion") = [equation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "definitions", .var "context", .var "witness"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "witness", .expression (cases.map fun e => .expression [e.1,e.2])] := by decide
private theorem cases_shape : cases =
    [(listValue [.symbol "MM0:ConvRefl", .var "expression"], reflexivityBody),
    (listValue [.symbol "MM0:ConvSymm", .var "child"], symmetryBody),
    (listValue [.symbol "MM0:ConvTrans", .var "first", .var "second"], transitivityBody),
    (listValue [.symbol "MM0:ConvCongruence", .var "symbol", .var "children"], congruenceBody),
    (listValue [.symbol "MM0:ConvUnfold", .var "symbol", .var "arguments", .var "images"], unfoldingBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem reflexivity_body_shape : reflexivityBody =
    .expression [.symbol "let", .var "inferred", .expression [.symbol "mm0:infer", .var "table", .var "context", .var "expression"],
      .expression [.symbol "mm0:conversion-refl-type", .var "inferred", .var "expression"]] := by decide
private theorem symmetry_body_shape : symmetryBody =
    .expression [.symbol "let", .var "converted", .expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "child"],
      .expression [.symbol "mm0:conversion-swap", .var "converted"]] := by decide
private theorem transitivity_body_shape : transitivityBody =
    .expression [.symbol "let", .var "converted2", .expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "first"],
      .expression [.symbol "mm0:conversion-first", .var "converted2", .var "table", .var "definitions", .var "context", .var "second"]] := by decide
private theorem congruence_body_shape : congruenceBody =
    .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:declaration", .var "table", .var "symbol"],
      .expression [.symbol "mm0:conversion-declaration", .var "declaration", .var "table", .var "definitions", .var "context", .var "symbol", .var "children"]] := by decide
private theorem unfolding_body_shape : unfoldingBody =
    .expression [.symbol "let", .var "declaration2", .expression [.symbol "mm0:declaration", .var "table", .var "symbol"],
      .expression [.symbol "mm0:conversion-unfold-declaration", .var "declaration2", .var "table", .var "definitions", .var "context",
        .var "symbol", .var "arguments", .var "images"]] := by decide
private theorem clause (terms definitions : Atom) (context : Context) (witness : ConvWitness) :
    clauses program "mm0:conversion" [terms, definitions, Data.context context, witnessValue witness] =
      [.evaluate (environment terms definitions context witness) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem call_from_body (bindings : Subst) (before after : State) (terms definitions : Atom) (context : Context) (witness : ConvWitness)
    (termsName definitionsName contextName witnessName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDefinitions : applySubst bindings (.var definitionsName) = definitions)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedWitness : applySubst bindings (.var witnessName) = witnessValue witness)
    (answer : Atom) (computed : PureReturns program (environment terms definitions context witness) before equation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:conversion", .var termsName, .var definitionsName, .var contextName, .var witnessName]) after answer := by
  apply authored_variable_call_returns program bindings (environment terms definitions context witness) before after
    "mm0:conversion" [termsName, definitionsName, contextName, witnessName] equation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedDefinitions, capturedContext, capturedWitness] using clause terms definitions context witness

theorem reflexivity_body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (definitions : Atom) (context : Context) (expression : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after, PureReturns program (environment (tableValue handle) definitions context (.refl expression)) before equation.body after
      (resultValue ((Preterm.infer (signatureOf entries) context expression).bind fun type =>
        if type.1 = [] then some ⟨expression, expression, type.2⟩ else none)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) before after := by
  obtain ⟨after, inferred, readyAfter, frame⟩ := Inference.returns handle cache entries uniqueRows separate context expression before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [body_shape]
  let bindings := environment (tableValue handle) definitions context (.refl expression)
  let bound := ("expression", Data.preterm expression) :: bindings
  apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.refl expression)) reflexivityBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
  · simp [cases_shape, witnessValue, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, bound, bindings, environment, Subst.lookup]
  · rw [reflexivity_body_shape]
    let result := Preterm.infer (signatureOf entries) context expression
    let checked := ("inferred", Data.inferred result) :: bound
    apply let_returns program bound checked before after after (.var "inferred") _ _ (Data.inferred result) _
    · exact inferred bound "table" "context" "expression" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, environment, Subst.lookup]
    · exact ConversionResults.reflexivity_captured_returns checked after result expression "inferred" "expression" rfl rfl

theorem unfolding_body_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound, PureReturns program (environment (tableValue handle) (tableValue definitions) context (.unfold symbol arguments images)) before equation.body after
      (resultValue (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  obtain ⟨after, bound, converted, readyAfter, frame⟩ := ConversionUnfolding.captured_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images before allocated bodiesAllocated ready
  refine ⟨after, bound, ?_, readyAfter, frame⟩
  rw [body_shape]
  let bindings := environment (tableValue handle) (tableValue definitions) context (.unfold symbol arguments images)
  let boundBindings := ("images", indicesValue images) :: ("arguments", expressionsValue arguments) :: ("symbol", natural symbol) :: bindings
  apply case_returns program bindings boundBindings before before after (.var "witness") (witnessValue (.unfold symbol arguments images)) unfoldingBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
  · simp [cases_shape, witnessValue, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, boundBindings, bindings, environment, Subst.lookup]
  · rw [unfolding_body_shape]
    let found := optionValue ((signatureOf entries symbol).map Data.declaration)
    let located := ("declaration2", found) :: boundBindings
    apply let_returns program boundBindings located before before after (.var "declaration2") _ _ found _
    · exact TableAccess.declaration_signature_returns boundBindings before handle entries symbol "table" "symbol" uniqueRows allocated rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, located, boundBindings, bindings, environment, Subst.lookup]
    · exact converted located "declaration2" "table" "definitions" "context" "symbol" "arguments" "images" rfl rfl rfl rfl rfl rfl rfl

theorem reflexivity_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (definitions : Atom) (context : Context) (expression : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName definitionsName contextName witnessName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var definitionsName) = definitions →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var witnessName) = witnessValue (.refl expression) →
        PureReturns program bindings before (.expression [.symbol "mm0:conversion", .var termsName, .var definitionsName, .var contextName, .var witnessName]) after
          (resultValue ((Preterm.infer (signatureOf entries) context expression).bind fun type =>
            if type.1 = [] then some ⟨expression, expression, type.2⟩ else none))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := reflexivity_body_returns handle cache entries uniqueRows separate definitions context expression before allocated ready
  exact ⟨after, fun bindings termsName definitionsName contextName witnessName a b c d =>
    call_from_body bindings before after (tableValue handle) definitions context (.refl expression) termsName definitionsName contextName witnessName a b c d _ computed,
    readyAfter, frame⟩

theorem unfolding_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound,
      (∀ bindings termsName definitionsName contextName witnessName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var definitionsName) = tableValue definitions →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var witnessName) = witnessValue (.unfold symbol arguments images) →
        PureReturns program bindings before (.expression [.symbol "mm0:conversion", .var termsName, .var definitionsName, .var contextName, .var witnessName]) after
          (resultValue (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images)))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  obtain ⟨after, bound, computed, readyAfter, frame⟩ := unfolding_body_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images before allocated bodiesAllocated ready
  exact ⟨after, bound, fun bindings termsName definitionsName contextName witnessName a b c d =>
    call_from_body bindings before after (tableValue handle) (tableValue definitions) context (.unfold symbol arguments images) termsName definitionsName contextName witnessName a b c d _ computed,
    readyAfter, frame⟩

def requestConfiguration (state : State) (handle definitions : Handle) (context : Context) (witness : ConvWitness) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) (tableValue definitions) context witness)
      (.expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "witness"]) }

theorem unfolding_sufficient_fuel (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle definitions context (.unfold symbol arguments images)) =
        .complete after [resultValue (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images))] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound state after := by
  obtain ⟨after, bound, path, readyAfter, frame⟩ := unfolding_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images state allocated bodiesAllocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) (tableValue definitions) context (.unfold symbol arguments images)) state after _ _
    (path _ "table" "definitions" "context" "witness" rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem unfolding_result_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Option Kernel.ConversionResult) :
    ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images) = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context (.unfold symbol arguments images)) =
        .complete after [resultValue answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := unfolding_sufficient_fuel handle definitions cache entries bodies uniqueRows uniqueBodies separate
    context symbol arguments images state allocated bodiesAllocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact ConversionResults.resultValue_injective (List.singleton_inj.mp same.2.1)

theorem unfolding_checks_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (result : Kernel.ConversionResult) :
    ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images)
      result.left result.right result.sort ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context (.unfold symbol arguments images)) =
        .complete after [resultValue (some result)] [] [] := by
  cases result with
  | mk left right sort =>
      exact (ConvWitness.conversion_eq_some_iff (signatureOf entries) (Unfolding.definitionSignature bodies) context
        (.unfold symbol arguments images) left right sort).symm.trans
        (unfolding_result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
          context symbol arguments images state allocated bodiesAllocated ready (some ⟨left, right, sort⟩))

theorem unfolding_refusal_iff_source_returns_none (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (context : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ ∃ left right sort, ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context
      (.unfold symbol arguments images) left right sort) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context (.unfold symbol arguments images)) =
        .complete after [.symbol "None"] [] [] :=
  (ConvWitness.conversion_none_iff (signatureOf entries) (Unfolding.definitionSignature bodies) context (.unfold symbol arguments images)).symm.trans
    (unfolding_result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
      context symbol arguments images state allocated bodiesAllocated ready none)

private theorem symmetry_returns (terms definitions : Atom) (context : Context) (child : ConvWitness)
    (before after : State) (result : Option Kernel.ConversionResult) (checkedChild : Call terms definitions context child before after result) :
    Call terms definitions context (.symm child) before after (result.map fun value => ⟨value.right, value.left, value.sort⟩) := by
  have body : PureReturns program (environment terms definitions context (.symm child)) before equation.body after
      (resultValue (result.map fun value => ⟨value.right, value.left, value.sort⟩)) := by
    rw [body_shape]
    let bindings := environment terms definitions context (.symm child)
    let bound := ("child", witnessValue child) :: bindings
    apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.symm child)) symmetryBody _ _ cases (read_cases_encoded cases)
    · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
    · simp [cases_shape, witnessValue, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, bound, bindings, environment, Subst.lookup]
    · rw [symmetry_body_shape]
      let withResult := ("converted", resultValue result) :: bound
      apply let_returns program bound withResult before after after (.var "converted") _ _ (resultValue result) _
      · exact checkedChild bound "table" "definitions" "context" "child" rfl rfl rfl rfl
      · simp [SpaceSemantics.matchValue, matchAtom, withResult, bound, bindings, environment, Subst.lookup]
      · exact ConversionResults.swap_captured_returns withResult after result "converted" rfl
  intro bindings termsName definitionsName contextName witnessName a b c d
  exact call_from_body bindings before after terms definitions context (.symm child) termsName definitionsName contextName witnessName a b c d _ body

private theorem first_none_body_returns (terms definitions : Atom) (context : Context) (second : ConvWitness) (state : State) :
    PureReturns program (firstEnvironment none terms definitions context second) state firstEquation.body state (.symbol "None") := by
  rw [first_body_shape]
  let bindings := firstEnvironment none terms definitions context second
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ firstCases (read_cases_encoded firstCases)
  · simpa [bindings, firstEnvironment, resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [first_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem first_some_body_returns (terms definitions : Atom) (context : Context) (second : ConvWitness)
    (first : Kernel.ConversionResult) (before after : State) (result : Option Kernel.ConversionResult)
    (checkedSecond : Call terms definitions context second before after result) :
    PureReturns program (firstEnvironment (some first) terms definitions context second) before firstEquation.body after
      (resultValue (result.bind fun second => if first.right = second.left ∧ first.sort = second.sort then
        some ⟨first.left, second.right, first.sort⟩ else none)) := by
  rw [first_body_shape]
  let bindings := firstEnvironment (some first) terms definitions context second
  let bound := ("sort", natural first.sort) :: ("middle", Data.preterm first.right) :: ("left", Data.preterm first.left) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (resultValue (some first)) firstSomeBody _ _ firstCases (read_cases_encoded firstCases)
  · simpa [bindings, firstEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [first_cases_shape, resultValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, bound, bindings, firstEnvironment, Subst.lookup]
  · rw [first_some_shape]
    let withResult := ("converted", resultValue result) :: bound
    apply let_returns program bound withResult before after after (.var "converted") _ _ (resultValue result) _
    · exact checkedSecond bound "table" "definitions" "context" "second" rfl rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withResult, bound, bindings, firstEnvironment, Subst.lookup]
    · exact ConversionResults.join_captured_returns withResult after first result "left" "middle" "sort" "converted" rfl rfl rfl rfl

private theorem transitivity_returns (terms definitions : Atom) (context : Context) (first second : ConvWitness)
    (before middle after : State) (firstResult answer : Option Kernel.ConversionResult)
    (checkedFirst : Call terms definitions context first before middle firstResult)
    (continued : PureReturns program (firstEnvironment firstResult terms definitions context second) middle firstEquation.body after (resultValue answer)) :
    Call terms definitions context (.trans first second) before after answer := by
  have body : PureReturns program (environment terms definitions context (.trans first second)) before equation.body after (resultValue answer) := by
    rw [body_shape]
    let bindings := environment terms definitions context (.trans first second)
    let bound := ("second", witnessValue second) :: ("first", witnessValue first) :: bindings
    apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.trans first second)) transitivityBody _ _ cases (read_cases_encoded cases)
    · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
    · simp [cases_shape, witnessValue, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, bound, bindings, environment, Subst.lookup]
    · rw [transitivity_body_shape]
      let withResult := ("converted2", resultValue firstResult) :: bound
      apply let_returns program bound withResult before middle after (.var "converted2") _ _ (resultValue firstResult) _
      · exact checkedFirst bound "table" "definitions" "context" "first" rfl rfl rfl rfl
      · simp [SpaceSemantics.matchValue, matchAtom, withResult, bound, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program withResult (firstEnvironment firstResult terms definitions context second) middle after
          "mm0:conversion-first" ["converted2", "table", "definitions", "context", "second"] firstEquation.body _
          (by decide) (by decide) (by decide) _ continued (by decide)
        simpa [withResult, bound, bindings, environment, applySubst, Subst.lookup] using first_clause firstResult terms definitions context second
  intro bindings termsName definitionsName contextName witnessName a b c d
  exact call_from_body bindings before after terms definitions context (.trans first second) termsName definitionsName contextName witnessName a b c d _ body

private theorem declaration_none_body_returns (terms definitions : Atom) (context : Context) (symbol : Nat) (children : List ConvWitness) (state : State) :
    PureReturns program (declarationEnvironment none terms definitions context symbol children) state declarationEquation.body state (.symbol "None") := by
  rw [declaration_body_shape]
  let bindings := declarationEnvironment none terms definitions context symbol children
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ declarationCases (read_cases_encoded declarationCases)
  · simpa [bindings, declarationEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [declaration_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem declaration_some_body_returns (terms definitions : Atom) (context : Context) (symbol : Nat) (children : List ConvWitness)
    (declaration : Kernel.TermDecl) (before after : State) (result : Option (List Preterm × List Preterm))
    (checkedArguments : ConversionArguments.Call terms definitions context (listValue (children.map witnessValue)) declaration.arguments before after result) :
    PureReturns program (declarationEnvironment (some declaration) terms definitions context symbol children) before declarationEquation.body after
      (resultValue (result.map fun values => ⟨Preterm.applyArgs (.term symbol) values.1, Preterm.applyArgs (.term symbol) values.2, declaration.resultSort⟩)) := by
  rw [declaration_body_shape]
  let bindings := declarationEnvironment (some declaration) terms definitions context symbol children
  let bound := ("dependencies", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) :: ("formal", Data.context declaration.arguments) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (optionValue (some (Data.declaration declaration))) declarationSomeBody _ _ declarationCases (read_cases_encoded declarationCases)
  · simpa [bindings, declarationEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [declaration_cases_shape, optionValue, Data.declaration, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, bound, bindings, declarationEnvironment, Subst.lookup]
  · rw [declaration_some_shape]
    let withResult := ("conversionArgumentsResult", ConversionResults.argumentsResultValue result) :: bound
    apply let_returns program bound withResult before after after (.var "conversionArgumentsResult") _ _ (ConversionResults.argumentsResultValue result) _
    · exact checkedArguments bound "table" "definitions" "context" "children" "formal" rfl rfl rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withResult, bound, bindings, declarationEnvironment, Subst.lookup]
    · exact ConversionResults.congruent_captured_returns withResult after result symbol declaration.resultSort "conversionArgumentsResult" "symbol" "sort" rfl rfl rfl

private theorem congruence_returns (handle : Handle) (entries : List ServiceInferenceCache.Row) (uniqueRows : ServiceInferenceCache.Unique entries)
    (definitions : Atom) (context : Context) (symbol : Nat) (children : List ConvWitness) (before after : State)
    (allocated : before.read handle = some (declarationRows entries)) (answer : Option Kernel.ConversionResult)
    (continued : PureReturns program (declarationEnvironment (signatureOf entries symbol) (tableValue handle) definitions context symbol children)
      before declarationEquation.body after (resultValue answer)) :
    Call (tableValue handle) definitions context (.congruence symbol children) before after answer := by
  have body : PureReturns program (environment (tableValue handle) definitions context (.congruence symbol children)) before equation.body after (resultValue answer) := by
    rw [body_shape]
    let bindings := environment (tableValue handle) definitions context (.congruence symbol children)
    let bound := ("children", listValue (children.map witnessValue)) :: ("symbol", natural symbol) :: bindings
    apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.congruence symbol children)) congruenceBody _ _ cases (read_cases_encoded cases)
    · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
    · simp [cases_shape, witnessValue, listValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, bound, bindings, environment, Subst.lookup]
    · rw [congruence_body_shape]
      let found := optionValue ((signatureOf entries symbol).map Data.declaration)
      let withDeclaration := ("declaration", found) :: bound
      apply let_returns program bound withDeclaration before before after (.var "declaration") _ _ found _
      · exact TableAccess.declaration_signature_returns bound before handle entries symbol "table" "symbol" uniqueRows allocated rfl rfl
      · simp [SpaceSemantics.matchValue, matchAtom, withDeclaration, bound, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program withDeclaration (declarationEnvironment (signatureOf entries symbol) (tableValue handle) definitions context symbol children) before after
          "mm0:conversion-declaration" ["declaration", "table", "definitions", "context", "symbol", "children"] declarationEquation.body _
          (by decide) (by decide) (by decide) _ continued (by decide)
        simpa [withDeclaration, found, bound, bindings, environment, applySubst, Subst.lookup] using declaration_clause (signatureOf entries symbol) (tableValue handle) definitions context symbol children
  intro bindings termsName definitionsName contextName witnessName a b c d
  exact call_from_body bindings before after (tableValue handle) definitions context (.congruence symbol children)
    termsName definitionsName contextName witnessName a b c d _ body

mutual

/-- Every finite supplied witness is checked by the pinned source. Only the
typing cache may change; term and definition tables remain in scope. -/
theorem returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound,
      Call (tableValue handle) (tableValue definitions) context witness before after
        (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context witness) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  cases witness with
  | refl expression =>
      obtain ⟨after, checked, readyAfter, frame⟩ := reflexivity_returns handle cache entries uniqueRows separate
        (tableValue definitions) context expression before allocated ready
      exact ⟨after, sizeOf expression, by simpa [ConvWitness.conversion?, Call] using checked, readyAfter, frame⟩
  | symm child =>
      obtain ⟨after, bound, checked, readyAfter, frame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
        context child before allocated bodiesAllocated ready
      refine ⟨after, bound, ?_, readyAfter, frame⟩
      simpa [ConvWitness.conversion?, Option.map_eq_bind] using symmetry_returns (tableValue handle) (tableValue definitions) context child before after _ checked
  | trans first second =>
      obtain ⟨middle, firstBound, checkedFirst, readyMiddle, firstFrame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
        context first before allocated bodiesAllocated ready
      cases firstResult : ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context first with
      | none =>
          refine ⟨middle, firstBound, ?_, readyMiddle, firstFrame⟩
          simpa [ConvWitness.conversion?, firstResult] using
            transitivity_returns (tableValue handle) (tableValue definitions) context first second before middle middle none none
              (by simpa only [firstResult] using checkedFirst)
              (first_none_body_returns (tableValue handle) (tableValue definitions) context second middle)
      | some converted =>
          obtain ⟨after, secondBound, checkedSecond, readyAfter, secondFrame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
            context second middle (by rw [firstFrame.other handle separate]; exact allocated)
            (by rw [firstFrame.other definitions separateDefinitions]; exact bodiesAllocated) readyMiddle
          refine ⟨after, max firstBound secondBound, ?_, readyAfter,
            (firstFrame.weaken (Nat.le_max_left _ _)).trans (secondFrame.weaken (Nat.le_max_right _ _))⟩
          simpa [ConvWitness.conversion?, firstResult] using
            transitivity_returns (tableValue handle) (tableValue definitions) context first second before middle after (some converted) _
              (by simpa only [firstResult] using checkedFirst)
              (first_some_body_returns (tableValue handle) (tableValue definitions) context second converted middle after _ checkedSecond)
  | congruence symbol children =>
      cases found : signatureOf entries symbol with
      | none =>
          refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
          simpa [ConvWitness.conversion?, found] using
            congruence_returns handle entries uniqueRows (tableValue definitions) context symbol children before before allocated none
              (by simpa only [found, resultValue] using declaration_none_body_returns (tableValue handle) (tableValue definitions) context symbol children before)
      | some declaration =>
          obtain ⟨after, bound, checkedArguments, readyAfter, frame⟩ := arguments_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
            context children declaration.arguments before allocated bodiesAllocated ready
          refine ⟨after, bound, ?_, readyAfter, frame⟩
          simpa [ConvWitness.conversion?, found, Option.map_eq_bind] using
            congruence_returns handle entries uniqueRows (tableValue definitions) context symbol children before after allocated
              ((ConvWitness.arguments? (signatureOf entries) (Unfolding.definitionSignature bodies) context children declaration.arguments).map
                fun values => ⟨Preterm.applyArgs (.term symbol) values.1, Preterm.applyArgs (.term symbol) values.2, declaration.resultSort⟩)
              (by simpa only [found] using declaration_some_body_returns (tableValue handle) (tableValue definitions) context symbol children declaration before after _ checkedArguments)
  | unfold symbol arguments images =>
      exact unfolding_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate context symbol arguments images before allocated bodiesAllocated ready
termination_by sizeOf witness

/-- Ordered congruence consumes precisely one supplied child per binder.
Arity mismatch and either endpoint's failed binder check complete with absence. -/
theorem arguments_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (children : List ConvWitness) (binders : Context) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound,
      ConversionArguments.Call (tableValue handle) (tableValue definitions) context (listValue (children.map witnessValue)) binders before after
        (ConvWitness.arguments? (signatureOf entries) (Unfolding.definitionSignature bodies) context children binders) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  cases children with
  | nil =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      cases binders with
      | nil =>
          simpa only [ConvWitness.arguments?, List.map_nil, ↓reduceIte] using
            ConversionArguments.call_from_view (tableValue handle) (tableValue definitions) context [] [] before before _
              (ConversionArguments.view_empty_returns (tableValue handle) (tableValue definitions) context [] before)
      | cons binder binders =>
          simpa only [ConvWitness.arguments?, List.map_nil, List.cons_ne_nil, ↓reduceIte] using
            ConversionArguments.call_from_view (tableValue handle) (tableValue definitions) context [] (binder :: binders) before before _
              (ConversionArguments.view_empty_returns (tableValue handle) (tableValue definitions) context (binder :: binders) before)
  | cons child children =>
      cases binders with
      | nil =>
          refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
          simpa only [ConvWitness.arguments?, List.map_cons] using
            ConversionArguments.call_from_view (tableValue handle) (tableValue definitions) context (witnessValue child :: children.map witnessValue) [] before before none
            (ConversionArguments.view_missing_binder_returns (tableValue handle) (tableValue definitions) context (witnessValue child) (children.map witnessValue) before)
      | cons binder binders =>
          obtain ⟨middle, childBound, checkedChild, readyMiddle, childFrame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
            context child before allocated bodiesAllocated ready
          obtain ⟨after, argumentBound, checkedArgument, readyAfter, argumentFrame⟩ := ConversionArguments.argument_body_returns handle cache entries uniqueRows separate
            (tableValue definitions) context (listValue (children.map witnessValue)) binder binders
            (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context child)
            (ConvWitness.arguments? (signatureOf entries) (Unfolding.definitionSignature bodies) context children binders) middle
            (fun state ⟨_, scope⟩ located valid => arguments_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
              context children binders state located
              (by rw [scope.other definitions separateDefinitions, childFrame.other definitions separateDefinitions]; exact bodiesAllocated) valid)
            (by rw [childFrame.other handle separate]; exact allocated) readyMiddle
          refine ⟨after, max childBound argumentBound, ?_, readyAfter,
            (childFrame.weaken (Nat.le_max_left _ _)).trans (argumentFrame.weaken (Nat.le_max_right _ _))⟩
          apply ConversionArguments.call_from_view
          simpa [ConvWitness.arguments?, Option.map_eq_bind] using
            ConversionArguments.view_cons_returns (tableValue handle) (tableValue definitions) context (witnessValue child) (children.map witnessValue) binder binders
              before middle after _ _ checkedChild checkedArgument
termination_by sizeOf children

end

theorem sufficient_fuel (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle definitions context witness) =
        .complete after [resultValue (ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context witness)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound state after := by
  obtain ⟨after, bound, path, readyAfter, frame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
    context witness state allocated bodiesAllocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) (tableValue definitions) context witness) state after _ _
    (path _ "table" "definitions" "context" "witness" rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Option Kernel.ConversionResult) :
    ConvWitness.conversion? (signatureOf entries) (Unfolding.definitionSignature bodies) context witness = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context witness) =
        .complete after [resultValue answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := sufficient_fuel handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
    context witness state allocated bodiesAllocated ready
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
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (result : Kernel.ConversionResult) :
    ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context witness result.left result.right result.sort ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context witness) =
        .complete after [resultValue (some result)] [] [] := by
  cases result with
  | mk left right sort =>
      exact (ConvWitness.conversion_eq_some_iff (signatureOf entries) (Unfolding.definitionSignature bodies) context witness left right sort).symm.trans
        (result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
          context witness state allocated bodiesAllocated ready (some ⟨left, right, sort⟩))

theorem refusal_iff_source_returns_none (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ ∃ left right sort, ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context witness left right sort) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions context witness) =
        .complete after [.symbol "None"] [] [] :=
  (ConvWitness.conversion_none_iff (signatureOf entries) (Unfolding.definitionSignature bodies) context witness).symm.trans
    (result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions
      context witness state allocated bodiesAllocated ready none)

theorem checks_iff_gslt_path (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (separateDefinitions : definitions ≠ cache)
    (context : Context) (witness : ConvWitness) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (Unfolding.definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (result : Kernel.ConversionResult) :
    ConvWitness.Checks (signatureOf entries) (Unfolding.definitionSignature bodies) context witness result.left result.right result.sort ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state handle definitions context witness)
        (finished after [resultValue (some result)] [] []) := by
  rw [checks_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate separateDefinitions context witness state allocated bodiesAllocated ready result]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

end Mettapedia.Languages.MM0.MeTTa.Conversion
