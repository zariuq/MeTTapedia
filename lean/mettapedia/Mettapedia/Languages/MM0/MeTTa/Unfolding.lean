import Mettapedia.Languages.MM0.MeTTa.ArgumentChecking
import Mettapedia.Languages.MM0.MeTTa.FreshDummies
import Mettapedia.Languages.MM0.MeTTa.SubstitutionValues
import Mettapedia.Languages.MM0.MeTTa.Substitution
import Mettapedia.Languages.MM0.Kernel.Unfolding

/-!
# Definition unfolding in the retained MM0 source

The source reads the declared body, checks the supplied parameters and fresh
dummy images, and substitutes them simultaneously. Definition rows are data
in the ordinary private table. Only the inference cache may change while
checking parameters; the definition and term tables remain frozen.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Unfolding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm TermDecl)
open Store (natural)
open ListAccess (listValue linkedValue optionValue)
open ListSubstitution (expressionsValue)
open Support (indicesValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

def bodyValue (body : Kernel.Definition.Body) : Atom :=
  listValue [.symbol "MM0:Definition", indicesValue body.dummies, Data.preterm body.expression]

def definitionRows (entries : List (Nat × Kernel.Definition.Body)) : List Atom :=
  Store.rows (entries.map fun entry => (entry.1, bodyValue entry.2))

def definitionSignature (entries : List (Nat × Kernel.Definition.Body)) : Kernel.Definition.Signature :=
  fun index => (entries.find? fun entry => entry.1 = index).map (·.2)

private def equation : SourceProgram.Equation := (kernelSource.program.equations.take 14)[13]'(by decide)
private def declarationEquation : SourceProgram.Equation := (kernelSource.program.equations.take 15)[14]'(by decide)
private def bodyEquation : SourceProgram.Equation := (kernelSource.program.equations.take 16)[15]'(by decide)
private def argumentsEquation : SourceProgram.Equation := (kernelSource.program.equations.take 17)[16]'(by decide)
private def dummiesEquation : SourceProgram.Equation := (kernelSource.program.equations.take 18)[17]'(by decide)
private def environment (terms definitions : Atom) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Subst :=
  [("images", indicesValue images), ("arguments", expressionsValue arguments), ("symbol", natural symbol),
    ("target", Data.context target), ("definitions", definitions), ("table", terms)]
private def declarationEnvironment (declaration : Option TermDecl) (terms definitions : Atom) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Subst :=
  environment terms definitions target symbol arguments images ++ [("valueInput", optionValue (declaration.map Data.declaration))]
private def bodyEnvironment (body : Option Kernel.Definition.Body) (terms : Atom) (target formal : Context)
    (arguments : List Preterm) (images : List Nat) : Subst :=
  [("images", indicesValue images), ("arguments", expressionsValue arguments), ("formal", Data.context formal),
    ("target", Data.context target), ("table", terms), ("valueInput", optionValue (body.map bodyValue))]
private def argumentsEnvironment (answer : Bool) (target : Context) (arguments : List Preterm)
    (dummies images : List Nat) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("images", indicesValue images), ("dummies", indicesValue dummies),
    ("arguments", expressionsValue arguments), ("target", Data.context target), ("conditionInput", boolean answer)]
private def dummiesEnvironment (answer : Bool) (arguments : List Preterm) (images : List Nat) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("images", indicesValue images),
    ("arguments", expressionsValue arguments), ("conditionInput", boolean answer)]
private def sourceCases (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def declarationCases := sourceCases declarationEquation.body
private def bodyCases := sourceCases bodyEquation.body
private def argumentsCases := sourceCases argumentsEquation.body
private def dummiesCases := sourceCases dummiesEquation.body
private def declaredBody : Atom := (declarationCases[1]'(by decide)).2
private def presentBody : Atom := (bodyCases[1]'(by decide)).2
private def fittedBody : Atom := (argumentsCases[1]'(by decide)).2
private def freshBody : Atom := (dummiesCases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:unfold") = [equation] := by decide
private theorem declaration_unique : program.equations.filter (fun e => e.head == "mm0:unfold-declaration") = [declarationEquation] := by decide
private theorem body_unique : program.equations.filter (fun e => e.head == "mm0:unfold-body") = [bodyEquation] := by decide
private theorem arguments_unique : program.equations.filter (fun e => e.head == "mm0:unfold-arguments") = [argumentsEquation] := by decide
private theorem dummies_unique : program.equations.filter (fun e => e.head == "mm0:unfold-dummies") = [dummiesEquation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "definitions", .var "target", .var "symbol", .var "arguments", .var "images"] := by decide
private theorem declaration_formals : declarationEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "target", .var "symbol", .var "arguments", .var "images"] := by decide
private theorem body_formals : bodyEquation.arguments = [.var "valueInput", .var "table", .var "target", .var "formal", .var "arguments", .var "images"] := by decide
private theorem arguments_formals : argumentsEquation.arguments = [.var "conditionInput", .var "target", .var "arguments", .var "dummies", .var "images", .var "expression"] := by decide
private theorem dummies_formals : dummiesEquation.arguments = [.var "conditionInput", .var "arguments", .var "images", .var "expression"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:declaration", .var "table", .var "symbol"],
      .expression [.symbol "mm0:unfold-declaration", .var "declaration", .var "table", .var "definitions", .var "target", .var "symbol", .var "arguments", .var "images"]] := by decide
private theorem declaration_body_shape : declarationEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (declarationCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem declaration_cases_shape : declarationCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", listValue [.symbol "MM0:TermDecl", .var "formal", .var "sort", .var "dependencies"]], declaredBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem declared_body_shape : declaredBody =
    .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:nat-table-get", .var "definitions", .var "symbol"],
      .expression [.symbol "mm0:unfold-body", .var "declaration", .var "table", .var "target", .var "formal", .var "arguments", .var "images"]] := by decide
private theorem definition_body_shape : bodyEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (bodyCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem body_cases_shape : bodyCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", listValue [.symbol "MM0:Definition", .var "dummies", .var "expression"]], presentBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem present_body_shape : presentBody =
    .expression [.symbol "let", .var "argumentsFit", .expression [.symbol "mm0:check-arguments", .var "table", .var "target", .var "arguments", .var "formal"],
      .expression [.symbol "mm0:unfold-arguments", .var "argumentsFit", .var "target", .var "arguments", .var "dummies", .var "images", .var "expression"]] := by decide
private theorem arguments_body_shape : argumentsEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (argumentsCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem arguments_cases_shape : argumentsCases = [(boolean false, .symbol "None"), (boolean true, fittedBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem fitted_body_shape : fittedBody =
    .expression [.symbol "let", .var "checkDummiesResult", .expression [.symbol "mm0:check-dummies", .var "target", .var "arguments", .var "dummies", .var "images"],
      .expression [.symbol "mm0:unfold-dummies", .var "checkDummiesResult", .var "arguments", .var "images", .var "expression"]] := by decide
private theorem dummies_body_shape : dummiesEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (dummiesCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem dummies_cases_shape : dummiesCases = [(boolean false, .symbol "None"), (boolean true, freshBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem fresh_body_shape : freshBody =
    .expression [.symbol "let", .var "substitutionValuesResult",
      .expression [.symbol "let", .var "combined",
        .expression [.symbol "let", .var "variableImagesResult", .expression [.symbol "mm0:variable-images", .var "images"],
          .expression [.symbol "mm0:list-append", .var "arguments", .var "variableImagesResult"]],
        .expression [.symbol "mm0:substitution-values", .var "combined"]],
      .expression [.symbol "mm0:subst", .var "expression", .var "substitutionValuesResult"]] := by decide
private theorem clause (terms definitions : Atom) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    clauses program "mm0:unfold" [terms, definitions, Data.context target, natural symbol, expressionsValue arguments, indicesValue images] =
      [.evaluate (environment terms definitions target symbol arguments images) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem declaration_clause (declaration : Option TermDecl) (terms definitions : Atom) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    clauses program "mm0:unfold-declaration" [optionValue (declaration.map Data.declaration), terms, definitions, Data.context target,
      natural symbol, expressionsValue arguments, indicesValue images] =
      [.evaluate (declarationEnvironment declaration terms definitions target symbol arguments images) declarationEquation.body] := by
  rw [clauses_use_only_the_named_equations, declaration_unique]
  simp [declaration_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, declarationEnvironment, environment]
private theorem body_clause (body : Option Kernel.Definition.Body) (terms : Atom) (target formal : Context) (arguments : List Preterm) (images : List Nat) :
    clauses program "mm0:unfold-body" [optionValue (body.map bodyValue), terms, Data.context target, Data.context formal, expressionsValue arguments, indicesValue images] =
      [.evaluate (bodyEnvironment body terms target formal arguments images) bodyEquation.body] := by
  rw [clauses_use_only_the_named_equations, body_unique]
  simp [body_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, bodyEnvironment]
private theorem arguments_clause (answer : Bool) (target : Context) (arguments : List Preterm) (dummies images : List Nat) (expression : Preterm) :
    clauses program "mm0:unfold-arguments" [boolean answer, Data.context target, expressionsValue arguments, indicesValue dummies, indicesValue images, Data.preterm expression] =
      [.evaluate (argumentsEnvironment answer target arguments dummies images expression) argumentsEquation.body] := by
  rw [clauses_use_only_the_named_equations, arguments_unique]
  simp [arguments_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, argumentsEnvironment]
private theorem dummies_clause (answer : Bool) (arguments : List Preterm) (images : List Nat) (expression : Preterm) :
    clauses program "mm0:unfold-dummies" [boolean answer, expressionsValue arguments, indicesValue images, Data.preterm expression] =
      [.evaluate (dummiesEnvironment answer arguments images expression) dummiesEquation.body] := by
  rw [clauses_use_only_the_named_equations, dummies_unique]
  simp [dummies_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, dummiesEnvironment]

private theorem dummies_body_returns (state : State) (answer : Bool) (arguments : List Preterm) (images : List Nat) (expression : Preterm) :
    PureReturns program (dummiesEnvironment answer arguments images expression) state dummiesEquation.body state
      (optionValue ((if answer then expression.substitute (Kernel.Substitution.ofList (Kernel.Definition.substitutionValues arguments images)) else none).map Data.preterm)) := by
  rw [dummies_body_shape]
  cases answer with
  | false =>
      let bindings := dummiesEnvironment false arguments images expression
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None") _ _ dummiesCases (read_cases_encoded dummiesCases)
      · simpa [bindings, dummiesEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [dummies_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      let bindings := dummiesEnvironment true arguments images expression
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) freshBody _ _ dummiesCases (read_cases_encoded dummiesCases)
      · simpa [bindings, dummiesEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [dummies_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · rw [fresh_body_shape]
        let values := Kernel.Definition.substitutionValues arguments images
        let prepared := ("substitutionValuesResult", linkedValue (values.map Data.preterm)) :: bindings
        apply let_returns program bindings prepared state state state (.var "substitutionValuesResult") _ _ (linkedValue (values.map Data.preterm)) _
        · let combined := ("combined", expressionsValue values) :: bindings
          apply let_returns program bindings combined state state state (.var "combined") _ _ (expressionsValue values) _
          · let withImages := ("variableImagesResult", expressionsValue (images.map Preterm.var)) :: bindings
            apply let_returns program bindings withImages state state state (.var "variableImagesResult") _ _ (expressionsValue (images.map Preterm.var)) _
            · simpa [expressionsValue, List.map_map, Function.comp_def] using
                SubstitutionValues.variable_images_captured_returns bindings state images "images" rfl
            · simp [SourceProgram.matchValue, matchAtom, withImages, bindings, dummiesEnvironment, Subst.lookup]
            · simpa [values, Kernel.Definition.substitutionValues, expressionsValue, List.map_append, List.map_map, Function.comp_def] using
                ListAccess.append_captured_returns withImages state (arguments.map Data.preterm) (images.map fun i => Data.preterm (.var i))
                  "arguments" "variableImagesResult" rfl
                  (by simp [withImages, expressionsValue, List.map_map, Function.comp_def, applySubst, Subst.lookup])
          · simp [SourceProgram.matchValue, matchAtom, combined, bindings, dummiesEnvironment, Subst.lookup]
          · exact SubstitutionValues.captured_returns combined state (values.map Data.preterm) "combined" rfl
        · simp [SourceProgram.matchValue, matchAtom, prepared, bindings, dummiesEnvironment, Subst.lookup]
        · exact Substitution.subst_captured_returns prepared state expression values "expression" "substitutionValuesResult" rfl rfl

private theorem arguments_body_returns (state : State) (answer : Bool) (target : Context) (arguments : List Preterm)
    (dummies images : List Nat) (expression : Preterm) :
    PureReturns program (argumentsEnvironment answer target arguments dummies images expression) state argumentsEquation.body state
      (optionValue ((if answer && Kernel.Definition.checkDummies target arguments dummies images then
        expression.substitute (Kernel.Substitution.ofList (Kernel.Definition.substitutionValues arguments images)) else none).map Data.preterm)) := by
  rw [arguments_body_shape]
  cases answer with
  | false =>
      let bindings := argumentsEnvironment false target arguments dummies images expression
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None") _ _ argumentsCases (read_cases_encoded argumentsCases)
      · simpa [bindings, argumentsEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [arguments_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      let bindings := argumentsEnvironment true target arguments dummies images expression
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) fittedBody _ _ argumentsCases (read_cases_encoded argumentsCases)
      · simpa [bindings, argumentsEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [arguments_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · rw [fitted_body_shape]
        let answer := Kernel.Definition.checkDummies target arguments dummies images
        let fresh := ("checkDummiesResult", boolean answer) :: bindings
        apply let_returns program bindings fresh state state state (.var "checkDummiesResult") _ _ (boolean answer) _
        · exact FreshDummies.captured_returns bindings state target arguments dummies images "target" "arguments" "dummies" "images" rfl rfl rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, fresh, bindings, argumentsEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program fresh (dummiesEnvironment answer arguments images expression) state state
            "mm0:unfold-dummies" ["checkDummiesResult", "arguments", "images", "expression"] dummiesEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [fresh, bindings, argumentsEnvironment, applySubst, Subst.lookup] using dummies_clause answer arguments images expression
          · simpa [answer] using dummies_body_returns state answer arguments images expression

private theorem definition_body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (target formal : Context) (arguments : List Preterm) (images : List Nat) (body : Option Kernel.Definition.Body) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after, PureReturns program (bodyEnvironment body (tableValue handle) target formal arguments images)
      before bodyEquation.body after
        (optionValue ((body.bind fun body => if Kernel.Substitution.checkArguments (signatureOf entries) target arguments formal &&
          Kernel.Definition.checkDummies target arguments body.dummies images then
          body.expression.substitute (Kernel.Substitution.ofList (Kernel.Definition.substitutionValues arguments images)) else none).map Data.preterm)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  rw [definition_body_shape]
  cases body with
  | none =>
      refine ⟨before, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := bodyEnvironment none (tableValue handle) target formal arguments images
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None") (.symbol "None") _ _ bodyCases (read_cases_encoded bodyCases)
      · simpa [bindings, bodyEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [body_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some body =>
      obtain ⟨after, fitted, readyAfter, frame⟩ := ArgumentChecking.returns handle cache entries uniqueRows separate target arguments formal before allocated ready
      refine ⟨after, ?_, readyAfter, frame⟩
      let bindings := bodyEnvironment (some body) (tableValue handle) target formal arguments images
      let bound := ("expression", Data.preterm body.expression) :: ("dummies", indicesValue body.dummies) :: bindings
      apply case_returns program bindings bound before before after (.var "valueInput") (optionValue (some (bodyValue body))) presentBody _ _ bodyCases (read_cases_encoded bodyCases)
      · simpa [bindings, bodyEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [body_cases_shape, bodyValue, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, optionValue, bound, bindings, bodyEnvironment, Subst.lookup]
      · rw [present_body_shape]
        let answer := Kernel.Substitution.checkArguments (signatureOf entries) target arguments formal
        let checked := ("argumentsFit", boolean answer) :: bound
        apply let_returns program bound checked before after after (.var "argumentsFit") _ _ (boolean answer) _
        · exact fitted bound "table" "target" "arguments" "formal" rfl rfl rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, checked, bound, bindings, bodyEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program checked (argumentsEnvironment answer target arguments body.dummies images body.expression) after after
            "mm0:unfold-arguments" ["argumentsFit", "target", "arguments", "dummies", "images", "expression"] argumentsEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [checked, bound, bindings, bodyEnvironment, applySubst, Subst.lookup] using arguments_clause answer target arguments body.dummies images body.expression
          · simpa [answer] using arguments_body_returns after answer target arguments body.dummies images body.expression

private theorem declaration_body_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat)
    (arguments : List Preterm) (images : List Nat) (declaration : Option TermDecl) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after, PureReturns program
      (declarationEnvironment declaration (tableValue handle) (tableValue definitions) target symbol arguments images)
      before declarationEquation.body after
        (optionValue ((declaration.bind fun declaration => (definitionSignature bodies symbol).bind fun body =>
          if Kernel.Substitution.checkArguments (signatureOf entries) target arguments declaration.arguments &&
            Kernel.Definition.checkDummies target arguments body.dummies images then
            body.expression.substitute (Kernel.Substitution.ofList (Kernel.Definition.substitutionValues arguments images)) else none).map Data.preterm)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  rw [declaration_body_shape]
  cases declaration with
  | none =>
      refine ⟨before, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := declarationEnvironment none (tableValue handle) (tableValue definitions) target symbol arguments images
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None") (.symbol "None") _ _ declarationCases (read_cases_encoded declarationCases)
      · simpa [bindings, declarationEnvironment, environment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [declaration_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some declaration =>
      obtain ⟨after, unfolded, readyAfter, frame⟩ := definition_body_returns handle cache entries uniqueRows separate
        target declaration.arguments arguments images (definitionSignature bodies symbol) before allocated ready
      refine ⟨after, ?_, readyAfter, frame⟩
      let bindings := declarationEnvironment (some declaration) (tableValue handle) (tableValue definitions) target symbol arguments images
      let bound := ("dependencies", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) ::
        ("formal", Data.context declaration.arguments) :: bindings
      apply case_returns program bindings bound before before after (.var "valueInput") (optionValue (some (Data.declaration declaration))) declaredBody
        _ _ declarationCases (read_cases_encoded declarationCases)
      · simpa [bindings, declarationEnvironment, environment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [declaration_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          Data.declaration, listValue, optionValue, matchAtom, bound, bindings, declarationEnvironment, environment, Subst.lookup]
      · rw [declared_body_shape]
        let found := optionValue ((definitionSignature bodies symbol).map bodyValue)
        let located := ("declaration", found) :: bound
        apply let_returns program bound located before before after (.var "declaration") _ _ found _
        · simpa [found, definitionRows, definitionSignature, Option.map_map, Function.comp_def] using
            TableAccess.indexed_rows_returns bodyValue bound before definitions bodies symbol "definitions" "symbol"
              uniqueBodies bodiesAllocated rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, located, bound, bindings, declarationEnvironment, environment, Subst.lookup]
        · apply authored_variable_call_returns program located
            (bodyEnvironment (definitionSignature bodies symbol) (tableValue handle) target declaration.arguments arguments images) before after
            "mm0:unfold-body" ["declaration", "table", "target", "formal", "arguments", "images"] bodyEquation.body _
            (by decide) (by decide) (by decide) _ unfolded (by decide)
          simpa [located, found, bound, bindings, declarationEnvironment, environment, applySubst, Subst.lookup] using
            body_clause (definitionSignature bodies symbol) (tableValue handle) target declaration.arguments arguments images

theorem body_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after, PureReturns program (environment (tableValue handle) (tableValue definitions) target symbol arguments images)
      before equation.body after
        (optionValue ((Kernel.Definition.unfold? (signatureOf entries) (definitionSignature bodies) target symbol arguments images).map Data.preterm)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  obtain ⟨after, unfolded, readyAfter, frame⟩ := declaration_body_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    target symbol arguments images (signatureOf entries symbol) before allocated bodiesAllocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  rw [body_shape]
  let bindings := environment (tableValue handle) (tableValue definitions) target symbol arguments images
  let found := optionValue ((signatureOf entries symbol).map Data.declaration)
  let located := ("declaration", found) :: bindings
  apply let_returns program bindings located before before after (.var "declaration") _ _ found _
  · exact TableAccess.declaration_signature_returns bindings before handle entries symbol "table" "symbol" uniqueRows allocated rfl rfl
  · simp [SourceProgram.matchValue, matchAtom, located, bindings, environment, Subst.lookup]
  · apply authored_variable_call_returns program located
      (declarationEnvironment (signatureOf entries symbol) (tableValue handle) (tableValue definitions) target symbol arguments images) before after
      "mm0:unfold-declaration" ["declaration", "table", "definitions", "target", "symbol", "arguments", "images"] declarationEquation.body _
      (by decide) (by decide) (by decide) _ _ (by decide)
    · simpa [located, found, bindings, environment, applySubst, Subst.lookup] using
        declaration_clause (signatureOf entries symbol) (tableValue handle) (tableValue definitions) target symbol arguments images
    · simpa [Kernel.Definition.unfold?] using unfolded

theorem returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (bodiesAllocated : before.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings termsName definitionsName targetName symbolName argumentsName imagesName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var definitionsName) = tableValue definitions →
        applySubst bindings (.var targetName) = Data.context target →
        applySubst bindings (.var symbolName) = natural symbol →
        applySubst bindings (.var argumentsName) = expressionsValue arguments →
        applySubst bindings (.var imagesName) = indicesValue images →
        PureReturns program bindings before
          (.expression [.symbol "mm0:unfold", .var termsName, .var definitionsName, .var targetName, .var symbolName, .var argumentsName, .var imagesName]) after
          (optionValue ((Kernel.Definition.unfold? (signatureOf entries) (definitionSignature bodies) target symbol arguments images).map Data.preterm))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    target symbol arguments images before allocated bodiesAllocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings termsName definitionsName targetName symbolName argumentsName imagesName capturedTerms capturedDefinitions capturedTarget capturedSymbol capturedArguments capturedImages
  apply authored_variable_call_returns program bindings (environment (tableValue handle) (tableValue definitions) target symbol arguments images) before after
    "mm0:unfold" [termsName, definitionsName, targetName, symbolName, argumentsName, imagesName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedDefinitions, capturedTarget, capturedSymbol, capturedArguments, capturedImages] using
    clause (tableValue handle) (tableValue definitions) target symbol arguments images

def requestConfiguration (state : State) (handle definitions : Handle) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) (tableValue definitions) target symbol arguments images)
      (.expression [.symbol "mm0:unfold", .var "table", .var "definitions", .var "target", .var "symbol", .var "arguments", .var "images"]) }

theorem sufficient_fuel (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle definitions target symbol arguments images) =
        .complete after [optionValue ((Kernel.Definition.unfold? (signatureOf entries) (definitionSignature bodies) target symbol arguments images).map Data.preterm)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
    target symbol arguments images state allocated bodiesAllocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) (tableValue definitions) target symbol arguments images) state after _ _
    (path _ "table" "definitions" "target" "symbol" "arguments" "images" rfl rfl rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Option Preterm) :
    Kernel.Definition.unfold? (signatureOf entries) (definitionSignature bodies) target symbol arguments images = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions target symbol arguments images) =
        .complete after [optionValue (answer.map Data.preterm)] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle definitions cache entries bodies uniqueRows uniqueBodies separate
    target symbol arguments images state allocated bodiesAllocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact Data.optional_preterm_injective (List.singleton_inj.mp same.2.1)

theorem unfolds_iff_source_returns (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (result : Preterm) :
    Kernel.Definition.Unfolds (signatureOf entries) (definitionSignature bodies) target symbol arguments images result ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions target symbol arguments images) =
        .complete after [optionValue (some (Data.preterm result))] [] [] :=
  (Kernel.Definition.unfold_eq_some_iff (signatureOf entries) (definitionSignature bodies) target symbol arguments images result).symm.trans
    (result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
      target symbol arguments images state allocated bodiesAllocated ready (some result))

theorem refusal_iff_source_returns_none (handle definitions cache : Handle) (entries : List ServiceInferenceCache.Row)
    (bodies : List (Nat × Kernel.Definition.Body))
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (uniqueBodies : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1)
    (separate : handle ≠ cache) (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (bodiesAllocated : state.read definitions = some (definitionRows bodies))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ ∃ result, Kernel.Definition.Unfolds (signatureOf entries) (definitionSignature bodies) target symbol arguments images result) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle definitions target symbol arguments images) = .complete after [.symbol "None"] [] [] :=
  (Kernel.Definition.unfold_none_iff (signatureOf entries) (definitionSignature bodies) target symbol arguments images).symm.trans
    (result_iff_source_returns handle definitions cache entries bodies uniqueRows uniqueBodies separate
      target symbol arguments images state allocated bodiesAllocated ready none)

end Mettapedia.Languages.MM0.MeTTa.Unfolding
