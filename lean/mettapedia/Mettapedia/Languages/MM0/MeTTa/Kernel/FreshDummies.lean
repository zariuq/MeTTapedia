import Mettapedia.Languages.MM0.MeTTa.Kernel.Freshness
import Mettapedia.Languages.MM0.MeTTa.Kernel.BinderChecking

/-!
# Complete dummy-image checking by the retained MM0 source

The source checks sort, defined occurrence support, and freshness in order.
After accepting a dummy it appends that variable to the checked arguments, so
later dummies must also be fresh for earlier images. Neither tables nor the
inference cache change during these checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.FreshDummies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (listValue viewValue)
open ListSubstitution (expressionsValue)
open Support (indicesValue)

private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 69)[68]'(by decide)
private def viewEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 70)[69]'(by decide)
private def sortEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 71)[70]'(by decide)
private def freshEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 72)[71]'(by decide)
private def environment (target : Context) (arguments : List Preterm) (sorts images : List Nat) : Subst :=
  [("images", indicesValue images), ("sorts", indicesValue sorts), ("arguments", expressionsValue arguments), ("target", Data.context target)]
private def viewEnvironment (target : Context) (arguments : List Preterm) (sorts images : List Nat) : Subst :=
  [("arguments", expressionsValue arguments), ("target", Data.context target),
    ("valueInputValue", viewValue (images.map natural)), ("valueInput", viewValue (sorts.map natural))]
private def consBindings (target : Context) (arguments : List Preterm) (sort : Nat) (sorts : List Nat) (image : Nat) (images : List Nat) : Subst :=
  ("images", indicesValue images) :: ("image", natural image) :: ("sorts", indicesValue sorts) :: ("sort", natural sort) ::
    viewEnvironment target arguments (sort :: sorts) (image :: images)
private def conditionEnvironment (answer : Bool) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (image : Nat) : Subst :=
  [("image", natural image), ("images", indicesValue images), ("sorts", indicesValue sorts),
    ("arguments", expressionsValue arguments), ("target", Data.context target), ("conditionInput", boolean answer)]
private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def viewCases := sourceCases viewEquation.body
private def sortCases := sourceCases sortEquation.body
private def freshCases := sourceCases freshEquation.body
private def consBody : Atom := (viewCases[3]'(by decide)).2
private def sortBody : Atom := (sortCases[1]'(by decide)).2
private def freshBody : Atom := (freshCases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:check-dummies") = [equation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:dummies-view") = [viewEquation] := by decide
private theorem sort_unique : program.equations.filter (fun e => e.head == "mm0:dummy-sort") = [sortEquation] := by decide
private theorem fresh_unique : program.equations.filter (fun e => e.head == "mm0:dummy-fresh") = [freshEquation] := by decide
private theorem formals : equation.arguments = [.var "target", .var "arguments", .var "sorts", .var "images"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "valueInputValue", .var "target", .var "arguments"] := by decide
private theorem sort_formals : sortEquation.arguments = [.var "conditionInput", .var "target", .var "arguments", .var "sorts", .var "images", .var "image"] := by decide
private theorem fresh_formals : freshEquation.arguments = [.var "conditionInput", .var "target", .var "arguments", .var "sorts", .var "images", .var "image"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "sorts"],
      .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "images"],
        .expression [.symbol "mm0:dummies-view", .var "view", .var "view2", .var "target", .var "arguments"]]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
      .expression (viewCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem view_cases_shape : viewCases = [(.expression [.symbol "List:Nil", .symbol "List:Nil"], boolean true),
    (.expression [.expression [.symbol "List:Cons", .var "sort", .var "sorts"], .symbol "List:Nil"], boolean false),
    (.expression [.symbol "List:Nil", .expression [.symbol "List:Cons", .var "image", .var "images"]], boolean false),
    (.expression [.expression [.symbol "List:Cons", .var "sort", .var "sorts"],
      .expression [.symbol "List:Cons", .var "image", .var "images"]], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "binderFits", .expression [.symbol "let", .var "items", listValue [],
      .expression [.symbol "let", .var "var", .expression [.symbol "MM0:Var", .var "image"],
        .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
          .expression [.symbol "mm0:check-binder", .var "items", .var "target", .var "var", .var "items2"]]]],
      .expression [.symbol "mm0:dummy-sort", .var "binderFits", .var "target", .var "arguments", .var "sorts", .var "images", .var "image"]] := by decide
private theorem sort_body_shape : sortEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (sortCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem sort_cases_shape : sortCases = [(boolean false, boolean false), (boolean true, sortBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem sort_true_body_shape : sortBody =
    .expression [.symbol "let", .var "freshAllResult", .expression [.symbol "mm0:fresh-all", .var "target", .var "image", .var "arguments"],
      .expression [.symbol "mm0:dummy-fresh", .var "freshAllResult", .var "target", .var "arguments", .var "sorts", .var "images", .var "image"]] := by decide
private theorem fresh_body_shape : freshEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (freshCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem fresh_cases_shape : freshCases = [(boolean false, boolean false), (boolean true, freshBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem fresh_true_body_shape : freshBody =
    .expression [.symbol "let", .var "combined", .expression [.symbol "let", .var "extended",
      .expression [.symbol "let", .var "var", .expression [.symbol "MM0:Var", .var "image"],
        .expression [.symbol "let", .var "items", listValue [], .expression [.symbol "mm0:list-cons", .var "var", .var "items"]]],
      .expression [.symbol "mm0:list-append", .var "arguments", .var "extended"]],
      .expression [.symbol "mm0:check-dummies", .var "target", .var "combined", .var "sorts", .var "images"]] := by decide
private theorem clause (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    clauses program "mm0:check-dummies" [Data.context target, expressionsValue arguments, indicesValue sorts, indicesValue images] =
      [.evaluate (environment target arguments sorts images) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    clauses program "mm0:dummies-view" [viewValue (sorts.map natural), viewValue (images.map natural), Data.context target, expressionsValue arguments] =
      [.evaluate (viewEnvironment target arguments sorts images) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]
private theorem sort_clause (answer : Bool) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (image : Nat) :
    clauses program "mm0:dummy-sort" [boolean answer, Data.context target, expressionsValue arguments, indicesValue sorts, indicesValue images, natural image] =
      [.evaluate (conditionEnvironment answer target arguments sorts images image) sortEquation.body] := by
  rw [clauses_use_only_the_named_equations, sort_unique]
  simp [sort_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, conditionEnvironment]
private theorem fresh_clause (answer : Bool) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (image : Nat) :
    clauses program "mm0:dummy-fresh" [boolean answer, Data.context target, expressionsValue arguments, indicesValue sorts, indicesValue images, natural image] =
      [.evaluate (conditionEnvironment answer target arguments sorts images image) freshEquation.body] := by
  rw [clauses_use_only_the_named_equations, fresh_unique]
  simp [fresh_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, conditionEnvironment]
private theorem call_from_body (bindings : Subst) (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (targetName argumentsName sortsName imagesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedArguments : applySubst bindings (.var argumentsName) = expressionsValue arguments)
    (capturedSorts : applySubst bindings (.var sortsName) = indicesValue sorts)
    (capturedImages : applySubst bindings (.var imagesName) = indicesValue images)
    (computed : PureReturns program (environment target arguments sorts images) state equation.body state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images))) :
    PureReturns program bindings state (.expression [.symbol "mm0:check-dummies", .var targetName, .var argumentsName, .var sortsName, .var imagesName]) state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images)) := by
  apply authored_variable_call_returns program bindings (environment target arguments sorts images) state state
    "mm0:check-dummies" [targetName, argumentsName, sortsName, imagesName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTarget, capturedArguments, capturedSorts, capturedImages] using clause target arguments sorts images

private theorem fresh_body_returns (state : State) (answer : Bool) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (image : Nat)
    (recursive : PureReturns program (environment target (arguments ++ [.var image]) sorts images) state equation.body state
      (boolean (Kernel.Definition.checkDummies target (arguments ++ [.var image]) sorts images))) :
    PureReturns program (conditionEnvironment answer target arguments sorts images image) state freshEquation.body state
      (boolean (answer && Kernel.Definition.checkDummies target (arguments ++ [.var image]) sorts images)) := by
  rw [fresh_body_shape]
  cases answer with
  | false =>
      let bindings := conditionEnvironment false target arguments sorts images image
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ freshCases (read_cases_encoded freshCases)
      · simpa [bindings, conditionEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [fresh_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := conditionEnvironment true target arguments sorts images image
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) freshBody
        _ _ freshCases (read_cases_encoded freshCases)
      · simpa [bindings, conditionEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [fresh_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [fresh_true_body_shape]
        let combined := ("combined", expressionsValue (arguments ++ [.var image])) :: bindings
        apply let_returns program bindings combined state state state (.var "combined") _ _ (expressionsValue (arguments ++ [.var image])) _
        · let extended := ("extended", expressionsValue [.var image]) :: bindings
          apply let_returns program bindings extended state state state (.var "extended") _ _ (expressionsValue [.var image]) _
          · let withVariable := ("var", Data.preterm (.var image)) :: bindings
            apply let_returns program bindings withVariable state state state (.var "var") _ _ (Data.preterm (.var image)) _
            · simpa [Data.preterm, applySubst, Subst.lookup, bindings, conditionEnvironment] using
                unary_constructor_returns program bindings state "MM0:Var" "image" (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, withVariable, bindings, conditionEnvironment, Subst.lookup]
            · let withEmpty := ("items", listValue []) :: withVariable
              apply let_returns program withVariable withEmpty state state state (.var "items") _ _ (listValue []) _
              · exact empty_constructor_returns program withVariable state "MM0:L" (by decide +kernel) (by decide)
              · simp [SpaceSemantics.matchValue, matchAtom, withEmpty, withVariable, bindings, conditionEnvironment, Subst.lookup]
              · exact ListAccess.cons_captured_returns withEmpty state (Data.preterm (.var image)) [] "var" "items" rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, extended, bindings, conditionEnvironment, Subst.lookup]
          · simpa [expressionsValue, List.map_append] using ListAccess.append_captured_returns extended state
              (arguments.map Data.preterm) [Data.preterm (.var image)] "arguments" "extended" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, combined, bindings, conditionEnvironment, Subst.lookup]
        · exact call_from_body combined state target (arguments ++ [.var image]) sorts images "target" "combined" "sorts" "images" rfl rfl rfl rfl recursive

private theorem sort_body_returns (state : State) (answer : Bool) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (image : Nat)
    (recursive : PureReturns program (environment target (arguments ++ [.var image]) sorts images) state equation.body state
      (boolean (Kernel.Definition.checkDummies target (arguments ++ [.var image]) sorts images))) :
    PureReturns program (conditionEnvironment answer target arguments sorts images image) state sortEquation.body state
      (boolean ((answer && arguments.all (Preterm.checkFreshFor target image)) &&
        Kernel.Definition.checkDummies target (arguments ++ [.var image]) sorts images)) := by
  rw [sort_body_shape]
  cases answer with
  | false =>
      let bindings := conditionEnvironment false target arguments sorts images image
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, conditionEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [sort_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := conditionEnvironment true target arguments sorts images image
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) sortBody
        _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, conditionEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [sort_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [sort_true_body_shape]
        let answer := arguments.all (Preterm.checkFreshFor target image)
        let tested := ("freshAllResult", boolean answer) :: bindings
        apply let_returns program bindings tested state state state (.var "freshAllResult") _ _ (boolean answer) _
        · exact Freshness.all_captured_returns bindings state target image arguments "target" "image" "arguments" rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, tested, bindings, conditionEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program tested (conditionEnvironment answer target arguments sorts images image) state state
            "mm0:dummy-fresh" ["freshAllResult", "target", "arguments", "sorts", "images", "image"] freshEquation.body _
            (by decide) (by decide) (by decide) _ (fresh_body_returns state answer target arguments sorts images image recursive) (by decide)
          simpa [tested, bindings, conditionEnvironment, applySubst, Subst.lookup] using fresh_clause answer target arguments sorts images image

private theorem binder_test_returns (state : State) (target : Context) (arguments : List Preterm)
    (sort : Nat) (sorts : List Nat) (image : Nat) (images : List Nat) :
    PureReturns program (consBindings target arguments sort sorts image images) state
      (.expression [.symbol "let", .var "items", listValue [],
        .expression [.symbol "let", .var "var", .expression [.symbol "MM0:Var", .var "image"],
          .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
            .expression [.symbol "mm0:check-binder", .var "items", .var "target", .var "var", .var "items2"]]]]) state
      (boolean (decide (target[image]? = some (.bound sort)))) := by
  let bindings := consBindings target arguments sort sorts image images
  let withTable := ("items", listValue []) :: bindings
  let withVariable := ("var", Data.preterm (.var image)) :: withTable
  let withBinder := ("items2", Data.binder (.bound sort)) :: withVariable
  apply let_returns program bindings withTable state state state (.var "items") _ _ (listValue []) _
  · exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
  · simp [SpaceSemantics.matchValue, matchAtom, withTable, Subst.lookup, bindings, consBindings, viewEnvironment]
  · apply let_returns program withTable withVariable state state state (.var "var") _ _ (Data.preterm (.var image)) _
    · simpa [Data.preterm, withTable, applySubst, Subst.lookup, bindings, consBindings, viewEnvironment] using
        unary_constructor_returns program withTable state "MM0:Var" "image" (by decide +kernel) (by decide)
    · simp [SpaceSemantics.matchValue, matchAtom, withVariable, withTable, Subst.lookup, bindings, consBindings, viewEnvironment]
    · apply let_returns program withVariable withBinder state state state (.var "items2") _ _ (Data.binder (.bound sort)) _
      · apply unary_constructor_of_returns program withVariable state state "MM0:L" _ _ (by decide +kernel) (by decide)
        simpa [withVariable, withTable, applySubst, Subst.lookup, bindings, consBindings, viewEnvironment] using
          unary_constructor_returns program withVariable state "MM0:Bound" "sort" (by decide +kernel) (by decide)
      · simp [SpaceSemantics.matchValue, matchAtom, withBinder, withVariable, withTable, Subst.lookup, bindings, consBindings, viewEnvironment]
      · have checked := BinderChecking.bound_captured_returns withBinder state (listValue []) target (.var image) sort
          "items" "target" "var" "items2" rfl
          rfl rfl rfl
        cases found : target[image]? with
        | none => simpa [Preterm.boundSort?, found] using checked
        | some binder => cases binder <;> simpa [Preterm.boundSort?, found] using checked

private theorem view_body_returns (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (recursive : ∀ sort remaining image rest, sorts = sort :: remaining →
      PureReturns program (environment target (arguments ++ [.var image]) remaining rest) state equation.body state
        (boolean (Kernel.Definition.checkDummies target (arguments ++ [.var image]) remaining rest))) :
    PureReturns program (viewEnvironment target arguments sorts images) state viewEquation.body state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images)) := by
  rw [view_body_shape]
  let bindings := viewEnvironment target arguments sorts images
  have input : PureReturns program bindings state (.expression [.var "valueInput", .var "valueInputValue"]) state
      (.expression [viewValue (sorts.map natural), viewValue (images.map natural)]) := by
    simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "valueInputValue"]
  cases sorts with
  | nil =>
      cases images with
      | nil =>
          apply case_returns program bindings bindings state state state _ _ (boolean true) _ _ viewCases (read_cases_encoded viewCases) input
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
          · exact grounded_returns program bindings state (.bool true)
      | cons image images =>
          let bound := ("images", indicesValue images) :: ("image", natural image) :: bindings
          apply case_returns program bindings bound state state state _ _ (boolean false) _ _ viewCases (read_cases_encoded viewCases) input
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, viewValue, indicesValue, bound, bindings, viewEnvironment, Subst.lookup]
          · exact grounded_returns program bound state (.bool false)
  | cons sort sorts =>
      cases images with
      | nil =>
          let bound := ("sorts", indicesValue sorts) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state _ _ (boolean false) _ _ viewCases (read_cases_encoded viewCases) input
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, viewValue, indicesValue, bound, bindings, viewEnvironment, Subst.lookup]
          · exact grounded_returns program bound state (.bool false)
      | cons image images =>
          let bound := consBindings target arguments sort sorts image images
          apply case_returns program bindings bound state state state _ _ consBody _ _ viewCases (read_cases_encoded viewCases) input
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, viewValue, indicesValue, bound, consBindings, bindings, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let answer := decide (target[image]? = some (.bound sort))
            let tested := ("binderFits", boolean answer) :: bound
            apply let_returns program bound tested state state state (.var "binderFits") _ _ (boolean answer) _
            · exact binder_test_returns state target arguments sort sorts image images
            · simp [SpaceSemantics.matchValue, matchAtom, tested, bound, consBindings, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program tested (conditionEnvironment answer target arguments sorts images image) state state
                "mm0:dummy-sort" ["binderFits", "target", "arguments", "sorts", "images", "image"] sortEquation.body _
                (by decide) (by decide) (by decide) _ (sort_body_returns state answer target arguments sorts images image (recursive sort sorts image images rfl)) (by decide)
              simpa [tested, bound, consBindings, bindings, viewEnvironment, applySubst, Subst.lookup] using sort_clause answer target arguments sorts images image

private theorem body_from_view (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (viewed : PureReturns program (viewEnvironment target arguments sorts images) state viewEquation.body state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images))) :
    PureReturns program (environment target arguments sorts images) state equation.body state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images)) := by
  rw [body_shape]
  let bindings := environment target arguments sorts images
  let firstView := ("view", viewValue (sorts.map natural)) :: bindings
  let bothViews := ("view2", viewValue (images.map natural)) :: firstView
  apply let_returns program bindings firstView state state state (.var "view") _ _ (viewValue (sorts.map natural)) _
  · exact ListAccess.view_captured_returns bindings state "sorts" (sorts.map natural) rfl
  · simp [SpaceSemantics.matchValue, matchAtom, firstView, bindings, environment, Subst.lookup]
  · apply let_returns program firstView bothViews state state state (.var "view2") _ _ (viewValue (images.map natural)) _
    · exact ListAccess.view_captured_returns firstView state "images" (images.map natural) rfl
    · simp [SpaceSemantics.matchValue, matchAtom, bothViews, firstView, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program bothViews (viewEnvironment target arguments sorts images) state state
        "mm0:dummies-view" ["view", "view2", "target", "arguments"] viewEquation.body _
        (by decide) (by decide) (by decide) _ viewed (by decide)
      simpa [bothViews, firstView, bindings, environment, applySubst, Subst.lookup] using view_clause target arguments sorts images

theorem body_returns (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    PureReturns program (environment target arguments sorts images) state equation.body state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images)) := by
  induction sorts generalizing arguments images with
  | nil =>
      apply body_from_view state target arguments [] images
      apply view_body_returns
      intro sort remaining image rest impossible
      cases impossible
  | cons sort sorts ih =>
      apply body_from_view state target arguments (sort :: sorts) images
      apply view_body_returns
      intro first remaining image rest same
      have tail := (List.cons.inj same).2
      subst remaining
      exact ih (arguments ++ [.var image]) rest

theorem captured_returns (bindings : Subst) (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (targetName argumentsName sortsName imagesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedArguments : applySubst bindings (.var argumentsName) = expressionsValue arguments)
    (capturedSorts : applySubst bindings (.var sortsName) = indicesValue sorts)
    (capturedImages : applySubst bindings (.var imagesName) = indicesValue images) :
    PureReturns program bindings state (.expression [.symbol "mm0:check-dummies", .var targetName, .var argumentsName, .var sortsName, .var imagesName]) state
      (boolean (Kernel.Definition.checkDummies target arguments sorts images)) :=
  call_from_body bindings state target arguments sorts images targetName argumentsName sortsName imagesName
    capturedTarget capturedArguments capturedSorts capturedImages (body_returns state target arguments sorts images)

def requestConfiguration (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat) : Configuration :=
  { state, control := .evaluate (environment target arguments sorts images)
      (.expression [.symbol "mm0:check-dummies", .var "target", .var "arguments", .var "sorts", .var "images"]) }

theorem sufficient_fuel (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state target arguments sorts images) =
      .complete state [boolean (Kernel.Definition.checkDummies target arguments sorts images)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment target arguments sorts images) state state _ _
    (captured_returns _ state target arguments sorts images "target" "arguments" "sorts" "images" rfl rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat) (answer : Bool) :
    Kernel.Definition.checkDummies target arguments sorts images = answer ↔
      ∃ fuel, run program fuel (requestConfiguration state target arguments sorts images) = .complete state [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state target arguments sorts images
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same; exact ⟨referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem fresh_dummies_iff_source_accepts (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    Kernel.Definition.FreshDummies target arguments sorts images ↔
      ∃ fuel, run program fuel (requestConfiguration state target arguments sorts images) = .complete state [boolean true] [] [] :=
  (Kernel.Definition.checkDummies_iff target arguments sorts images).symm.trans
    (result_iff_source_returns state target arguments sorts images true)

theorem source_acceptance_requires_distinct_images (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (accepted : ∃ fuel, run program fuel (requestConfiguration state target arguments sorts images) = .complete state [boolean true] [] []) :
    images.Nodup := ((fresh_dummies_iff_source_accepts state target arguments sorts images).mpr accepted).distinct

theorem source_acceptance_excludes_parameter_capture (state : State) (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (accepted : ∃ fuel, run program fuel (requestConfiguration state target arguments sorts images) = .complete state [boolean true] [] []) :
    ∀ image ∈ images, ∀ expression ∈ arguments, ¬ Preterm.HasVar target image expression :=
  ((fresh_dummies_iff_source_accepts state target arguments sorts images).mpr accepted).excludes_arguments

end Mettapedia.Languages.MM0.MeTTa.FreshDummies
