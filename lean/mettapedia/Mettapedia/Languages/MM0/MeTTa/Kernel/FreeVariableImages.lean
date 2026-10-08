import Mettapedia.Languages.MM0.MeTTa.Kernel.Dependencies
import Mettapedia.Languages.MM0.Presentation.FreeVariablesData

/-!
# Dependency images in the retained MM0 source

Every clause is projected from the digest-checked source program. The source
traversal preserves order and repeated dependency positions and refuses any
image that is not a matching bound variable. It changes no store or cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.FreeVariableImages

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm Binder)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open Support (indicesValue resultValue)
open Presentation.ComputationalFreeVariables (boundImage? images?)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def free_imageEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 162)[161]'(by decide +kernel)
private def free_imageEnvironment (target formal arguments position : Atom) : Subst :=
  [("position", position), ("arguments", arguments), ("formal", formal), ("target", target)]
private theorem free_image_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-image") = [free_imageEquation] := by decide +kernel
private theorem free_image_formals :
    free_imageEquation.arguments = [.var "target", .var "formal", .var "arguments", .var "position"] := by decide +kernel
private theorem free_image_clause (target formal arguments position : Atom) :
    clauses program "mm0:free-image" [target, formal, arguments, position] =
      [.evaluate (free_imageEnvironment target formal arguments position) free_imageEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_image_unique]
  simp [free_image_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_imageEnvironment]
private theorem free_image_captured_of_body (bindings : Subst) (before after : State)
    (target formal arguments position : Atom) (targetName formalName argumentsName positionName : String) (answer : Atom)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_position : applySubst bindings (.var positionName) = position)
    (computed : PureReturns program (free_imageEnvironment target formal arguments position) before free_imageEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-image", .var targetName, .var formalName, .var argumentsName, .var positionName]) after answer := by
  apply authored_variable_call_returns program bindings (free_imageEnvironment target formal arguments position) before after "mm0:free-image"
    [targetName, formalName, argumentsName, positionName] free_imageEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_target, capture_formal, capture_arguments, capture_position] using free_image_clause target formal arguments position
private theorem free_image_shape :
    free_imageEquation.body = .expression [.symbol "let", .var "entry", .expression [.symbol "mm0:data-at", .var "formal", .var "position"], .expression [.symbol "mm0:free-image-formal", .var "entry", .var "target", .var "arguments", .var "position"]] := by decide +kernel

private def free_image_formalEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 163)[162]'(by decide +kernel)
private def free_image_formalEnvironment (valueInput target arguments position : Atom) : Subst :=
  [("position", position), ("arguments", arguments), ("target", target), ("valueInput", valueInput)]
private theorem free_image_formal_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-image-formal") = [free_image_formalEquation] := by decide +kernel
private theorem free_image_formal_formals :
    free_image_formalEquation.arguments = [.var "valueInput", .var "target", .var "arguments", .var "position"] := by decide +kernel
private theorem free_image_formal_clause (valueInput target arguments position : Atom) :
    clauses program "mm0:free-image-formal" [valueInput, target, arguments, position] =
      [.evaluate (free_image_formalEnvironment valueInput target arguments position) free_image_formalEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_image_formal_unique]
  simp [free_image_formal_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_image_formalEnvironment]
private theorem free_image_formal_captured_of_body (bindings : Subst) (before after : State)
    (valueInput target arguments position : Atom) (valueInputName targetName argumentsName positionName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_position : applySubst bindings (.var positionName) = position)
    (computed : PureReturns program (free_image_formalEnvironment valueInput target arguments position) before free_image_formalEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-image-formal", .var valueInputName, .var targetName, .var argumentsName, .var positionName]) after answer := by
  apply authored_variable_call_returns program bindings (free_image_formalEnvironment valueInput target arguments position) before after "mm0:free-image-formal"
    [valueInputName, targetName, argumentsName, positionName] free_image_formalEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_target, capture_arguments, capture_position] using free_image_formal_clause valueInput target arguments position
private def free_image_formalCases := casesOf free_image_formalEquation.body
private def free_image_formalBody1 : Atom := (free_image_formalCases[1]'(by decide +kernel)).2
private theorem free_image_formal_body_1_shape :
    free_image_formalBody1 = .expression [.symbol "let", .var "entry", .expression [.symbol "mm0:data-at", .var "arguments", .var "position"], .expression [.symbol "mm0:free-image-argument", .var "entry", .var "target", .var "sort"]] := by decide +kernel
private theorem free_image_formal_shape :
    free_image_formalEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_image_formalCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_image_formal_cases_shape :
    free_image_formalCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]]], free_image_formalBody1),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]]], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_image_argumentEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 164)[163]'(by decide +kernel)
private def free_image_argumentEnvironment (valueInput target sort : Atom) : Subst :=
  [("sort", sort), ("target", target), ("valueInput", valueInput)]
private theorem free_image_argument_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-image-argument") = [free_image_argumentEquation] := by decide +kernel
private theorem free_image_argument_formals :
    free_image_argumentEquation.arguments = [.var "valueInput", .var "target", .var "sort"] := by decide +kernel
private theorem free_image_argument_clause (valueInput target sort : Atom) :
    clauses program "mm0:free-image-argument" [valueInput, target, sort] =
      [.evaluate (free_image_argumentEnvironment valueInput target sort) free_image_argumentEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_image_argument_unique]
  simp [free_image_argument_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_image_argumentEnvironment]
private theorem free_image_argument_captured_of_body (bindings : Subst) (before after : State)
    (valueInput target sort : Atom) (valueInputName targetName sortName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_sort : applySubst bindings (.var sortName) = sort)
    (computed : PureReturns program (free_image_argumentEnvironment valueInput target sort) before free_image_argumentEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-image-argument", .var valueInputName, .var targetName, .var sortName]) after answer := by
  apply authored_variable_call_returns program bindings (free_image_argumentEnvironment valueInput target sort) before after "mm0:free-image-argument"
    [valueInputName, targetName, sortName] free_image_argumentEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_target, capture_sort] using free_image_argument_clause valueInput target sort
private def free_image_argumentCases := casesOf free_image_argumentEquation.body
private def free_image_argumentBody0 : Atom := (free_image_argumentCases[0]'(by decide +kernel)).2
private theorem free_image_argument_body_0_shape :
    free_image_argumentBody0 = .expression [.symbol "let", .var "entry", .expression [.symbol "mm0:data-at", .var "target", .var "image"], .expression [.symbol "mm0:free-image-target", .var "entry", .var "sort", .var "image"]] := by decide +kernel
private theorem free_image_argument_shape :
    free_image_argumentEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_image_argumentCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_image_argument_cases_shape :
    free_image_argumentCases = [
      (.expression [.symbol "Some", .expression [.symbol "MM0:Var", .var "image"]], free_image_argumentBody0),
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .expression [.symbol "MM0:Term", .var "symbol"]], .symbol "None"),
      (.expression [.symbol "Some", .expression [.symbol "MM0:App", .var "function", .var "argument"]], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_image_targetEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 165)[164]'(by decide +kernel)
private def free_image_targetEnvironment (valueInput expected image : Atom) : Subst :=
  [("image", image), ("expected", expected), ("valueInput", valueInput)]
private theorem free_image_target_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-image-target") = [free_image_targetEquation] := by decide +kernel
private theorem free_image_target_formals :
    free_image_targetEquation.arguments = [.var "valueInput", .var "expected", .var "image"] := by decide +kernel
private theorem free_image_target_clause (valueInput expected image : Atom) :
    clauses program "mm0:free-image-target" [valueInput, expected, image] =
      [.evaluate (free_image_targetEnvironment valueInput expected image) free_image_targetEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_image_target_unique]
  simp [free_image_target_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_image_targetEnvironment]
private theorem free_image_target_captured_of_body (bindings : Subst) (before after : State)
    (valueInput expected image : Atom) (valueInputName expectedName imageName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_expected : applySubst bindings (.var expectedName) = expected)
    (capture_image : applySubst bindings (.var imageName) = image)
    (computed : PureReturns program (free_image_targetEnvironment valueInput expected image) before free_image_targetEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-image-target", .var valueInputName, .var expectedName, .var imageName]) after answer := by
  apply authored_variable_call_returns program bindings (free_image_targetEnvironment valueInput expected image) before after "mm0:free-image-target"
    [valueInputName, expectedName, imageName] free_image_targetEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_expected, capture_image] using free_image_target_clause valueInput expected image
private def free_image_targetCases := casesOf free_image_targetEquation.body
private def free_image_targetBody0 : Atom := (free_image_targetCases[0]'(by decide +kernel)).2
private theorem free_image_target_body_0_shape :
    free_image_targetBody0 = .expression [.symbol "let", .var "equal", .expression [.symbol "mm0:nat-eq", .var "actual", .var "expected"], .expression [.symbol "mm0:free-image-equal", .var "equal", .var "image"]] := by decide +kernel
private theorem free_image_target_shape :
    free_image_targetEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_image_targetCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_image_target_cases_shape :
    free_image_targetCases = [
      (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "actual"]]], free_image_targetBody0),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]]], .symbol "None"),
      (.symbol "None", .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_image_equalEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 166)[165]'(by decide +kernel)
private def free_image_equalEnvironment (conditionInput image : Atom) : Subst :=
  [("image", image), ("conditionInput", conditionInput)]
private theorem free_image_equal_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-image-equal") = [free_image_equalEquation] := by decide +kernel
private theorem free_image_equal_formals :
    free_image_equalEquation.arguments = [.var "conditionInput", .var "image"] := by decide +kernel
private theorem free_image_equal_clause (conditionInput image : Atom) :
    clauses program "mm0:free-image-equal" [conditionInput, image] =
      [.evaluate (free_image_equalEnvironment conditionInput image) free_image_equalEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_image_equal_unique]
  simp [free_image_equal_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_image_equalEnvironment]
private theorem free_image_equal_captured_of_body (bindings : Subst) (before after : State)
    (conditionInput image : Atom) (conditionInputName imageName : String) (answer : Atom)
    (capture_conditionInput : applySubst bindings (.var conditionInputName) = conditionInput)
    (capture_image : applySubst bindings (.var imageName) = image)
    (computed : PureReturns program (free_image_equalEnvironment conditionInput image) before free_image_equalEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-image-equal", .var conditionInputName, .var imageName]) after answer := by
  apply authored_variable_call_returns program bindings (free_image_equalEnvironment conditionInput image) before after "mm0:free-image-equal"
    [conditionInputName, imageName] free_image_equalEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_conditionInput, capture_image] using free_image_equal_clause conditionInput image
private def free_image_equalCases := casesOf free_image_equalEquation.body
private def free_image_equalBody0 : Atom := (free_image_equalCases[0]'(by decide +kernel)).2
private theorem free_image_equal_body_0_shape :
    free_image_equalBody0 = .expression [.symbol "Some", .var "image"] := by decide +kernel
private theorem free_image_equal_shape :
    free_image_equalEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (free_image_equalCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_image_equal_cases_shape :
    free_image_equalCases = [
      (boolean true, free_image_equalBody0),
      (boolean false, .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_imagesEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 167)[166]'(by decide +kernel)
private def free_imagesEnvironment (target formal arguments positions : Atom) : Subst :=
  [("positions", positions), ("arguments", arguments), ("formal", formal), ("target", target)]
private theorem free_images_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-images") = [free_imagesEquation] := by decide +kernel
private theorem free_images_formals :
    free_imagesEquation.arguments = [.var "target", .var "formal", .var "arguments", .var "positions"] := by decide +kernel
private theorem free_images_clause (target formal arguments positions : Atom) :
    clauses program "mm0:free-images" [target, formal, arguments, positions] =
      [.evaluate (free_imagesEnvironment target formal arguments positions) free_imagesEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_images_unique]
  simp [free_images_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_imagesEnvironment]
private theorem free_images_captured_of_body (bindings : Subst) (before after : State)
    (target formal arguments positions : Atom) (targetName formalName argumentsName positionsName : String) (answer : Atom)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_positions : applySubst bindings (.var positionsName) = positions)
    (computed : PureReturns program (free_imagesEnvironment target formal arguments positions) before free_imagesEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-images", .var targetName, .var formalName, .var argumentsName, .var positionsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_imagesEnvironment target formal arguments positions) before after "mm0:free-images"
    [targetName, formalName, argumentsName, positionsName] free_imagesEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_target, capture_formal, capture_arguments, capture_positions] using free_images_clause target formal arguments positions
private theorem free_images_shape :
    free_imagesEquation.body = .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "positions"], .expression [.symbol "mm0:free-images-view", .var "view", .var "target", .var "formal", .var "arguments"]] := by decide +kernel

private def free_images_viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 168)[167]'(by decide +kernel)
private def free_images_viewEnvironment (valueInput target formal arguments : Atom) : Subst :=
  [("arguments", arguments), ("formal", formal), ("target", target), ("valueInput", valueInput)]
private theorem free_images_view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-images-view") = [free_images_viewEquation] := by decide +kernel
private theorem free_images_view_formals :
    free_images_viewEquation.arguments = [.var "valueInput", .var "target", .var "formal", .var "arguments"] := by decide +kernel
private theorem free_images_view_clause (valueInput target formal arguments : Atom) :
    clauses program "mm0:free-images-view" [valueInput, target, formal, arguments] =
      [.evaluate (free_images_viewEnvironment valueInput target formal arguments) free_images_viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_images_view_unique]
  simp [free_images_view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_images_viewEnvironment]
private theorem free_images_view_captured_of_body (bindings : Subst) (before after : State)
    (valueInput target formal arguments : Atom) (valueInputName targetName formalName argumentsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (computed : PureReturns program (free_images_viewEnvironment valueInput target formal arguments) before free_images_viewEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-images-view", .var valueInputName, .var targetName, .var formalName, .var argumentsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_images_viewEnvironment valueInput target formal arguments) before after "mm0:free-images-view"
    [valueInputName, targetName, formalName, argumentsName] free_images_viewEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_target, capture_formal, capture_arguments] using free_images_view_clause valueInput target formal arguments
private def free_images_viewCases := casesOf free_images_viewEquation.body
private def free_images_viewBody0 : Atom := (free_images_viewCases[0]'(by decide +kernel)).2
private theorem free_images_view_body_0_shape :
    free_images_viewBody0 = .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "Some", .var "items"]] := by decide +kernel
private def free_images_viewBody1 : Atom := (free_images_viewCases[1]'(by decide +kernel)).2
private theorem free_images_view_body_1_shape :
    free_images_viewBody1 = .expression [.symbol "let", .var "freeImageResult", .expression [.symbol "mm0:free-image", .var "target", .var "formal", .var "arguments", .var "position"], .expression [.symbol "mm0:free-images-first", .var "freeImageResult", .var "target", .var "formal", .var "arguments", .var "positions"]] := by decide +kernel
private theorem free_images_view_shape :
    free_images_viewEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_images_viewCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_images_view_cases_shape :
    free_images_viewCases = [
      (.symbol "List:Nil", free_images_viewBody0),
      (.expression [.symbol "List:Cons", .var "position", .var "positions"], free_images_viewBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_images_firstEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 169)[168]'(by decide +kernel)
private def free_images_firstEnvironment (valueInput target formal arguments positions : Atom) : Subst :=
  [("positions", positions), ("arguments", arguments), ("formal", formal), ("target", target), ("valueInput", valueInput)]
private theorem free_images_first_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-images-first") = [free_images_firstEquation] := by decide +kernel
private theorem free_images_first_formals :
    free_images_firstEquation.arguments = [.var "valueInput", .var "target", .var "formal", .var "arguments", .var "positions"] := by decide +kernel
private theorem free_images_first_clause (valueInput target formal arguments positions : Atom) :
    clauses program "mm0:free-images-first" [valueInput, target, formal, arguments, positions] =
      [.evaluate (free_images_firstEnvironment valueInput target formal arguments positions) free_images_firstEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_images_first_unique]
  simp [free_images_first_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_images_firstEnvironment]
private theorem free_images_first_captured_of_body (bindings : Subst) (before after : State)
    (valueInput target formal arguments positions : Atom) (valueInputName targetName formalName argumentsName positionsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_positions : applySubst bindings (.var positionsName) = positions)
    (computed : PureReturns program (free_images_firstEnvironment valueInput target formal arguments positions) before free_images_firstEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-images-first", .var valueInputName, .var targetName, .var formalName, .var argumentsName, .var positionsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_images_firstEnvironment valueInput target formal arguments positions) before after "mm0:free-images-first"
    [valueInputName, targetName, formalName, argumentsName, positionsName] free_images_firstEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_target, capture_formal, capture_arguments, capture_positions] using free_images_first_clause valueInput target formal arguments positions
private def free_images_firstCases := casesOf free_images_firstEquation.body
private def free_images_firstBody1 : Atom := (free_images_firstCases[1]'(by decide +kernel)).2
private theorem free_images_first_body_1_shape :
    free_images_firstBody1 = .expression [.symbol "let", .var "freeImagesResult", .expression [.symbol "mm0:free-images", .var "target", .var "formal", .var "arguments", .var "positions"], .expression [.symbol "mm0:free-images-tail", .var "image", .var "freeImagesResult"]] := by decide +kernel
private theorem free_images_first_shape :
    free_images_firstEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_images_firstCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_images_first_cases_shape :
    free_images_firstCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "image"], free_images_firstBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_images_tailEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 170)[169]'(by decide +kernel)
private def free_images_tailEnvironment (image valueInput : Atom) : Subst :=
  [("valueInput", valueInput), ("image", image)]
private theorem free_images_tail_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-images-tail") = [free_images_tailEquation] := by decide +kernel
private theorem free_images_tail_formals :
    free_images_tailEquation.arguments = [.var "image", .var "valueInput"] := by decide +kernel
private theorem free_images_tail_clause (image valueInput : Atom) :
    clauses program "mm0:free-images-tail" [image, valueInput] =
      [.evaluate (free_images_tailEnvironment image valueInput) free_images_tailEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_images_tail_unique]
  simp [free_images_tail_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_images_tailEnvironment]
private theorem free_images_tail_captured_of_body (bindings : Subst) (before after : State)
    (image valueInput : Atom) (imageName valueInputName : String) (answer : Atom)
    (capture_image : applySubst bindings (.var imageName) = image)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (computed : PureReturns program (free_images_tailEnvironment image valueInput) before free_images_tailEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-images-tail", .var imageName, .var valueInputName]) after answer := by
  apply authored_variable_call_returns program bindings (free_images_tailEnvironment image valueInput) before after "mm0:free-images-tail"
    [imageName, valueInputName] free_images_tailEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_image, capture_valueInput] using free_images_tail_clause image valueInput
private def free_images_tailCases := casesOf free_images_tailEquation.body
private def free_images_tailBody1 : Atom := (free_images_tailCases[1]'(by decide +kernel)).2
private theorem free_images_tail_body_1_shape :
    free_images_tailBody1 = .expression [.symbol "let", .var "extended", .expression [.symbol "mm0:list-cons", .var "image", .var "images"], .expression [.symbol "Some", .var "extended"]] := by decide +kernel
private theorem free_images_tail_shape :
    free_images_tailEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_images_tailCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_images_tail_cases_shape :
    free_images_tailCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "images"], free_images_tailBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private theorem equal_body_returns (state : State) (condition : Bool) (image : Nat) :
    PureReturns program (free_image_equalEnvironment (boolean condition) (natural image)) state
      free_image_equalEquation.body state (optionValue ((if condition then some image else none).map natural)) := by
  rw [free_image_equal_shape]
  let bindings := free_image_equalEnvironment (boolean condition) (natural image)
  cases condition with
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean false) (.symbol "None") _ _ free_image_equalCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [free_image_equal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean true) free_image_equalBody0 _ _ free_image_equalCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [free_image_equal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [free_image_equal_body_0_shape]
        simpa [bindings, free_image_equalEnvironment, applySubst, Subst.lookup, optionValue] using
          unary_constructor_returns program bindings state "Some" "image" some_is_data_constructor (by decide)

private theorem target_body_returns (state : State) (entry : Option Binder) (expected image : Nat) :
    PureReturns program (free_image_targetEnvironment (optionValue (entry.map Data.binder))
      (natural expected) (natural image)) state free_image_targetEquation.body state
      (optionValue ((if entry = some (.bound expected) then some image else none).map natural)) := by
  rw [free_image_target_shape]
  let bindings := free_image_targetEnvironment (optionValue (entry.map Data.binder)) (natural expected) (natural image)
  cases entry with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ free_image_targetCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_image_target_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some binder =>
      cases binder with
      | regular sort deps =>
          let bound := ("dependencies", Data.dependencies deps) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.regular sort deps)))) (.symbol "None") _ _ free_image_targetCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_target_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, free_image_targetEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"
      | bound actual =>
          let bound := ("actual", natural actual) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.bound actual)))) free_image_targetBody0 _ _ free_image_targetCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_target_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, free_image_targetEnvironment, Subst.lookup]
          · rw [free_image_target_body_0_shape]
            let checked := ("equal", boolean (decide (actual = expected))) :: bound
            apply let_returns program bound checked state state state (.var "equal") _ _
              (boolean (decide (actual = expected))) _
            · exact Scalar.equality_captured_returns bound state "actual" "expected" actual expected rfl
                (by simp [bound, bindings, free_image_targetEnvironment, applySubst, Subst.lookup])
            · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, free_image_targetEnvironment, Subst.lookup]
            · apply free_image_equal_captured_of_body checked state state
                (boolean (decide (actual = expected))) (natural image) "equal" "image" _ rfl
                (by simp [checked, bound, bindings, free_image_targetEnvironment, applySubst, Subst.lookup])
              simpa using equal_body_returns state (decide (actual = expected)) image

private theorem argument_body_returns (state : State) (entry : Option Preterm) (target : Context) (sort : Nat) :
    PureReturns program (free_image_argumentEnvironment (optionValue (entry.map Data.preterm))
      (Data.context target) (natural sort)) state free_image_argumentEquation.body state
      (optionValue ((match entry with
        | some (.var image) => if target[image]? = some (Binder.bound sort) then some image else none
        | _ => none).map natural)) := by
  rw [free_image_argument_shape]
  let bindings := free_image_argumentEnvironment (optionValue (entry.map Data.preterm)) (Data.context target) (natural sort)
  cases entry with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_image_argumentCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_image_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some expression =>
      cases expression with
      | term symbol =>
          let bound := ("symbol", natural symbol) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.preterm (.term symbol)))) (.symbol "None") _ _ free_image_argumentCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.preterm,
              bound, bindings, free_image_argumentEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"
      | app function argument =>
          let bound := ("argument", Data.preterm argument) :: ("function", Data.preterm function) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.preterm (.app function argument)))) (.symbol "None") _ _ free_image_argumentCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.preterm,
              bound, bindings, free_image_argumentEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"
      | var image =>
          let bound := ("image", natural image) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.preterm (.var image)))) free_image_argumentBody0 _ _ free_image_argumentCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.preterm,
              bound, bindings, free_image_argumentEnvironment, Subst.lookup]
          · rw [free_image_argument_body_0_shape]
            let found := ("entry", optionValue ((target.map Data.binder)[image]?)) :: bound
            apply let_returns program bound found state state state (.var "entry") _ _
              (optionValue ((target.map Data.binder)[image]?)) _
            · exact ListAccess.data_at_list_returns bound state (target.map Data.binder) image "target" "image"
                (by simp [bound, bindings, free_image_argumentEnvironment, applySubst, Subst.lookup, Data.context]) rfl
            · simp [SpaceSemantics.matchValue, matchAtom, found, bound, bindings, free_image_argumentEnvironment, Subst.lookup]
            · apply free_image_target_captured_of_body found state state
                (optionValue ((target[image]?).map Data.binder)) (natural sort) (natural image) "entry" "sort" "image" _
                (by simp [found, applySubst, Subst.lookup, List.getElem?_map])
                (by simp [found, bound, bindings, free_image_argumentEnvironment, applySubst, Subst.lookup])
                (by simp [found, bound, bindings, free_image_argumentEnvironment, applySubst, Subst.lookup])
              exact target_body_returns state (target[image]?) sort image

private theorem formal_body_returns (state : State) (entry : Option Binder) (target : Context)
    (arguments : List Preterm) (position : Nat) :
    PureReturns program (free_image_formalEnvironment (optionValue (entry.map Data.binder))
      (Data.context target) (listValue (arguments.map Data.preterm)) (natural position)) state
      free_image_formalEquation.body state
      (optionValue ((match entry, arguments[position]? with
        | some (.bound sort), some (.var image) => if target[image]? = some (Binder.bound sort) then some image else none
        | _, _ => none).map natural)) := by
  rw [free_image_formal_shape]
  let bindings := free_image_formalEnvironment (optionValue (entry.map Data.binder)) (Data.context target)
    (listValue (arguments.map Data.preterm)) (natural position)
  cases entry with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_image_formalCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_image_formal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some binder =>
      cases binder with
      | regular sort deps =>
          let bound := ("dependencies", Data.dependencies deps) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.regular sort deps)))) (.symbol "None") _ _ free_image_formalCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_formal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, free_image_formalEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"
      | bound sort =>
          let bound := ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.bound sort)))) free_image_formalBody1 _ _ free_image_formalCases (read_cases_encoded _)
          · exact variable_returns program bindings state "valueInput"
          · simp [free_image_formal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, free_image_formalEnvironment, Subst.lookup]
          · rw [free_image_formal_body_1_shape]
            let found := ("entry", optionValue ((arguments.map Data.preterm)[position]?)) :: bound
            apply let_returns program bound found state state state (.var "entry") _ _
              (optionValue ((arguments.map Data.preterm)[position]?)) _
            · exact ListAccess.data_at_list_returns bound state (arguments.map Data.preterm) position "arguments" "position"
                (by simp [bound, bindings, free_image_formalEnvironment, applySubst, Subst.lookup])
                (by simp [bound, bindings, free_image_formalEnvironment, applySubst, Subst.lookup])
            · simp [SpaceSemantics.matchValue, matchAtom, found, bound, bindings, free_image_formalEnvironment, Subst.lookup]
            · apply free_image_argument_captured_of_body found state state
                (optionValue ((arguments[position]?).map Data.preterm)) (Data.context target) (natural sort) "entry" "target" "sort" _
                (by simp [found, applySubst, Subst.lookup, List.getElem?_map])
                (by simp [found, bound, bindings, free_image_formalEnvironment, applySubst, Subst.lookup])
                (by simp [found, bound, bindings, free_image_formalEnvironment, applySubst, Subst.lookup])
              have computed := argument_body_returns state (arguments[position]?) target sort
              cases lookup : arguments[position]? with
              | none => simpa [lookup] using computed
              | some expression => cases expression <;> simpa [lookup] using computed

private theorem bound_image_normal (target formal : Context) (arguments : List Preterm) (position : Nat) :
    boundImage? target formal arguments position =
      match formal[position]?, arguments[position]? with
      | some (.bound sort), some (.var image) => if target[image]? = some (Binder.bound sort) then some image else none
      | _, _ => none := by
  cases f : formal[position]? with
  | none => simp [boundImage?, Kernel.FreeVariables.checkImage, f]
  | some binder =>
      cases binder with
      | regular sort deps => simp [boundImage?, Kernel.FreeVariables.checkImage, f]
      | bound sort =>
          cases a : arguments[position]? with
          | none => simp [boundImage?, Kernel.FreeVariables.checkImage, f, a]
          | some argument =>
              cases argument <;>
                simp [boundImage?, Kernel.FreeVariables.checkImage, Kernel.FreeVariables.argumentIndex?, f, a]

theorem image_body_returns (state : State) (target formal : Context) (arguments : List Preterm) (position : Nat) :
    PureReturns program (free_imageEnvironment (Data.context target) (Data.context formal)
      (listValue (arguments.map Data.preterm)) (natural position)) state free_imageEquation.body state
      (optionValue ((boundImage? target formal arguments position).map natural)) := by
  rw [free_image_shape, bound_image_normal]
  let bindings := free_imageEnvironment (Data.context target) (Data.context formal)
    (listValue (arguments.map Data.preterm)) (natural position)
  let found := ("entry", optionValue ((formal.map Data.binder)[position]?)) :: bindings
  apply let_returns program bindings found state state state (.var "entry") _ _
    (optionValue ((formal.map Data.binder)[position]?)) _
  · exact ListAccess.data_at_list_returns bindings state (formal.map Data.binder) position "formal" "position" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, found, bindings, free_imageEnvironment, Subst.lookup]
  · apply free_image_formal_captured_of_body found state state
      (optionValue ((formal[position]?).map Data.binder)) (Data.context target)
      (listValue (arguments.map Data.preterm)) (natural position) "entry" "target" "arguments" "position" _
      (by simp [found, applySubst, Subst.lookup, List.getElem?_map])
      (by simp [found, bindings, free_imageEnvironment, applySubst, Subst.lookup])
      (by simp [found, bindings, free_imageEnvironment, applySubst, Subst.lookup])
      (by simp [found, bindings, free_imageEnvironment, applySubst, Subst.lookup])
    exact formal_body_returns state (formal[position]?) target arguments position

theorem image_captured_returns (bindings : Subst) (state : State) (target formal : Context)
    (arguments : List Preterm) (position : Nat) (targetName formalName argumentsName positionName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedArguments : applySubst bindings (.var argumentsName) = listValue (arguments.map Data.preterm))
    (capturedPosition : applySubst bindings (.var positionName) = natural position) :
    PureReturns program bindings state (.expression [.symbol "mm0:free-image", .var targetName,
      .var formalName, .var argumentsName, .var positionName]) state
      (optionValue ((boundImage? target formal arguments position).map natural)) :=
  free_image_captured_of_body bindings state state _ _ _ _ targetName formalName argumentsName positionName _
    capturedTarget capturedFormal capturedArguments capturedPosition (image_body_returns state target formal arguments position)

private theorem images_tail_body_returns (state : State) (image : Nat) (tail : Option (List Nat)) :
    PureReturns program (free_images_tailEnvironment (natural image) (resultValue tail)) state
      free_images_tailEquation.body state (resultValue (tail.map (image :: ·))) := by
  rw [free_images_tail_shape]
  let bindings := free_images_tailEnvironment (natural image) (resultValue tail)
  cases tail with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_images_tailCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_images_tail_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some images =>
      let bound := ("images", indicesValue images) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some images))
        free_images_tailBody1 _ _ free_images_tailCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_images_tail_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, free_images_tailEnvironment, Subst.lookup]
      · rw [free_images_tail_body_1_shape]
        let extended := ("extended", indicesValue (image :: images)) :: bound
        apply let_returns program bound extended state state state (.var "extended") _ _ (indicesValue (image :: images)) _
        · simpa [indicesValue] using ListAccess.cons_captured_returns bound state (natural image) (images.map natural)
            "image" "images" (by simp [bound, bindings, free_images_tailEnvironment, applySubst, Subst.lookup]) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, extended, bound, bindings, free_images_tailEnvironment, Subst.lookup]
        · simpa [extended, resultValue, optionValue, applySubst, Subst.lookup] using
            unary_constructor_returns program extended state "Some" "extended" some_is_data_constructor (by decide)

private theorem images_first_body_returns (state : State) (target formal : Context) (arguments : List Preterm)
    (positions : List Nat) (first : Option Nat)
    (recursive : PureReturns program (free_imagesEnvironment (Data.context target) (Data.context formal)
      (listValue (arguments.map Data.preterm)) (indicesValue positions)) state free_imagesEquation.body state
        (resultValue (images? target formal arguments positions))) :
    PureReturns program (free_images_firstEnvironment (optionValue (first.map natural)) (Data.context target)
      (Data.context formal) (listValue (arguments.map Data.preterm)) (indicesValue positions)) state
      free_images_firstEquation.body state (resultValue (do
        let image ← first
        let images ← images? target formal arguments positions
        pure (image :: images))) := by
  rw [free_images_first_shape]
  let bindings := free_images_firstEnvironment (optionValue (first.map natural)) (Data.context target)
    (Data.context formal) (listValue (arguments.map Data.preterm)) (indicesValue positions)
  cases first with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_images_firstCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_images_first_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some image =>
      let bound := ("image", natural image) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (optionValue (some (natural image)))
        free_images_firstBody1 _ _ free_images_firstCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_images_first_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, optionValue,
          bound, bindings, free_images_firstEnvironment, Subst.lookup]
      · rw [free_images_first_body_1_shape]
        let remaining := ("freeImagesResult", resultValue (images? target formal arguments positions)) :: bound
        apply let_returns program bound remaining state state state (.var "freeImagesResult") _ _
          (resultValue (images? target formal arguments positions)) _
        · exact free_images_captured_of_body bound state state _ _ _ _ "target" "formal" "arguments" "positions" _
            (by simp [bound, bindings, free_images_firstEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_images_firstEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_images_firstEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_images_firstEnvironment, applySubst, Subst.lookup]) recursive
        · simp [SpaceSemantics.matchValue, matchAtom, remaining, bound, bindings, free_images_firstEnvironment, Subst.lookup]
        · apply free_images_tail_captured_of_body remaining state state (natural image)
            (resultValue (images? target formal arguments positions)) "image" "freeImagesResult" _
            (by simp [remaining, bound, bindings, free_images_firstEnvironment, applySubst, Subst.lookup]) rfl
          have computed := images_tail_body_returns state image (images? target formal arguments positions)
          cases tail : images? target formal arguments positions <;> simpa [tail] using computed

theorem images_body_returns (state : State) (target formal : Context) (arguments : List Preterm) (positions : List Nat) :
    PureReturns program (free_imagesEnvironment (Data.context target) (Data.context formal)
      (listValue (arguments.map Data.preterm)) (indicesValue positions)) state free_imagesEquation.body state
      (resultValue (images? target formal arguments positions)) := by
  induction positions with
  | nil =>
      rw [free_images_shape]
      let bindings := free_imagesEnvironment (Data.context target) (Data.context formal)
        (listValue (arguments.map Data.preterm)) (indicesValue [])
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "positions" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, free_imagesEnvironment, Subst.lookup]
      · apply free_images_view_captured_of_body viewed state state (viewValue []) (Data.context target)
          (Data.context formal) (listValue (arguments.map Data.preterm)) "view" "target" "formal" "arguments" _ rfl
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
        rw [free_images_view_shape]
        let callee := free_images_viewEnvironment (viewValue []) (Data.context target) (Data.context formal)
          (listValue (arguments.map Data.preterm))
        apply case_returns program callee callee state state state (.var "valueInput") (viewValue [])
          free_images_viewBody0 _ _ free_images_viewCases (read_cases_encoded _)
        · exact variable_returns program callee state "valueInput"
        · simp [free_images_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
        · rw [free_images_view_body_0_shape]
          let wrapped := ("items", indicesValue []) :: callee
          apply let_returns program callee wrapped state state state (.var "items") _ _ (indicesValue []) _
          · exact empty_constructor_returns program callee state "MM0:L" list_is_data_constructor (by decide)
          · simp [SpaceSemantics.matchValue, matchAtom, wrapped, callee, free_images_viewEnvironment, Subst.lookup]
          · simpa [wrapped, resultValue, optionValue, images?, applySubst, Subst.lookup] using
              unary_constructor_returns program wrapped state "Some" "items" some_is_data_constructor (by decide)
  | cons position positions ih =>
      rw [free_images_shape]
      let bindings := free_imagesEnvironment (Data.context target) (Data.context formal)
        (listValue (arguments.map Data.preterm)) (indicesValue (position :: positions))
      let viewed := ("view", viewValue ((position :: positions).map natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _
        (viewValue ((position :: positions).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "positions" ((position :: positions).map natural) rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, free_imagesEnvironment, Subst.lookup]
      · apply free_images_view_captured_of_body viewed state state (viewValue ((position :: positions).map natural))
          (Data.context target) (Data.context formal) (listValue (arguments.map Data.preterm))
          "view" "target" "formal" "arguments" _ rfl
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
          (by simp [viewed, bindings, free_imagesEnvironment, applySubst, Subst.lookup])
        rw [free_images_view_shape]
        let callee := free_images_viewEnvironment (viewValue ((position :: positions).map natural))
          (Data.context target) (Data.context formal) (listValue (arguments.map Data.preterm))
        let bound := ("positions", indicesValue positions) :: ("position", natural position) :: callee
        apply case_returns program callee bound state state state (.var "valueInput")
          (viewValue ((position :: positions).map natural)) free_images_viewBody1 _ _ free_images_viewCases (read_cases_encoded _)
        · exact variable_returns program callee state "valueInput"
        · simp [free_images_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, indicesValue,
            bound, callee, free_images_viewEnvironment, Subst.lookup]
        · rw [free_images_view_body_1_shape]
          let found := ("freeImageResult", optionValue ((boundImage? target formal arguments position).map natural)) :: bound
          apply let_returns program bound found state state state (.var "freeImageResult") _ _
            (optionValue ((boundImage? target formal arguments position).map natural)) _
          · exact image_captured_returns bound state target formal arguments position "target" "formal" "arguments" "position"
              (by simp [bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
              (by simp [bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
              (by simp [bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup]) rfl
          · simp [SpaceSemantics.matchValue, matchAtom, found, bound, callee, free_images_viewEnvironment, Subst.lookup]
          · apply free_images_first_captured_of_body found state state
              (optionValue ((boundImage? target formal arguments position).map natural)) (Data.context target)
              (Data.context formal) (listValue (arguments.map Data.preterm)) (indicesValue positions)
              "freeImageResult" "target" "formal" "arguments" "positions" _ rfl
              (by simp [found, bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
              (by simp [found, bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
              (by simp [found, bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
              (by simp [found, bound, callee, free_images_viewEnvironment, applySubst, Subst.lookup])
            exact images_first_body_returns state target formal arguments positions
              (boundImage? target formal arguments position) ih

theorem captured_returns (bindings : Subst) (state : State) (target formal : Context)
    (arguments : List Preterm) (positions : List Nat) (targetName formalName argumentsName positionsName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedArguments : applySubst bindings (.var argumentsName) = listValue (arguments.map Data.preterm))
    (capturedPositions : applySubst bindings (.var positionsName) = indicesValue positions) :
    PureReturns program bindings state (.expression [.symbol "mm0:free-images", .var targetName,
      .var formalName, .var argumentsName, .var positionsName]) state
      (resultValue (images? target formal arguments positions)) :=
  free_images_captured_of_body bindings state state _ _ _ _ targetName formalName argumentsName positionsName _
    capturedTarget capturedFormal capturedArguments capturedPositions (images_body_returns state target formal arguments positions)

end Mettapedia.Languages.MM0.MeTTa.FreeVariableImages
