import Mettapedia.Languages.MM0.MeTTa.Kernel.FreeVariableContributions
import Mettapedia.Languages.MM0.MeTTa.Kernel.ArgumentChecking

/-!
# Free-variable traversal of the retained MM0 program

The source follows the application spine and the independent binder-sensitive
free-variable computation. Completed refusal is distinct from exhausted fuel.
Only the scoped inference cache may change while checking argument types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.FreeVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm Binder TermDecl)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open Support (indicesValue resultValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open Presentation.ComputationalFreeVariables (images? contributions? indicesSpine? indices?)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def free_spineEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 175)[174]'(by decide +kernel)
private def free_spineEnvironment (table context valueInput arguments free_lists : Atom) : Subst :=
  [("free-lists", free_lists), ("arguments", arguments), ("valueInput", valueInput), ("context", context), ("table", table)]
private theorem free_spine_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-spine") = [free_spineEquation] := by decide +kernel
private theorem free_spine_formals :
    free_spineEquation.arguments = [.var "table", .var "context", .var "valueInput", .var "arguments", .var "free-lists"] := by decide +kernel
private theorem free_spine_clause (table context valueInput arguments free_lists : Atom) :
    clauses program "mm0:free-spine" [table, context, valueInput, arguments, free_lists] =
      [.evaluate (free_spineEnvironment table context valueInput arguments free_lists) free_spineEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_spine_unique]
  simp [free_spine_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_spineEnvironment]
private theorem free_spine_captured_of_body (bindings : Subst) (before after : State)
    (table context valueInput arguments free_lists : Atom) (tableName contextName valueInputName argumentsName free_listsName : String) (answer : Atom)
    (capture_table : applySubst bindings (.var tableName) = table)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (computed : PureReturns program (free_spineEnvironment table context valueInput arguments free_lists) before free_spineEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-spine", .var tableName, .var contextName, .var valueInputName, .var argumentsName, .var free_listsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_spineEnvironment table context valueInput arguments free_lists) before after "mm0:free-spine"
    [tableName, contextName, valueInputName, argumentsName, free_listsName] free_spineEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_table, capture_context, capture_valueInput, capture_arguments, capture_free_lists] using free_spine_clause table context valueInput arguments free_lists
private def free_spineCases := casesOf free_spineEquation.body
private def free_spineBody0 : Atom := (free_spineCases[0]'(by decide +kernel)).2
private theorem free_spine_body_0_shape :
    free_spineBody0 = .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "arguments"], .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "free-lists"], .expression [.symbol "mm0:free-variable-spine", .var "view", .var "view2", .var "context", .var "index"]]] := by decide +kernel
private def free_spineBody1 : Atom := (free_spineCases[1]'(by decide +kernel)).2
private theorem free_spine_body_1_shape :
    free_spineBody1 = .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:declaration", .var "table", .var "symbol"], .expression [.symbol "mm0:free-head", .var "declaration", .var "table", .var "context", .var "arguments", .var "free-lists"]] := by decide +kernel
private def free_spineBody2 : Atom := (free_spineCases[2]'(by decide +kernel)).2
private theorem free_spine_body_2_shape :
    free_spineBody2 = .expression [.symbol "let", .var "freeSpineResult", .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "mm0:free-spine", .var "table", .var "context", .var "argument", .var "items", .var "items2"]]], .expression [.symbol "mm0:free-argument", .var "freeSpineResult", .var "table", .var "context", .var "function", .var "argument", .var "arguments", .var "free-lists"]] := by decide +kernel
private theorem free_spine_shape :
    free_spineEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_spineCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_spine_cases_shape :
    free_spineCases = [
      (.expression [.symbol "MM0:Var", .var "index"], free_spineBody0),
      (.expression [.symbol "MM0:Term", .var "symbol"], free_spineBody1),
      (.expression [.symbol "MM0:App", .var "function", .var "argument"], free_spineBody2),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_variable_spineEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 176)[175]'(by decide +kernel)
private def free_variable_spineEnvironment (valueInput free_listsInput context index : Atom) : Subst :=
  [("index", index), ("context", context), ("free-listsInput", free_listsInput), ("valueInput", valueInput)]
private theorem free_variable_spine_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-variable-spine") = [free_variable_spineEquation] := by decide +kernel
private theorem free_variable_spine_formals :
    free_variable_spineEquation.arguments = [.var "valueInput", .var "free-listsInput", .var "context", .var "index"] := by decide +kernel
private theorem free_variable_spine_clause (valueInput free_listsInput context index : Atom) :
    clauses program "mm0:free-variable-spine" [valueInput, free_listsInput, context, index] =
      [.evaluate (free_variable_spineEnvironment valueInput free_listsInput context index) free_variable_spineEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_variable_spine_unique]
  simp [free_variable_spine_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_variable_spineEnvironment]
private theorem free_variable_spine_captured_of_body (bindings : Subst) (before after : State)
    (valueInput free_listsInput context index : Atom) (valueInputName free_listsInputName contextName indexName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_free_listsInput : applySubst bindings (.var free_listsInputName) = free_listsInput)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_index : applySubst bindings (.var indexName) = index)
    (computed : PureReturns program (free_variable_spineEnvironment valueInput free_listsInput context index) before free_variable_spineEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-variable-spine", .var valueInputName, .var free_listsInputName, .var contextName, .var indexName]) after answer := by
  apply authored_variable_call_returns program bindings (free_variable_spineEnvironment valueInput free_listsInput context index) before after "mm0:free-variable-spine"
    [valueInputName, free_listsInputName, contextName, indexName] free_variable_spineEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_free_listsInput, capture_context, capture_index] using free_variable_spine_clause valueInput free_listsInput context index
private def free_variable_spineCases := casesOf free_variable_spineEquation.body
private def free_variable_spineBody0 : Atom := (free_variable_spineCases[0]'(by decide +kernel)).2
private theorem free_variable_spine_body_0_shape :
    free_variable_spineBody0 = .expression [.symbol "let", .var "var", .expression [.symbol "MM0:Var", .var "index"], .expression [.symbol "mm0:support", .var "context", .var "var"]] := by decide +kernel
private theorem free_variable_spine_shape :
    free_variable_spineEquation.body = .expression [.symbol "case", .expression [.var "valueInput", .var "free-listsInput"],
      .expression (free_variable_spineCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_variable_spine_cases_shape :
    free_variable_spineCases = [
      (.expression [.symbol "List:Nil", .symbol "List:Nil"], free_variable_spineBody0),
      (.expression [.symbol "List:Nil", .expression [.symbol "List:Cons", .var "free", .var "rest"]], .symbol "None"),
      (.expression [.expression [.symbol "List:Cons", .var "argument", .var "rest"], .var "free-lists"], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_headEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 177)[176]'(by decide +kernel)
private def free_headEnvironment (valueInput table context arguments free_lists : Atom) : Subst :=
  [("free-lists", free_lists), ("arguments", arguments), ("context", context), ("table", table), ("valueInput", valueInput)]
private theorem free_head_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-head") = [free_headEquation] := by decide +kernel
private theorem free_head_formals :
    free_headEquation.arguments = [.var "valueInput", .var "table", .var "context", .var "arguments", .var "free-lists"] := by decide +kernel
private theorem free_head_clause (valueInput table context arguments free_lists : Atom) :
    clauses program "mm0:free-head" [valueInput, table, context, arguments, free_lists] =
      [.evaluate (free_headEnvironment valueInput table context arguments free_lists) free_headEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_head_unique]
  simp [free_head_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_headEnvironment]
private theorem free_head_captured_of_body (bindings : Subst) (before after : State)
    (valueInput table context arguments free_lists : Atom) (valueInputName tableName contextName argumentsName free_listsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_table : applySubst bindings (.var tableName) = table)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (computed : PureReturns program (free_headEnvironment valueInput table context arguments free_lists) before free_headEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-head", .var valueInputName, .var tableName, .var contextName, .var argumentsName, .var free_listsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_headEnvironment valueInput table context arguments free_lists) before after "mm0:free-head"
    [valueInputName, tableName, contextName, argumentsName, free_listsName] free_headEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_table, capture_context, capture_arguments, capture_free_lists] using free_head_clause valueInput table context arguments free_lists
private def free_headCases := casesOf free_headEquation.body
private def free_headBody1 : Atom := (free_headCases[1]'(by decide +kernel)).2
private theorem free_head_body_1_shape :
    free_headBody1 = .expression [.symbol "let", .var "argumentsFit", .expression [.symbol "mm0:check-arguments", .var "table", .var "context", .var "arguments", .var "formal"], .expression [.symbol "mm0:free-typed", .var "argumentsFit", .var "context", .var "formal", .var "arguments", .var "free-lists", .var "dependencies"]] := by decide +kernel
private theorem free_head_shape :
    free_headEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_headCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_head_cases_shape :
    free_headCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression [.symbol "MM0:TermDecl", .var "formal", .var "sort", .var "dependencies"]]], free_headBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_typedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 178)[177]'(by decide +kernel)
private def free_typedEnvironment (conditionInput context formal arguments free_lists dependencies : Atom) : Subst :=
  [("dependencies", dependencies), ("free-lists", free_lists), ("arguments", arguments), ("formal", formal), ("context", context), ("conditionInput", conditionInput)]
private theorem free_typed_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-typed") = [free_typedEquation] := by decide +kernel
private theorem free_typed_formals :
    free_typedEquation.arguments = [.var "conditionInput", .var "context", .var "formal", .var "arguments", .var "free-lists", .var "dependencies"] := by decide +kernel
private theorem free_typed_clause (conditionInput context formal arguments free_lists dependencies : Atom) :
    clauses program "mm0:free-typed" [conditionInput, context, formal, arguments, free_lists, dependencies] =
      [.evaluate (free_typedEnvironment conditionInput context formal arguments free_lists dependencies) free_typedEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_typed_unique]
  simp [free_typed_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_typedEnvironment]
private theorem free_typed_captured_of_body (bindings : Subst) (before after : State)
    (conditionInput context formal arguments free_lists dependencies : Atom) (conditionInputName contextName formalName argumentsName free_listsName dependenciesName : String) (answer : Atom)
    (capture_conditionInput : applySubst bindings (.var conditionInputName) = conditionInput)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (capture_dependencies : applySubst bindings (.var dependenciesName) = dependencies)
    (computed : PureReturns program (free_typedEnvironment conditionInput context formal arguments free_lists dependencies) before free_typedEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-typed", .var conditionInputName, .var contextName, .var formalName, .var argumentsName, .var free_listsName, .var dependenciesName]) after answer := by
  apply authored_variable_call_returns program bindings (free_typedEnvironment conditionInput context formal arguments free_lists dependencies) before after "mm0:free-typed"
    [conditionInputName, contextName, formalName, argumentsName, free_listsName, dependenciesName] free_typedEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_conditionInput, capture_context, capture_formal, capture_arguments, capture_free_lists, capture_dependencies] using free_typed_clause conditionInput context formal arguments free_lists dependencies
private def free_typedCases := casesOf free_typedEquation.body
private def free_typedBody1 : Atom := (free_typedCases[1]'(by decide +kernel)).2
private theorem free_typed_body_1_shape :
    free_typedBody1 = .expression [.symbol "let", .var "freeContributionsResult", .expression [.symbol "mm0:free-contributions", .var "context", .var "formal", .var "arguments", .var "formal", .var "free-lists"], .expression [.symbol "mm0:free-contributed", .var "freeContributionsResult", .var "context", .var "formal", .var "arguments", .var "dependencies"]] := by decide +kernel
private theorem free_typed_shape :
    free_typedEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (free_typedCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_typed_cases_shape :
    free_typedCases = [
      (boolean false, .symbol "None"),
      (boolean true, free_typedBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_contributedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 179)[178]'(by decide +kernel)
private def free_contributedEnvironment (valueInput context formal arguments dependencies : Atom) : Subst :=
  [("dependencies", dependencies), ("arguments", arguments), ("formal", formal), ("context", context), ("valueInput", valueInput)]
private theorem free_contributed_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-contributed") = [free_contributedEquation] := by decide +kernel
private theorem free_contributed_formals :
    free_contributedEquation.arguments = [.var "valueInput", .var "context", .var "formal", .var "arguments", .var "dependencies"] := by decide +kernel
private theorem free_contributed_clause (valueInput context formal arguments dependencies : Atom) :
    clauses program "mm0:free-contributed" [valueInput, context, formal, arguments, dependencies] =
      [.evaluate (free_contributedEnvironment valueInput context formal arguments dependencies) free_contributedEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_contributed_unique]
  simp [free_contributed_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_contributedEnvironment]
private theorem free_contributed_captured_of_body (bindings : Subst) (before after : State)
    (valueInput context formal arguments dependencies : Atom) (valueInputName contextName formalName argumentsName dependenciesName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_dependencies : applySubst bindings (.var dependenciesName) = dependencies)
    (computed : PureReturns program (free_contributedEnvironment valueInput context formal arguments dependencies) before free_contributedEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-contributed", .var valueInputName, .var contextName, .var formalName, .var argumentsName, .var dependenciesName]) after answer := by
  apply authored_variable_call_returns program bindings (free_contributedEnvironment valueInput context formal arguments dependencies) before after "mm0:free-contributed"
    [valueInputName, contextName, formalName, argumentsName, dependenciesName] free_contributedEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_context, capture_formal, capture_arguments, capture_dependencies] using free_contributed_clause valueInput context formal arguments dependencies
private def free_contributedCases := casesOf free_contributedEquation.body
private def free_contributedBody1 : Atom := (free_contributedCases[1]'(by decide +kernel)).2
private theorem free_contributed_body_1_shape :
    free_contributedBody1 = .expression [.symbol "let", .var "freeImagesResult", .expression [.symbol "mm0:free-images", .var "context", .var "formal", .var "arguments", .var "dependencies"], .expression [.symbol "mm0:free-contribution-tail", .var "free", .var "freeImagesResult"]] := by decide +kernel
private theorem free_contributed_shape :
    free_contributedEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_contributedCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_contributed_cases_shape :
    free_contributedCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "free"], free_contributedBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_argumentEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 180)[179]'(by decide +kernel)
private def free_argumentEnvironment (valueInput table context function argument arguments free_lists : Atom) : Subst :=
  [("free-lists", free_lists), ("arguments", arguments), ("argument", argument), ("function", function), ("context", context), ("table", table), ("valueInput", valueInput)]
private theorem free_argument_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-argument") = [free_argumentEquation] := by decide +kernel
private theorem free_argument_formals :
    free_argumentEquation.arguments = [.var "valueInput", .var "table", .var "context", .var "function", .var "argument", .var "arguments", .var "free-lists"] := by decide +kernel
private theorem free_argument_clause (valueInput table context function argument arguments free_lists : Atom) :
    clauses program "mm0:free-argument" [valueInput, table, context, function, argument, arguments, free_lists] =
      [.evaluate (free_argumentEnvironment valueInput table context function argument arguments free_lists) free_argumentEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_argument_unique]
  simp [free_argument_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_argumentEnvironment]
private theorem free_argument_captured_of_body (bindings : Subst) (before after : State)
    (valueInput table context function argument arguments free_lists : Atom) (valueInputName tableName contextName functionName argumentName argumentsName free_listsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_table : applySubst bindings (.var tableName) = table)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_function : applySubst bindings (.var functionName) = function)
    (capture_argument : applySubst bindings (.var argumentName) = argument)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (computed : PureReturns program (free_argumentEnvironment valueInput table context function argument arguments free_lists) before free_argumentEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-argument", .var valueInputName, .var tableName, .var contextName, .var functionName, .var argumentName, .var argumentsName, .var free_listsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_argumentEnvironment valueInput table context function argument arguments free_lists) before after "mm0:free-argument"
    [valueInputName, tableName, contextName, functionName, argumentName, argumentsName, free_listsName] free_argumentEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_table, capture_context, capture_function, capture_argument, capture_arguments, capture_free_lists] using free_argument_clause valueInput table context function argument arguments free_lists
private def free_argumentCases := casesOf free_argumentEquation.body
private def free_argumentBody1 : Atom := (free_argumentCases[1]'(by decide +kernel)).2
private theorem free_argument_body_1_shape :
    free_argumentBody1 = .expression [.symbol "let", .var "extended", .expression [.symbol "mm0:list-cons", .var "argument", .var "arguments"], .expression [.symbol "let", .var "extended2", .expression [.symbol "mm0:list-cons", .var "free", .var "free-lists"], .expression [.symbol "mm0:free-spine", .var "table", .var "context", .var "function", .var "extended", .var "extended2"]]] := by decide +kernel
private theorem free_argument_shape :
    free_argumentEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_argumentCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_argument_cases_shape :
    free_argumentCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "free"], free_argumentBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_variablesEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 181)[180]'(by decide +kernel)
private def free_variablesEnvironment (table context source : Atom) : Subst :=
  [("source", source), ("context", context), ("table", table)]
private theorem free_variables_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-variables") = [free_variablesEquation] := by decide +kernel
private theorem free_variables_formals :
    free_variablesEquation.arguments = [.var "table", .var "context", .var "source"] := by decide +kernel
private theorem free_variables_clause (table context source : Atom) :
    clauses program "mm0:free-variables" [table, context, source] =
      [.evaluate (free_variablesEnvironment table context source) free_variablesEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_variables_unique]
  simp [free_variables_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_variablesEnvironment]
private theorem free_variables_captured_of_body (bindings : Subst) (before after : State)
    (table context source : Atom) (tableName contextName sourceName : String) (answer : Atom)
    (capture_table : applySubst bindings (.var tableName) = table)
    (capture_context : applySubst bindings (.var contextName) = context)
    (capture_source : applySubst bindings (.var sourceName) = source)
    (computed : PureReturns program (free_variablesEnvironment table context source) before free_variablesEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-variables", .var tableName, .var contextName, .var sourceName]) after answer := by
  apply authored_variable_call_returns program bindings (free_variablesEnvironment table context source) before after "mm0:free-variables"
    [tableName, contextName, sourceName] free_variablesEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_table, capture_context, capture_source] using free_variables_clause table context source
private theorem free_variables_shape :
    free_variablesEquation.body = .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "mm0:free-spine", .var "table", .var "context", .var "source", .var "items", .var "items2"]]] := by decide +kernel

private def expressionsValue (values : List Preterm) : Atom := listValue (values.map Data.preterm)
private def freeListsValue (values : List (List Nat)) : Atom := listValue (values.map indicesValue)
private def spineEnvironment (terms : Atom) (context : Context) (source : Preterm)
    (arguments : List Preterm) (freeLists : List (List Nat)) : Subst :=
  free_spineEnvironment terms (Data.context context) (Data.preterm source) (expressionsValue arguments) (freeListsValue freeLists)

private theorem contributed_body_returns (state : State) (context formal : Context) (arguments : List Preterm)
    (dependencies : List Nat) (contributed : Option (List Nat)) :
    PureReturns program (free_contributedEnvironment (resultValue contributed) (Data.context context)
      (Data.context formal) (expressionsValue arguments) (indicesValue dependencies)) state
      free_contributedEquation.body state (resultValue (do
        let free ← contributed
        let returned ← images? context formal arguments dependencies
        pure (free ++ returned))) := by
  rw [free_contributed_shape]
  let bindings := free_contributedEnvironment (resultValue contributed) (Data.context context)
    (Data.context formal) (expressionsValue arguments) (indicesValue dependencies)
  cases contributed with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_contributedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contributed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some free =>
      let bound := ("free", indicesValue free) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some free))
        free_contributedBody1 _ _ free_contributedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contributed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, free_contributedEnvironment, Subst.lookup]
      · rw [free_contributed_body_1_shape]
        let images := ("freeImagesResult", resultValue (images? context formal arguments dependencies)) :: bound
        apply let_returns program bound images state state state (.var "freeImagesResult") _ _
          (resultValue (images? context formal arguments dependencies)) _
        · exact FreeVariableImages.captured_returns bound state context formal arguments dependencies
            "context" "formal" "arguments" "dependencies"
            (by simp [bound, bindings, free_contributedEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_contributedEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_contributedEnvironment, expressionsValue, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_contributedEnvironment, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, images, bound, bindings, free_contributedEnvironment, Subst.lookup]
        · have computed := FreeVariableContributions.tail_captured_returns images state free
            (images? context formal arguments dependencies) "free" "freeImagesResult"
            (by simp [images, bound, applySubst, Subst.lookup]) rfl
          cases returned : images? context formal arguments dependencies <;> simpa [returned] using computed

private theorem typed_body_returns (state : State) (typed : Bool) (context formal : Context)
    (arguments : List Preterm) (freeLists : List (List Nat)) (dependencies : List Nat) :
    PureReturns program (free_typedEnvironment (boolean typed) (Data.context context) (Data.context formal)
      (expressionsValue arguments) (freeListsValue freeLists) (indicesValue dependencies)) state free_typedEquation.body state
      (resultValue (if typed then do
        let contributed ← contributions? context formal arguments formal freeLists
        let returned ← images? context formal arguments dependencies
        pure (contributed ++ returned)
      else none)) := by
  rw [free_typed_shape]
  let bindings := free_typedEnvironment (boolean typed) (Data.context context) (Data.context formal)
    (expressionsValue arguments) (freeListsValue freeLists) (indicesValue dependencies)
  cases typed with
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false)
        (.symbol "None") _ _ free_typedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [free_typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        free_typedBody1 _ _ free_typedCases (read_cases_encoded _)
      · exact variable_returns program bindings state "conditionInput"
      · simp [free_typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [free_typed_body_1_shape]
        let contributed := ("freeContributionsResult", resultValue (contributions? context formal arguments formal freeLists)) :: bindings
        apply let_returns program bindings contributed state state state (.var "freeContributionsResult") _ _
          (resultValue (contributions? context formal arguments formal freeLists)) _
        · exact FreeVariableContributions.captured_returns bindings state context formal arguments formal freeLists
            "context" "formal" "arguments" "formal" "free-lists" rfl rfl rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, contributed, bindings, free_typedEnvironment, Subst.lookup]
        · apply free_contributed_captured_of_body contributed state state
            (resultValue (contributions? context formal arguments formal freeLists)) (Data.context context)
            (Data.context formal) (expressionsValue arguments) (indicesValue dependencies)
            "freeContributionsResult" "context" "formal" "arguments" "dependencies" _ rfl
            (by simp [contributed, bindings, free_typedEnvironment, applySubst, Subst.lookup])
            (by simp [contributed, bindings, free_typedEnvironment, applySubst, Subst.lookup])
            (by simp [contributed, bindings, free_typedEnvironment, applySubst, Subst.lookup])
            (by simp [contributed, bindings, free_typedEnvironment, applySubst, Subst.lookup])
          exact contributed_body_returns state context formal arguments dependencies
            (contributions? context formal arguments formal freeLists)

private theorem variable_spine_body_returns (state : State) (signature : Kernel.TermSignature)
    (context : Context) (index : Nat) (arguments : List Preterm) (freeLists : List (List Nat)) :
    PureReturns program (free_variable_spineEnvironment (viewValue (arguments.map Data.preterm))
      (viewValue (freeLists.map indicesValue)) (Data.context context) (natural index)) state
      free_variable_spineEquation.body state (resultValue (indicesSpine? signature context (.var index) arguments freeLists)) := by
  rw [free_variable_spine_shape]
  let bindings := free_variable_spineEnvironment (viewValue (arguments.map Data.preterm))
    (viewValue (freeLists.map indicesValue)) (Data.context context) (natural index)
  cases arguments with
  | nil =>
      cases freeLists with
      | nil =>
          apply case_returns program bindings bindings state state state _
            (.expression [viewValue [], viewValue []]) free_variable_spineBody0 _ _ free_variable_spineCases (read_cases_encoded _)
          · exact tuple_variables_return program bindings state ["valueInput", "free-listsInput"]
          · simp [free_variable_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
          · rw [free_variable_spine_body_0_shape]
            let wrapped := ("var", Data.preterm (.var index)) :: bindings
            apply let_returns program bindings wrapped state state state (.var "var") _ _ (Data.preterm (.var index)) _
            · exact unary_constructor_returns program bindings state "MM0:Var" "index" (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, wrapped, bindings, free_variable_spineEnvironment, Subst.lookup]
            · exact Support.captured_returns wrapped state context (.var index) "context" "var"
                (by simp [wrapped, bindings, free_variable_spineEnvironment, applySubst, Subst.lookup]) rfl
      | cons free rest =>
          let bound := ("rest", freeListsValue rest) :: ("free", indicesValue free) :: bindings
          apply case_returns program bindings bound state state state _
            (.expression [viewValue [], viewValue ((free :: rest).map indicesValue)]) (.symbol "None") _ _
            free_variable_spineCases (read_cases_encoded _)
          · exact tuple_variables_return program bindings state ["valueInput", "free-listsInput"]
          · simp [free_variable_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, freeListsValue,
              bound, bindings, free_variable_spineEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"
  | cons argument rest =>
      let bound := ("free-lists", viewValue (freeLists.map indicesValue)) ::
        ("rest", expressionsValue rest) :: ("argument", Data.preterm argument) :: bindings
      apply case_returns program bindings bound state state state _
        (.expression [viewValue ((argument :: rest).map Data.preterm), viewValue (freeLists.map indicesValue)]) (.symbol "None") _ _
        free_variable_spineCases (read_cases_encoded _)
      · exact tuple_variables_return program bindings state ["valueInput", "free-listsInput"]
      · cases freeLists <;> simp [free_variable_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, expressionsValue,
          bound, bindings, free_variable_spineEnvironment, Subst.lookup]
      · exact symbol_returns program bound state "None"

private theorem head_body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (arguments : List Preterm) (freeLists : List (List Nat))
    (declaration : Option TermDecl) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (free_headEnvironment (optionValue (declaration.map Data.declaration)) (tableValue handle)
        (Data.context context) (expressionsValue arguments) (freeListsValue freeLists)) before free_headEquation.body after
        (resultValue (do
          let declaration ← declaration
          if Kernel.Substitution.checkArguments (signatureOf entries) context arguments declaration.arguments then
            let contributed ← contributions? context declaration.arguments arguments declaration.arguments freeLists
            let returned ← images? context declaration.arguments arguments (declaration.dependencies.sort (· ≤ ·))
            pure (contributed ++ returned)
          else none)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf arguments) before after := by
  cases declaration with
  | none =>
      refine ⟨before, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      rw [free_head_shape]
      let bindings := free_headEnvironment (.symbol "None") (tableValue handle)
        (Data.context context) (expressionsValue arguments) (freeListsValue freeLists)
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_headCases (read_cases_encoded _)
      · exact variable_returns program bindings before "valueInput"
      · simp [free_head_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some declaration =>
      obtain ⟨after, checked, readyAfter, frame⟩ := ArgumentChecking.returns handle cache entries uniqueRows separate
        context arguments declaration.arguments before allocated ready
      refine ⟨after, ?_, readyAfter, frame⟩
      rw [free_head_shape]
      let bindings := free_headEnvironment (optionValue (some (Data.declaration declaration))) (tableValue handle)
        (Data.context context) (expressionsValue arguments) (freeListsValue freeLists)
      let bound := ("dependencies", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) ::
        ("formal", Data.context declaration.arguments) :: bindings
      apply case_returns program bindings bound before before after (.var "valueInput")
        (optionValue (some (Data.declaration declaration))) free_headBody1 _ _ free_headCases (read_cases_encoded _)
      · exact variable_returns program bindings before "valueInput"
      · simp [free_head_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.declaration, listValue,
          bound, bindings, free_headEnvironment, Subst.lookup]
      · rw [free_head_body_1_shape]
        let fits := Kernel.Substitution.checkArguments (signatureOf entries) context arguments declaration.arguments
        let typed := ("argumentsFit", boolean fits) :: bound
        apply let_returns program bound typed before after after (.var "argumentsFit") _ _ (boolean fits) _
        · exact checked bound "table" "context" "arguments" "formal"
            (by simp [bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            rfl
            (by simp [bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, typed, bound, bindings, free_headEnvironment, Subst.lookup]
        · apply free_typed_captured_of_body typed after after (boolean fits) (Data.context context)
            (Data.context declaration.arguments) (expressionsValue arguments) (freeListsValue freeLists)
            (Data.dependencies declaration.dependencies) "argumentsFit" "context" "formal" "arguments" "free-lists" "dependencies" _ rfl
            (by simp [typed, bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            (by simp [typed, bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            (by simp [typed, bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            (by simp [typed, bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
            (by simp [typed, bound, bindings, free_headEnvironment, applySubst, Subst.lookup])
          exact typed_body_returns after fits context declaration.arguments arguments freeLists
            (declaration.dependencies.sort (· ≤ ·))

private theorem lookup_cons_ne (bindings : Subst) (key name : String) (value : Atom) (different : key ≠ name) :
    Subst.lookup ((key, value) :: bindings) name = Subst.lookup bindings name := by
  unfold Subst.lookup
  simp only [List.find?_cons]
  rw [beq_eq_false_iff_ne.mpr different]

private theorem empty_spine_returns (bindings : Subst) (before after : State) (terms : Atom)
    (context : Context) (source : Preterm) (tableName contextName sourceName : String) (answer : Atom)
    (tableFirst : tableName ≠ "items") (tableSecond : tableName ≠ "items2")
    (contextFirst : contextName ≠ "items") (contextSecond : contextName ≠ "items2")
    (sourceFirst : sourceName ≠ "items") (sourceSecond : sourceName ≠ "items2")
    (noItems : Subst.lookup bindings "items" = none) (noItems2 : Subst.lookup bindings "items2" = none)
    (capturedTable : applySubst bindings (.var tableName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedSource : applySubst bindings (.var sourceName) = Data.preterm source)
    (computed : PureReturns program (spineEnvironment terms context source [] []) before free_spineEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []],
      .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression []],
        .expression [.symbol "mm0:free-spine", .var tableName, .var contextName, .var sourceName, .var "items", .var "items2"]]]) after answer := by
  let first := ("items", expressionsValue []) :: bindings
  let second := ("items2", freeListsValue []) :: first
  apply let_returns program bindings first before before after (.var "items") _ _ (expressionsValue []) _
  · exact empty_constructor_returns program bindings before "MM0:L" list_is_data_constructor (by decide)
  · simp [SpaceSemantics.matchValue, matchAtom, first, noItems]
  · apply let_returns program first second before before after (.var "items2") _ _ (freeListsValue []) _
    · exact empty_constructor_returns program first before "MM0:L" list_is_data_constructor (by decide)
    · simp only [SpaceSemantics.matchBinding_var, SpaceSemantics.matchValue, matchAtom]
      have absent : Subst.lookup first "items2" = none := by
        dsimp only [first]
        rw [lookup_cons_ne bindings "items" "items2" (expressionsValue []) (by decide)]
        exact noItems2
      simp [absent, second]
    · apply free_spine_captured_of_body second before after terms (Data.context context) (Data.preterm source)
        (expressionsValue []) (freeListsValue []) tableName contextName sourceName "items" "items2" _
        _ _ _ _ rfl computed
      · simpa only [second, first, applySubst,
          lookup_cons_ne _ "items2" tableName _ (Ne.symm tableSecond),
          lookup_cons_ne _ "items" tableName _ (Ne.symm tableFirst)] using capturedTable
      · simpa only [second, first, applySubst,
          lookup_cons_ne _ "items2" contextName _ (Ne.symm contextSecond),
          lookup_cons_ne _ "items" contextName _ (Ne.symm contextFirst)] using capturedContext
      · simpa only [second, first, applySubst,
          lookup_cons_ne _ "items2" sourceName _ (Ne.symm sourceSecond),
          lookup_cons_ne _ "items" sourceName _ (Ne.symm sourceFirst)] using capturedSource
      · simp [second, first, applySubst, Subst.lookup]

private theorem argument_none_body_returns (state : State) (terms : Atom) (context : Context)
    (function argument : Preterm) (arguments : List Preterm) (freeLists : List (List Nat)) :
    PureReturns program (free_argumentEnvironment (.symbol "None") terms (Data.context context)
      (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)) state
      free_argumentEquation.body state (.symbol "None") := by
  rw [free_argument_shape]
  let bindings := free_argumentEnvironment (.symbol "None") terms (Data.context context)
    (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
    (.symbol "None") _ _ free_argumentCases (read_cases_encoded _)
  · exact variable_returns program bindings state "valueInput"
  · simp [free_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem argument_some_body_returns (before after : State) (terms : Atom) (context : Context)
    (function argument : Preterm) (arguments : List Preterm) (freeLists : List (List Nat)) (free : List Nat) (answer : Atom)
    (recursive : PureReturns program (spineEnvironment terms context function (argument :: arguments) (free :: freeLists))
      before free_spineEquation.body after answer) :
    PureReturns program (free_argumentEnvironment (resultValue (some free)) terms (Data.context context)
      (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)) before
      free_argumentEquation.body after answer := by
  rw [free_argument_shape]
  let bindings := free_argumentEnvironment (resultValue (some free)) terms (Data.context context)
    (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)
  let bound := ("free", indicesValue free) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (resultValue (some free))
    free_argumentBody1 _ _ free_argumentCases (read_cases_encoded _)
  · exact variable_returns program bindings before "valueInput"
  · simp [free_argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
      bound, bindings, free_argumentEnvironment, Subst.lookup]
  · rw [free_argument_body_1_shape]
    let extended := ("extended", expressionsValue (argument :: arguments)) :: bound
    let extended2 := ("extended2", freeListsValue (free :: freeLists)) :: extended
    apply let_returns program bound extended before before after (.var "extended") _ _ (expressionsValue (argument :: arguments)) _
    · exact ListAccess.cons_captured_returns bound before (Data.preterm argument) (arguments.map Data.preterm)
        "argument" "arguments" (by simp [bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup, expressionsValue])
    · simp [SpaceSemantics.matchValue, matchAtom, extended, bound, bindings, free_argumentEnvironment, Subst.lookup]
    · apply let_returns program extended extended2 before before after (.var "extended2") _ _ (freeListsValue (free :: freeLists)) _
      · exact ListAccess.cons_captured_returns extended before (indicesValue free) (freeLists.map indicesValue)
          "free" "free-lists" (by simp [extended, bound, applySubst, Subst.lookup])
          (by simp [extended, bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup, freeListsValue])
      · simp [SpaceSemantics.matchValue, matchAtom, extended2, extended, bound, bindings, free_argumentEnvironment, Subst.lookup]
      · exact free_spine_captured_of_body extended2 before after terms (Data.context context) (Data.preterm function)
          (expressionsValue (argument :: arguments)) (freeListsValue (free :: freeLists))
          "table" "context" "function" "extended" "extended2" _
          (by simp [extended2, extended, bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup])
          (by simp [extended2, extended, bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup])
          (by simp [extended2, extended, bound, bindings, free_argumentEnvironment, applySubst, Subst.lookup])
          (by simp [extended2, extended, applySubst, Subst.lookup]) rfl recursive

private theorem application_body_returns (bindings : Subst) (before middle after : State) (terms : Atom) (context : Context)
    (function argument : Preterm) (arguments : List Preterm) (freeLists : List (List Nat)) (free : Option (List Nat)) (answer : Atom)
    (capturedTable : applySubst bindings (.var "table") = terms)
    (capturedContext : applySubst bindings (.var "context") = Data.context context)
    (capturedFunction : applySubst bindings (.var "function") = Data.preterm function)
    (capturedArgument : applySubst bindings (.var "argument") = Data.preterm argument)
    (capturedArguments : applySubst bindings (.var "arguments") = expressionsValue arguments)
    (capturedFreeLists : applySubst bindings (.var "free-lists") = freeListsValue freeLists)
    (noItems : Subst.lookup bindings "items" = none) (noItems2 : Subst.lookup bindings "items2" = none)
    (noResult : Subst.lookup bindings "freeSpineResult" = none)
    (child : PureReturns program (spineEnvironment terms context argument [] []) before free_spineEquation.body middle (resultValue free))
    (handled : PureReturns program (free_argumentEnvironment (resultValue free) terms (Data.context context)
      (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)) middle
      free_argumentEquation.body after answer) :
    PureReturns program bindings before free_spineBody2 after answer := by
  rw [free_spine_body_2_shape]
  let bound := ("freeSpineResult", resultValue free) :: bindings
  apply let_returns program bindings bound before middle after (.var "freeSpineResult") _ _ (resultValue free) _
  · exact empty_spine_returns bindings before middle terms context argument "table" "context" "argument" _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      noItems noItems2
      capturedTable capturedContext capturedArgument child
  · simp [SpaceSemantics.matchValue, matchAtom, bound, noResult]
  · exact free_argument_captured_of_body bound middle after (resultValue free) terms (Data.context context)
      (Data.preterm function) (Data.preterm argument) (expressionsValue arguments) (freeListsValue freeLists)
      "freeSpineResult" "table" "context" "function" "argument" "arguments" "free-lists" _ rfl
      (by simpa [bound, applySubst, Subst.lookup] using capturedTable)
      (by simpa [bound, applySubst, Subst.lookup] using capturedContext)
      (by simpa [bound, applySubst, Subst.lookup] using capturedFunction)
      (by simpa [bound, applySubst, Subst.lookup] using capturedArgument)
      (by simpa [bound, applySubst, Subst.lookup] using capturedArguments)
      (by simpa [bound, applySubst, Subst.lookup] using capturedFreeLists) handled

theorem spine_body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (arguments : List Preterm) (freeLists : List (List Nat)) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (spineEnvironment (tableValue handle) context source arguments freeLists)
        before free_spineEquation.body after (resultValue (indicesSpine? (signatureOf entries) context source arguments freeLists)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf source + sizeOf arguments) before after := by
  induction source generalizing arguments freeLists before with
  | var index =>
      refine ⟨before, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      rw [free_spine_shape]
      let bindings := spineEnvironment (tableValue handle) context (.var index) arguments freeLists
      let bound := ("index", natural index) :: bindings
      apply case_returns program bindings bound before before before (.var "valueInput") (Data.preterm (.var index))
        free_spineBody0 _ _ free_spineCases (read_cases_encoded _)
      · exact variable_returns program bindings before "valueInput"
      · simp [free_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
      · rw [free_spine_body_0_shape]
        let viewed := ("view", viewValue (arguments.map Data.preterm)) :: bound
        let both := ("view2", viewValue (freeLists.map indicesValue)) :: viewed
        apply let_returns program bound viewed before before before (.var "view") _ _ (viewValue (arguments.map Data.preterm)) _
        · exact ListAccess.view_captured_returns bound before "arguments" (arguments.map Data.preterm)
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, expressionsValue, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
        · apply let_returns program viewed both before before before (.var "view2") _ _ (viewValue (freeLists.map indicesValue)) _
          · exact ListAccess.view_captured_returns viewed before "free-lists" (freeLists.map indicesValue)
              (by simp [viewed, bound, bindings, spineEnvironment, free_spineEnvironment, freeListsValue, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchValue, matchAtom, both, viewed, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
          · exact free_variable_spine_captured_of_body both before before (viewValue (arguments.map Data.preterm))
              (viewValue (freeLists.map indicesValue)) (Data.context context) (natural index) "view" "view2" "context" "index" _
              (by simp [both, viewed, applySubst, Subst.lookup]) rfl
              (by simp [both, viewed, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
              (by simp [both, viewed, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
              (variable_spine_body_returns before (signatureOf entries) context index arguments freeLists)
  | term symbol =>
      obtain ⟨after, computed, readyAfter, frame⟩ := head_body_returns handle cache entries uniqueRows separate
        context arguments freeLists (signatureOf entries symbol) before allocated ready
      refine ⟨after, ?_, readyAfter, frame.weaken (by omega)⟩
      rw [free_spine_shape]
      let bindings := spineEnvironment (tableValue handle) context (.term symbol) arguments freeLists
      let bound := ("symbol", natural symbol) :: bindings
      apply case_returns program bindings bound before before after (.var "valueInput") (Data.preterm (.term symbol))
        free_spineBody1 _ _ free_spineCases (read_cases_encoded _)
      · exact variable_returns program bindings before "valueInput"
      · simp [free_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
      · rw [free_spine_body_1_shape]
        let found := ("declaration", optionValue ((signatureOf entries symbol).map Data.declaration)) :: bound
        apply let_returns program bound found before before after (.var "declaration") _ _
          (optionValue ((signatureOf entries symbol).map Data.declaration)) _
        · exact TableAccess.declaration_signature_returns bound before handle entries symbol "table" "symbol" uniqueRows allocated
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup]) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, found, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
        · apply free_head_captured_of_body found before after (optionValue ((signatureOf entries symbol).map Data.declaration))
            (tableValue handle) (Data.context context) (expressionsValue arguments) (freeListsValue freeLists)
            "declaration" "table" "context" "arguments" "free-lists" _ rfl
            (by simp [found, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [found, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [found, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [found, bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
          exact computed
  | app function argument ihFunction ihArgument =>
      obtain ⟨middle, child, readyMiddle, frameChild⟩ := ihArgument [] [] before allocated ready
      have allocatedMiddle : middle.read handle = some (declarationRows entries) := by
        rw [frameChild.other handle separate]
        exact allocated
      have childBound : sizeOf argument + sizeOf ([] : List Preterm) ≤ sizeOf (Preterm.app function argument) + sizeOf arguments := by
        simp
        omega
      have lift (after : State)
          (handled : PureReturns program (free_argumentEnvironment (resultValue (indicesSpine? (signatureOf entries) context argument [] []))
            (tableValue handle) (Data.context context) (Data.preterm function) (Data.preterm argument)
            (expressionsValue arguments) (freeListsValue freeLists)) middle free_argumentEquation.body after
              (resultValue (indicesSpine? (signatureOf entries) context (.app function argument) arguments freeLists)))
          (readyAfter : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after)
          (frame : InferenceCache.Frame cache (tableValue handle) (sizeOf (Preterm.app function argument) + sizeOf arguments) middle after) :
          ∃ after,
            PureReturns program (spineEnvironment (tableValue handle) context (.app function argument) arguments freeLists)
              before free_spineEquation.body after (resultValue (indicesSpine? (signatureOf entries) context (.app function argument) arguments freeLists)) ∧
            InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
            InferenceCache.Frame cache (tableValue handle) (sizeOf (Preterm.app function argument) + sizeOf arguments) before after := by
        refine ⟨after, ?_, readyAfter, (frameChild.weaken childBound).trans frame⟩
        rw [free_spine_shape]
        let bindings := spineEnvironment (tableValue handle) context (.app function argument) arguments freeLists
        let bound := ("argument", Data.preterm argument) :: ("function", Data.preterm function) :: bindings
        apply case_returns program bindings bound before before after (.var "valueInput") (Data.preterm (.app function argument))
          free_spineBody2 _ _ free_spineCases (read_cases_encoded _)
        · exact variable_returns program bindings before "valueInput"
        · simp [free_spine_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]
        · exact application_body_returns bound before middle after (tableValue handle) context function argument arguments freeLists
            (indicesSpine? (signatureOf entries) context argument [] []) _
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [bound, applySubst, Subst.lookup]) rfl
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, applySubst, Subst.lookup])
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup])
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup])
            (by simp [bound, bindings, spineEnvironment, free_spineEnvironment, Subst.lookup]) child handled
      cases first : indicesSpine? (signatureOf entries) context argument [] [] with
      | none =>
          apply lift middle _ readyMiddle (InferenceCache.Frame.refl _ _ _ _)
          simpa [first, indicesSpine?, resultValue, optionValue] using
            argument_none_body_returns middle (tableValue handle) context function argument arguments freeLists
      | some free =>
          obtain ⟨after, computed, readyAfter, frame⟩ := ihFunction (argument :: arguments) (free :: freeLists)
            middle allocatedMiddle readyMiddle
          apply lift after _ readyAfter (frame.weaken (by simp; omega))
          simpa [first, indicesSpine?] using
            argument_some_body_returns middle after (tableValue handle) context function argument arguments freeLists free _ computed

theorem body_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      PureReturns program (free_variablesEnvironment (tableValue handle) (Data.context context) (Data.preterm source)) before
        free_variablesEquation.body after (resultValue (indices? (signatureOf entries) context source)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf source + 1) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := spine_body_returns handle cache entries uniqueRows separate
    context source [] [] before allocated ready
  refine ⟨after, ?_, readyAfter, by simpa using frame⟩
  rw [free_variables_shape]
  let bindings := free_variablesEnvironment (tableValue handle) (Data.context context) (Data.preterm source)
  exact empty_spine_returns bindings before after (tableValue handle) context source "table" "context" "source" _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl computed

theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after,
      (∀ bindings tableName contextName sourceName,
        applySubst bindings (.var tableName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var sourceName) = Data.preterm source →
        PureReturns program bindings before (.expression [.symbol "mm0:free-variables", .var tableName,
          .var contextName, .var sourceName]) after (resultValue (indices? (signatureOf entries) context source))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf source + 1) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := body_returns handle cache entries uniqueRows separate context source before allocated ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings tableName contextName sourceName tableCaptured contextCaptured sourceCaptured
  exact free_variables_captured_of_body bindings before after _ _ _ tableName contextName sourceName _
    tableCaptured contextCaptured sourceCaptured computed

def requestConfiguration (state : State) (handle : Handle) (context : Context) (source : Preterm) : Configuration :=
  { state, control := .evaluate (free_variablesEnvironment (tableValue handle) (Data.context context) (Data.preterm source))
      (.expression [.symbol "mm0:free-variables", .var "table", .var "context", .var "source"]) }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before handle context source) =
        .complete after [resultValue (indices? (signatureOf entries) context source)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf source + 1) before after := by
  obtain ⟨after, computed, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate context source before allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (free_variablesEnvironment (tableValue handle) (Data.context context) (Data.preterm source)) before after _ _
    (computed _ "table" "context" "source" rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) (answer : Option (List Nat)) :
    indices? (signatureOf entries) context source = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration before handle context source) =
        .complete after [resultValue answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel handle cache entries uniqueRows separate context source before allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact Support.resultValue_injective (List.singleton_inj.mp same.2.1)

theorem free_variables_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) (free : Finset Nat) :
    Preterm.FreeVars (signatureOf entries) context source free ↔
      ∃ indices after fuel, indices.toFinset = free ∧
        run program fuel (requestConfiguration before handle context source) =
          .complete after [resultValue (some indices)] [] [] := by
  constructor
  · intro known
    obtain ⟨indices, computed, interpreted⟩ := Presentation.ComputationalFreeVariables.indices_complete known
    obtain ⟨after, fuel, returned⟩ := (result_iff_source_returns handle cache entries uniqueRows separate context source before allocated ready (some indices)).mp computed
    exact ⟨indices, after, fuel, interpreted, returned⟩
  · rintro ⟨indices, after, fuel, interpreted, returned⟩
    have computed := (result_iff_source_returns handle cache entries uniqueRows separate context source before allocated ready (some indices)).mpr ⟨after, fuel, returned⟩
    rw [← interpreted]
    exact Presentation.ComputationalFreeVariables.indices_sound computed

theorem refusal_iff_source_returns_none (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    (¬ ∃ free, Preterm.FreeVars (signatureOf entries) context source free) ↔
      ∃ after fuel, run program fuel (requestConfiguration before handle context source) =
        .complete after [.symbol "None"] [] [] := by
  rw [← Presentation.ComputationalFreeVariables.indices_refusal_iff]
  exact result_iff_source_returns handle cache entries uniqueRows separate context source before allocated ready none

theorem free_variables_iff_gslt_path (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) (free : Finset Nat) :
    Preterm.FreeVars (signatureOf entries) context source free ↔
      ∃ indices after, indices.toFinset = free ∧
        (theory program).MultiStep (requestConfiguration before handle context source)
          (finished after [resultValue (some indices)] [] []) := by
  rw [free_variables_iff_source_returns handle cache entries uniqueRows separate context source before allocated ready free]
  constructor
  · rintro ⟨indices, after, fuel, interpreted, returned⟩
    exact ⟨indices, after, interpreted, (completed_run_iff_path program _ after _ [] []).mp ⟨fuel, returned⟩⟩
  · rintro ⟨indices, after, interpreted, path⟩
    obtain ⟨fuel, returned⟩ := (completed_run_iff_path program _ after _ [] []).mpr path
    exact ⟨indices, after, fuel, interpreted, returned⟩

/-- Any completed execution has the same result and the derived store frame;
the statement applies to the observed execution, not only to a chosen witness. -/
theorem completed_frame (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (source : Preterm) (before : State)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before)
    (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration before handle context source) = .complete after answers [] []) :
    InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf source + 1) before after ∧
      answers = [resultValue (indices? (signatureOf entries) context source)] := by
  obtain ⟨reference, referenceFuel, completed, readyReference, frame⟩ := sufficient_fuel handle cache entries uniqueRows separate context source before allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  exact ⟨same.1 ▸ readyReference, same.1 ▸ frame, same.2.1.symm⟩

theorem bound_variable_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache) (sort : Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel, run program fuel (requestConfiguration state handle [.bound sort] (.var 0)) =
      .complete after [resultValue (some [0])] [] [] :=
  (result_iff_source_returns handle cache entries uniqueRows separate [.bound sort] (.var 0) state allocated ready (some [0])).mp rfl

theorem missing_variable_refuses (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel, run program fuel (requestConfiguration state handle [] (.var 0)) =
      .complete after [.symbol "None"] [] [] :=
  (result_iff_source_returns handle cache entries uniqueRows separate [] (.var 0) state allocated ready none).mp rfl

end Mettapedia.Languages.MM0.MeTTa.FreeVariables
