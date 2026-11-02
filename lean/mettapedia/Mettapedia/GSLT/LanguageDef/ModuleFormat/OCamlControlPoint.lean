import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateEncoding
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn

/-! Relate emitted administrative configurations to the independent source
machine state they finish realizing. The rank measures administrative
work only; executing a source step may start a new administrative phase.
No source transition or runtime executor is defined here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

inductive ControlPoint (program : OCaml.Program) : OCaml.MachineState → Pattern → Nat → Prop where
  | state {source : OCaml.MachineState} {target : Pattern} :
      state? (patterns program) source = some target → ControlPoint program source target 0
  | application {function argument : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
      {next : OCaml.MachineState} :
      continuation? (patterns program) rest = some encodedRest →
      OCaml.applyClosure program function argument rest = .ok next →
      ControlPoint program next (node "MlApply" [value function, value argument, encodedRest]) 2
  | matchOne {index : Nat} {parameter : OCaml.MatchPattern} {argument : OCaml.Value} {body : OCaml.Code}
      {captured : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern} :
      (patterns program)[index]? = some parameter →
      continuation? (patterns program) rest = some encodedRest →
      ControlPoint program (OCaml.enterBody parameter argument body captured rest)
        (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) 1
  | select {clauses : List OCaml.Clause} {encodedClauses : Pattern} {argument : OCaml.Value}
      {captured : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern} {next : OCaml.MachineState} :
      clauseList? (patterns program) clauses = some encodedClauses →
      continuation? (patterns program) rest = some encodedRest →
      OCaml.returnValue program argument (.matchValue clauses captured :: rest) = .ok next →
      ControlPoint program next (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest])
        (2 * clauses.length + 1)
  | clause {index : Nat} {clause : OCaml.Clause} {clauses : List OCaml.Clause} {later : Pattern}
      {argument : OCaml.Value} {captured : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern}
      {next : OCaml.MachineState} :
      (patterns program)[index]? = some clause.pattern →
      clauseList? (patterns program) clauses = some later →
      continuation? (patterns program) rest = some encodedRest →
      OCaml.returnValue program argument (.matchValue (clause :: clauses) captured :: rest) = .ok next →
      ControlPoint program next
        (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
        (2 * clauses.length + 2)
  | build {kind : OCaml.Build} {items : List OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
      {next : OCaml.MachineState} :
      continuation? (patterns program) rest = some encodedRest →
      OCaml.finishBuild program kind items rest = .ok next →
      ControlPoint program next (node "MlBuildConfig" [build kind, valueList items, encodedRest]) 3
  | primitive {operator : OCaml.Primitive} {arguments : List OCaml.Value} {result : OCaml.Result}
      {rest : OCaml.Continuation} {encodedRest : Pattern} :
      continuation? (patterns program) rest = some encodedRest →
      operator.eval arguments = .ok result →
      ControlPoint program (finishPrimitive result rest)
        (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) 2
  | answer {result : OCaml.Result} {rest : OCaml.Continuation} {encodedRest : Pattern} :
      continuation? (patterns program) rest = some encodedRest →
      ControlPoint program (finishPrimitive result rest) (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) 1

theorem initial_control_point (program : OCaml.Program) : ControlPoint program (OCaml.begin program) (initial program) 0 :=
  .state (initial_state program (patterns program))

theorem return_function_source_point (program : OCaml.Program) (function argument : OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (next : OCaml.MachineState)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (applied : OCaml.applyClosure program function argument rest = .ok next) :
    OCaml.machineStep program (.returned function (.function argument :: rest)) = .ok (some next) ∧
      ControlPoint program next (node "MlApply" [value function, value argument, encodedRest]) 2 := by
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue, applied]
    rfl
  · exact .application resolved applied

theorem return_let_source_point (program : OCaml.Program) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (indexed : (patterns program)[index]? = some parameter)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.returned argument (.letValue parameter body captured :: rest)) =
      .ok (some (OCaml.enterBody parameter argument body captured rest)) ∧
    ControlPoint program (OCaml.enterBody parameter argument body captured rest)
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) 1 := by
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue]
    rfl
  · exact .matchOne indexed resolved

theorem return_match_source_point (program : OCaml.Program) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (next : OCaml.MachineState) (listed : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (selected : OCaml.returnValue program argument (.matchValue clauses captured :: rest) = .ok next) :
    OCaml.machineStep program (.returned argument (.matchValue clauses captured :: rest)) = .ok (some next) ∧
    ControlPoint program next (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest])
      (2 * clauses.length + 1) := by
  constructor
  · simp only [OCaml.machineStep, selected]
    rfl
  · exact .select listed resolved selected

#print axioms initial_control_point
#print axioms return_function_source_point
#print axioms return_let_source_point
#print axioms return_match_source_point

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
