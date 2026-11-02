import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint

/-! Source-meaningful requests handled by the three existing controller
services. Failure requests carry the actual failed source pattern; ordinary
primitive faults remain results, distinct from malformed IR arguments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

inductive SourceServiceRequest (program : OCaml.Program) : Pattern → Prop where
  | primitive (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
      (rest : OCaml.Continuation) (encodedRest : Pattern) :
      continuation? (patterns program) rest = some encodedRest → operator.eval arguments = .ok result →
      SourceServiceRequest program (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
  | matchFailure (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
      (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern) :
      (patterns program)[index]? = some parameter → continuation? (patterns program) rest = some encodedRest →
      OCaml.matchPattern parameter argument = none →
      SourceServiceRequest program (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
  | clauseFailure (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
      (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern) :
      (patterns program)[index]? = some clause.pattern → clauseList? (patterns program) clauses = some later →
      continuation? (patterns program) rest = some encodedRest → OCaml.matchPattern clause.pattern argument = none →
      SourceServiceRequest program (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
