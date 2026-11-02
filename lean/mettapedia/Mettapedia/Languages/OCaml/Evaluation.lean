import Mettapedia.Languages.OCaml.PatternMatching
import Mettapedia.Languages.OCaml.Primitives

/-! Finite evaluation judgments for the indexed pure OCaml core. These
judgments do not call the environment machine, its step function or its
budgeted runner. Argument judgments evaluate the tail before the head.
Faults are source observations; malformed code has no evaluation derivation.
Machine and emitted execution adequacy are separate theorems. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  inductive Evaluates (program : Program) : Environment → Code → Result → Prop where
    | literal {environment code value}
        (instruction : program.instruction? code = some (.literal value)) :
        Evaluates program environment code (.ok (.literal value))
    | variable {environment code index value}
        (instruction : program.instruction? code = some (.variable index))
        (binding : environment[index]? = some value) :
        Evaluates program environment code (.ok value)
    | lambda {environment code parameter body}
        (instruction : program.instruction? code = some (.lambda parameter body)) :
        Evaluates program environment code (.ok (.closure (.lambda code) environment))
    | recursive {environment code definitions body result}
        (instruction : program.instruction? code = some (.letRecursive definitions body))
        (evaluated : Evaluates program (recursiveEnvironment code definitions environment) body result) :
        Evaluates program environment code result
    | argumentFault {environment code function argument fault}
        (instruction : program.instruction? code = some (.apply function argument))
        (evaluated : Evaluates program environment argument (.error fault)) :
        Evaluates program environment code (.error fault)
    | functionFault {environment code function argument actual fault}
        (instruction : program.instruction? code = some (.apply function argument))
        (argumentValue : Evaluates program environment argument (.ok actual))
        (evaluated : Evaluates program environment function (.error fault)) :
        Evaluates program environment code (.error fault)
    | application {environment code function argument actual callable result}
        (instruction : program.instruction? code = some (.apply function argument))
        (argumentValue : Evaluates program environment argument (.ok actual))
        (functionValue : Evaluates program environment function (.ok callable))
        (applied : Applies program callable actual result) :
        Evaluates program environment code result
    | letFault {environment code pattern value body fault}
        (instruction : program.instruction? code = some (.letValue pattern value body))
        (evaluated : Evaluates program environment value (.error fault)) :
        Evaluates program environment code (.error fault)
    | letMismatch {environment code pattern value body actual}
        (instruction : program.instruction? code = some (.letValue pattern value body))
        (evaluated : Evaluates program environment value (.ok actual))
        (mismatch : matchPattern pattern actual = none) :
        Evaluates program environment code (.error .matchFailure)
    | letBody {environment code pattern value body actual bindings result}
        (instruction : program.instruction? code = some (.letValue pattern value body))
        (evaluated : Evaluates program environment value (.ok actual))
        (matched : matchPattern pattern actual = some bindings)
        (continued : Evaluates program (extend environment bindings) body result) :
        Evaluates program environment code result
    | conditionFault {environment code condition yes no fault}
        (instruction : program.instruction? code = some (.branch condition yes no))
        (evaluated : Evaluates program environment condition (.error fault)) :
        Evaluates program environment code (.error fault)
    | branch {environment code condition yes no choice result}
        (instruction : program.instruction? code = some (.branch condition yes no))
        (evaluated : Evaluates program environment condition (.ok (.literal (.boolean choice))))
        (continued : Evaluates program environment (if choice then yes else no) result) :
        Evaluates program environment code result
    | andFault {environment code left right fault}
        (instruction : program.instruction? code = some (.andThen left right))
        (evaluated : Evaluates program environment left (.error fault)) :
        Evaluates program environment code (.error fault)
    | andFalse {environment code left right}
        (instruction : program.instruction? code = some (.andThen left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean false)))) :
        Evaluates program environment code (.ok (.literal (.boolean false)))
    | andRightFault {environment code left right fault}
        (instruction : program.instruction? code = some (.andThen left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean true))))
        (continued : Evaluates program environment right (.error fault)) :
        Evaluates program environment code (.error fault)
    | andRightValue {environment code left right value}
        (instruction : program.instruction? code = some (.andThen left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean true))))
        (continued : Evaluates program environment right (.ok (.literal (.boolean value)))) :
        Evaluates program environment code (.ok (.literal (.boolean value)))
    | orFault {environment code left right fault}
        (instruction : program.instruction? code = some (.orElse left right))
        (evaluated : Evaluates program environment left (.error fault)) :
        Evaluates program environment code (.error fault)
    | orTrue {environment code left right}
        (instruction : program.instruction? code = some (.orElse left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean true)))) :
        Evaluates program environment code (.ok (.literal (.boolean true)))
    | orRightFault {environment code left right fault}
        (instruction : program.instruction? code = some (.orElse left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean false))))
        (continued : Evaluates program environment right (.error fault)) :
        Evaluates program environment code (.error fault)
    | orRightValue {environment code left right value}
        (instruction : program.instruction? code = some (.orElse left right))
        (evaluated : Evaluates program environment left (.ok (.literal (.boolean false))))
        (continued : Evaluates program environment right (.ok (.literal (.boolean value)))) :
        Evaluates program environment code (.ok (.literal (.boolean value)))
    | consTailFault {environment code head tail fault}
        (instruction : program.instruction? code = some (.cons head tail))
        (evaluated : Evaluates program environment tail (.error fault)) :
        Evaluates program environment code (.error fault)
    | consHeadFault {environment code head tail tailValue fault}
        (instruction : program.instruction? code = some (.cons head tail))
        (last : Evaluates program environment tail (.ok tailValue))
        (first : Evaluates program environment head (.error fault)) :
        Evaluates program environment code (.error fault)
    | cons {environment code head tail first last}
        (instruction : program.instruction? code = some (.cons head tail))
        (tailValue : Evaluates program environment tail (.ok last))
        (headValue : Evaluates program environment head (.ok first)) :
        Evaluates program environment code (.ok (.cons first last))
    | tupleFault {environment code fields fault}
        (instruction : program.instruction? code = some (.tuple fields))
        (evaluated : EvaluatesArguments program environment fields (.error fault)) :
        Evaluates program environment code (.error fault)
    | tuple {environment code fields values}
        (instruction : program.instruction? code = some (.tuple fields))
        (evaluated : EvaluatesArguments program environment fields (.ok values))
        (arity : 2 ≤ values.length) :
        Evaluates program environment code (.ok (.tuple values))
    | variantFault {environment code typeId constructor fields fault}
        (instruction : program.instruction? code = some (.variant typeId constructor fields))
        (evaluated : EvaluatesArguments program environment fields (.error fault)) :
        Evaluates program environment code (.error fault)
    | variant {environment code typeId constructor fields values}
        (instruction : program.instruction? code = some (.variant typeId constructor fields))
        (evaluated : EvaluatesArguments program environment fields (.ok values))
        (declaration : ⟨typeId, constructor, values.length⟩ ∈ program.constructors) :
        Evaluates program environment code (.ok (.variant typeId constructor values))
    | primitiveFault {environment code operator arguments fault}
        (instruction : program.instruction? code = some (.primitive operator arguments))
        (evaluated : EvaluatesArguments program environment arguments (.error fault)) :
        Evaluates program environment code (.error fault)
    | primitive {environment code operator arguments values result}
        (instruction : program.instruction? code = some (.primitive operator arguments))
        (evaluated : EvaluatesArguments program environment arguments (.ok values))
        (calculated : operator.eval values = .ok result) :
        Evaluates program environment code result
    | matchFault {environment code scrutinee clauses fault}
        (instruction : program.instruction? code = some (.matchValue scrutinee clauses))
        (evaluated : Evaluates program environment scrutinee (.error fault)) :
        Evaluates program environment code (.error fault)
    | matchFailure {environment code scrutinee clauses value}
        (instruction : program.instruction? code = some (.matchValue scrutinee clauses))
        (evaluated : Evaluates program environment scrutinee (.ok value))
        (mismatch : selectClause clauses value = none) :
        Evaluates program environment code (.error .matchFailure)
    | matchBody {environment code scrutinee clauses value body bindings result}
        (instruction : program.instruction? code = some (.matchValue scrutinee clauses))
        (evaluated : Evaluates program environment scrutinee (.ok value))
        (selected : selectClause clauses value = some (body, bindings))
        (continued : Evaluates program (extend environment bindings) body result) :
        Evaluates program environment code result

  inductive Applies (program : Program) : Value → Value → Result → Prop where
    | lambda {code parameter body captured argument bindings result}
        (instruction : program.instruction? code = some (.lambda parameter body))
        (matched : matchPattern parameter argument = some bindings)
        (evaluated : Evaluates program (extend captured bindings) body result) :
        Applies program (.closure (.lambda code) captured) argument result
    | lambdaMismatch {code parameter body captured argument}
        (instruction : program.instruction? code = some (.lambda parameter body))
        (mismatch : matchPattern parameter argument = none) :
        Applies program (.closure (.lambda code) captured) argument (.error .matchFailure)
    | recursive {group slot definitions groupBody code parameter body captured argument bindings result}
        (groupInstruction : program.instruction? group = some (.letRecursive definitions groupBody))
        (definition : definitions[slot]? = some code)
        (instruction : program.instruction? code = some (.lambda parameter body))
        (matched : matchPattern parameter argument = some bindings)
        (evaluated : Evaluates program
          (extend (recursiveEnvironment group definitions captured) bindings) body result) :
        Applies program (.closure (.recursive group slot) captured) argument result
    | recursiveMismatch {group slot definitions groupBody code parameter body captured argument}
        (groupInstruction : program.instruction? group = some (.letRecursive definitions groupBody))
        (definition : definitions[slot]? = some code)
        (instruction : program.instruction? code = some (.lambda parameter body))
        (mismatch : matchPattern parameter argument = none) :
        Applies program (.closure (.recursive group slot) captured) argument (.error .matchFailure)

  inductive EvaluatesArguments (program : Program) :
      Environment → List Code → Except Fault (List Value) → Prop where
    | nil {environment} : EvaluatesArguments program environment [] (.ok [])
    | tailFault {environment first rest fault}
        (last : EvaluatesArguments program environment rest (.error fault)) :
        EvaluatesArguments program environment (first :: rest) (.error fault)
    | headFault {environment first rest values fault}
        (last : EvaluatesArguments program environment rest (.ok values))
        (head : Evaluates program environment first (.error fault)) :
        EvaluatesArguments program environment (first :: rest) (.error fault)
    | cons {environment first rest value values}
        (last : EvaluatesArguments program environment rest (.ok values))
        (head : Evaluates program environment first (.ok value)) :
        EvaluatesArguments program environment (first :: rest) (.ok (value :: values))
end

end Mettapedia.Languages.OCaml
