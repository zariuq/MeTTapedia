import Mettapedia.Languages.OCaml.TreePatternMatching
import Mettapedia.Languages.OCaml.Primitives

/-! Finite operational judgments for unallocated expression trees. Closures
carry tree bodies and captures. The rules do not call assembly, code lookup,
the indexed evaluator or a budgeted runner. The shared primitive profile is
used only through its data/function-presence operand view. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive TreePrimitive (operator : Primitive) (arguments : List TreeValue) : TreeResult → Prop where
  | literal {value : Literal}
      (calculated : operator.eval (arguments.map TreeValue.primitiveOperand) = .ok (.ok (.literal value))) :
      TreePrimitive operator arguments (.ok (.literal value))
  | fault {error : Fault}
      (calculated : operator.eval (arguments.map TreeValue.primitiveOperand) = .ok (.error error)) :
      TreePrimitive operator arguments (.error error)

mutual
  inductive TreeEvaluates (constructors : List Constructor) : TreeEnvironment → ExpressionTree → TreeResult → Prop where
    | literal {environment value} : TreeEvaluates constructors environment (.literal value) (.ok (.literal value))
    | variable {environment index value} (binding : environment[index]? = some value) :
        TreeEvaluates constructors environment (.variableRef index) (.ok value)
    | lambda {environment parameter body} :
        TreeEvaluates constructors environment (.lambda parameter body) (.ok (.closure (.lambda parameter body) environment))
    | recursive {environment definitions body result}
        (evaluated : TreeEvaluates constructors (recursiveTreeEnvironment definitions environment) body result) :
        TreeEvaluates constructors environment (.letRecursive definitions body) result
    | argumentFault {environment function argument fault}
        (evaluated : TreeEvaluates constructors environment argument (.error fault)) :
        TreeEvaluates constructors environment (.apply function argument) (.error fault)
    | functionFault {environment function argument actual fault}
        (argumentValue : TreeEvaluates constructors environment argument (.ok actual))
        (evaluated : TreeEvaluates constructors environment function (.error fault)) :
        TreeEvaluates constructors environment (.apply function argument) (.error fault)
    | application {environment function argument actual callable result}
        (argumentValue : TreeEvaluates constructors environment argument (.ok actual))
        (functionValue : TreeEvaluates constructors environment function (.ok callable))
        (applied : TreeApplies constructors callable actual result) :
        TreeEvaluates constructors environment (.apply function argument) result
    | letFault {environment pattern value body fault}
        (evaluated : TreeEvaluates constructors environment value (.error fault)) :
        TreeEvaluates constructors environment (.letValue pattern value body) (.error fault)
    | letMismatch {environment pattern value body actual}
        (evaluated : TreeEvaluates constructors environment value (.ok actual))
        (mismatch : matchTreePattern pattern actual = none) :
        TreeEvaluates constructors environment (.letValue pattern value body) (.error .matchFailure)
    | letBody {environment pattern value body actual bindings result}
        (evaluated : TreeEvaluates constructors environment value (.ok actual))
        (matched : matchTreePattern pattern actual = some bindings)
        (continued : TreeEvaluates constructors (extendTree environment bindings) body result) :
        TreeEvaluates constructors environment (.letValue pattern value body) result
    | conditionFault {environment condition yes no fault}
        (evaluated : TreeEvaluates constructors environment condition (.error fault)) :
        TreeEvaluates constructors environment (.branch condition yes no) (.error fault)
    | branch {environment condition yes no choice result}
        (evaluated : TreeEvaluates constructors environment condition (.ok (.literal (.boolean choice))))
        (continued : TreeEvaluates constructors environment (if choice then yes else no) result) :
        TreeEvaluates constructors environment (.branch condition yes no) result
    | andFault {environment left right fault}
        (evaluated : TreeEvaluates constructors environment left (.error fault)) :
        TreeEvaluates constructors environment (.andThen left right) (.error fault)
    | andFalse {environment left right}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean false)))) :
        TreeEvaluates constructors environment (.andThen left right) (.ok (.literal (.boolean false)))
    | andRightFault {environment left right fault}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean true))))
        (continued : TreeEvaluates constructors environment right (.error fault)) :
        TreeEvaluates constructors environment (.andThen left right) (.error fault)
    | andRightValue {environment left right value}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean true))))
        (continued : TreeEvaluates constructors environment right (.ok (.literal (.boolean value)))) :
        TreeEvaluates constructors environment (.andThen left right) (.ok (.literal (.boolean value)))
    | orFault {environment left right fault}
        (evaluated : TreeEvaluates constructors environment left (.error fault)) :
        TreeEvaluates constructors environment (.orElse left right) (.error fault)
    | orTrue {environment left right}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean true)))) :
        TreeEvaluates constructors environment (.orElse left right) (.ok (.literal (.boolean true)))
    | orRightFault {environment left right fault}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean false))))
        (continued : TreeEvaluates constructors environment right (.error fault)) :
        TreeEvaluates constructors environment (.orElse left right) (.error fault)
    | orRightValue {environment left right value}
        (evaluated : TreeEvaluates constructors environment left (.ok (.literal (.boolean false))))
        (continued : TreeEvaluates constructors environment right (.ok (.literal (.boolean value)))) :
        TreeEvaluates constructors environment (.orElse left right) (.ok (.literal (.boolean value)))
    | consTailFault {environment head tail fault}
        (evaluated : TreeEvaluates constructors environment tail (.error fault)) :
        TreeEvaluates constructors environment (.cons head tail) (.error fault)
    | consHeadFault {environment head tail tailValue fault}
        (last : TreeEvaluates constructors environment tail (.ok tailValue))
        (first : TreeEvaluates constructors environment head (.error fault)) :
        TreeEvaluates constructors environment (.cons head tail) (.error fault)
    | cons {environment head tail first last}
        (tailValue : TreeEvaluates constructors environment tail (.ok last))
        (headValue : TreeEvaluates constructors environment head (.ok first)) :
        TreeEvaluates constructors environment (.cons head tail) (.ok (.cons first last))
    | tupleFault {environment fields fault}
        (evaluated : TreeEvaluatesArguments constructors environment fields (.error fault)) :
        TreeEvaluates constructors environment (.tuple fields) (.error fault)
    | tuple {environment fields values}
        (evaluated : TreeEvaluatesArguments constructors environment fields (.ok values)) (arity : 2 ≤ values.length) :
        TreeEvaluates constructors environment (.tuple fields) (.ok (.tuple values))
    | variantFault {environment typeId constructor fields fault}
        (evaluated : TreeEvaluatesArguments constructors environment fields (.error fault)) :
        TreeEvaluates constructors environment (.variant typeId constructor fields) (.error fault)
    | variant {environment typeId constructor fields values}
        (evaluated : TreeEvaluatesArguments constructors environment fields (.ok values))
        (declaration : ⟨typeId, constructor, values.length⟩ ∈ constructors) :
        TreeEvaluates constructors environment (.variant typeId constructor fields) (.ok (.variant typeId constructor values))
    | primitiveFault {environment operator arguments fault}
        (evaluated : TreeEvaluatesArguments constructors environment arguments (.error fault)) :
        TreeEvaluates constructors environment (.primitive operator arguments) (.error fault)
    | primitive {environment operator arguments values result}
        (evaluated : TreeEvaluatesArguments constructors environment arguments (.ok values))
        (calculated : TreePrimitive operator values result) :
        TreeEvaluates constructors environment (.primitive operator arguments) result
    | matchFault {environment scrutinee clauses fault}
        (evaluated : TreeEvaluates constructors environment scrutinee (.error fault)) :
        TreeEvaluates constructors environment (.matchValue scrutinee clauses) (.error fault)
    | matchFailure {environment scrutinee clauses value}
        (evaluated : TreeEvaluates constructors environment scrutinee (.ok value))
        (mismatch : selectTreeClause clauses value = none) :
        TreeEvaluates constructors environment (.matchValue scrutinee clauses) (.error .matchFailure)
    | matchBody {environment scrutinee clauses value body bindings result}
        (evaluated : TreeEvaluates constructors environment scrutinee (.ok value))
        (selected : selectTreeClause clauses value = some (body, bindings))
        (continued : TreeEvaluates constructors (extendTree environment bindings) body result) :
        TreeEvaluates constructors environment (.matchValue scrutinee clauses) result

  inductive TreeApplies (constructors : List Constructor) : TreeValue → TreeValue → TreeResult → Prop where
    | lambda {parameter body captured argument bindings result}
        (matched : matchTreePattern parameter argument = some bindings)
        (evaluated : TreeEvaluates constructors (extendTree captured bindings) body result) :
        TreeApplies constructors (.closure (.lambda parameter body) captured) argument result
    | lambdaMismatch {parameter body captured argument} (mismatch : matchTreePattern parameter argument = none) :
        TreeApplies constructors (.closure (.lambda parameter body) captured) argument (.error .matchFailure)
    | recursive {slot definitions parameter body captured argument bindings result}
        (definition : definitions[slot]? = some (.lambda parameter body))
        (matched : matchTreePattern parameter argument = some bindings)
        (evaluated : TreeEvaluates constructors (extendTree (recursiveTreeEnvironment definitions captured) bindings) body result) :
        TreeApplies constructors (.closure (.recursive definitions slot) captured) argument result
    | recursiveMismatch {slot definitions parameter body captured argument}
        (definition : definitions[slot]? = some (.lambda parameter body)) (mismatch : matchTreePattern parameter argument = none) :
        TreeApplies constructors (.closure (.recursive definitions slot) captured) argument (.error .matchFailure)

  inductive TreeEvaluatesArguments (constructors : List Constructor) :
      TreeEnvironment → List ExpressionTree → Except Fault (List TreeValue) → Prop where
    | nil {environment} : TreeEvaluatesArguments constructors environment [] (.ok [])
    | tailFault {environment first rest fault}
        (last : TreeEvaluatesArguments constructors environment rest (.error fault)) :
        TreeEvaluatesArguments constructors environment (first :: rest) (.error fault)
    | headFault {environment first rest values fault}
        (last : TreeEvaluatesArguments constructors environment rest (.ok values))
        (head : TreeEvaluates constructors environment first (.error fault)) :
        TreeEvaluatesArguments constructors environment (first :: rest) (.error fault)
    | cons {environment first rest value values}
        (last : TreeEvaluatesArguments constructors environment rest (.ok values))
        (head : TreeEvaluates constructors environment first (.ok value)) :
        TreeEvaluatesArguments constructors environment (first :: rest) (.ok (value :: values))
end

end Mettapedia.Languages.OCaml
