import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.Erlang.Primitives

/-! Finite primitive controls, independent of whole-machine emission. The
expected outcomes come from the source IR model and use the actual IR codec. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages

def encode (pattern : Syntax.Pattern) : String :=
  CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)

def primitiveCases : List (String × Erlang.Primitive × List Erlang.Value) :=
  let n := fun value => Erlang.Value.literal (.integer value)
  let a := fun name => Erlang.Value.literal (.atom name)
  [("add-big", .add, [n (2 ^ 100), n 5]), ("subtract-big", .subtract, [n (-(2 ^ 100)), n 5]),
   ("multiply-big", .multiply, [n (2 ^ 100), n 3]), ("divide-signed", .divide, [n (-7), n 3]),
   ("remainder-signed", .remainder, [n (-7), n 3]), ("zero-fault", .divide, [n 1, n 0]),
   ("negate", .negate, [n (-5)]), ("integer-test", .isInteger, [n 5]),
   ("integer-test-negative", .isInteger, [a "true"]), ("atom-test", .isAtom, [a "true"]),
   ("not", .notBool, [a "true"]), ("not-fault", .notBool, [n 3]),
   ("and", .andBool, [a "true", a "false"]), ("or", .orBool, [a "false", a "true"]),
   ("xor", .xorBool, [a "true", a "true"]), ("numeric-guard", .greater, [n 5, n 0]),
   ("cross-type-order", .less, [n 1, a "a"]), ("atom-order", .less, [a "a", a "b"]),
   ("tuple-order", .less, [.tuple [], .tuple [n (-100)]]),
   ("list-order", .less, [.literal .nil, .cons (n 0) (.literal .nil)]),
   ("pid-equality", .equal, [.pid 1, .pid 2]),
   ("nested-pid-equality", .equal, [.tuple [.pid 1], .tuple [.pid 2]]),
   ("proper-list", .isList, [.cons (n 1) (.literal .nil)]),
   ("improper-list", .isList, [.cons (n 1) (n 2)]),
   ("function-arity", .isFunctionArity, [.closure 2 (.lambda 0) [], n 2]),
   ("function-arity-negative", .isFunctionArity, [.closure 2 (.lambda 0) [], n 1]),
   ("arity-argument-fault", .isFunctionArity, [.closure 2 (.lambda 0) [], n (-1)])]

def primitiveControls : String := primitiveCases.foldl (fun text (label, operator, arguments) =>
  let expected := match operator.eval arguments with
    | .error _ => "None"
    | .ok (.ok result) => "(Some " ++ encode (ErlangCompilation.node "ErPrimitiveValue" [ErlangCompilation.value result]) ++ ")"
    | .ok (.error fault) => "(Some " ++ encode (ErlangCompilation.node "ErPrimitiveFault" [ErlangCompilation.fault fault]) ++ ")"
  text ++ "!(let* (($operator (quote " ++ encode (ErlangCompilation.primitive operator) ++ "))" ++
    " ($arguments (quote " ++ encode (ErlangCompilation.valueList arguments) ++ "))" ++
    " ($actual (gslt:er:primitive $operator $arguments)) ($expected (quote " ++ expected ++ ")))" ++
    " (println! (ErPrimitiveControl " ++ reprStr label ++ " (== $actual $expected))))\n") ""

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls
