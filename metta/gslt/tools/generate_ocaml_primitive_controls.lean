import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.OCaml.Primitives

/-! Native service controls against the independent OCaml primitive model.
No program execution or primitive result is precomputed into runtime plans. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

open Mettapedia.Languages
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

def integer (number : Int) : OCaml.Value := .literal (.integer number)
def boolean (value : Bool) : OCaml.Value := .literal (.boolean value)
def encoded (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)

def fault : OCaml.Fault → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  | .divisionByZero => node "MlDivisionByZero"
  | .matchFailure => node "MlMatchFailure"
  | .functionalComparison => node "MlFunctionalComparison"

def primitiveCases : List (OCaml.Primitive × List OCaml.Value) :=
  [(.add, [integer 1, integer 2]), (.subtract, [integer 3, integer 9]),
   (.multiply, [integer 6, integer 7]), (.divide, [integer (-7), integer 3]),
   (.divide, [integer 7, integer (-3)]), (.divide, [integer (-7), integer (-3)]),
   (.modulo, [integer (-7), integer 3]), (.modulo, [integer 7, integer (-3)]),
   (.divide, [integer 1, integer 0]), (.modulo, [integer 1, integer 0]),
   (.negate, [integer (-7)]), (.notBool, [boolean true]), (.notBool, [boolean false]),
   (.add, [integer (OCaml.integerHalf - 1), integer 1]),
   (.subtract, [integer (-OCaml.integerHalf), integer 1]),
   (.multiply, [integer (OCaml.integerHalf - 1), integer (OCaml.integerHalf - 1)]),
   (.divide, [integer (-OCaml.integerHalf), integer (-1)]),
   (.modulo, [integer (-OCaml.integerHalf), integer (-1)]),
   (.negate, [integer (-OCaml.integerHalf)]),
   (.equal, [integer 7, integer 7]), (.different, [integer 7, integer 7]),
   (.less, [integer (-1), integer 1]), (.lessEqual, [integer 1, integer 1]),
   (.greater, [integer 9, integer 1]), (.greaterEqual, [integer 1, integer 1]),
   (.equal, [boolean false, boolean true]),
   (.less, [.literal .nil, .cons (integer 1) (.literal .nil)]),
   (.equal, [.cons (integer 1) (.literal .nil), .cons (integer 1) (.literal .nil)]),
   (.less, [.tuple [integer 1, integer 9], .tuple [integer 2, integer 0]]),
   (.equal, [.tuple [integer 1, boolean true], .tuple [integer 1, boolean true]]),
   (.less, [.variant 0 2 [], .variant 0 1 [integer 0]]),
   (.less, [.variant 0 0 [], .variant 0 2 []]),
   (.less, [.variant 0 1 [integer 9], .variant 0 3 [integer 0]]),
   (.equal, [.closure (.lambda 0) [], .closure (.lambda 0) []]),
   (.less, [.closure (.lambda 0) [], .closure (.lambda 0) []]),
   (.less, [.tuple [integer 0, .closure (.lambda 0) []], .tuple [integer 1, .closure (.lambda 0) []]]),
   (.equal, [.tuple [integer 0, .closure (.lambda 0) []], .tuple [integer 0, .closure (.lambda 0) []]]),
   (.less, [.literal (.string [0, 255]), .literal (.string [1])])]

def main (arguments : List String) : IO Unit := do
  let [output] := arguments | throw (IO.userError "expected an output file")
  let mut controls : List String := []
  for (number, index) in ([0,1,-1,15,16,-7,2^62-1,-(2^62),2^120+7,-(2^120)+7] : List Int).zipIdx do
    let expected := encoded (literal (.integer number))
    controls := controls ++ ["!(let* (($expected (quote " ++ expected ++ "))" ++
      " ($actual (gslt:ml:integer " ++ toString number ++ ")) ($decoded (gslt:ml:integer-value $expected)))" ++
      " (println! (OCamlIntegerControl " ++ toString index ++ " (== $actual $expected)" ++
      " (== $decoded (Some " ++ toString number ++ ")))))\n"]
  for ((operator, arguments), index) in primitiveCases.zipIdx do
    let .ok result := operator.eval arguments | throw (IO.userError "invalid primitive reference case")
    let expected := match result with
      | .ok result => node "MlPrimitiveValue" [value result]
      | .error error => node "MlPrimitiveFault" [fault error]
    controls := controls ++ ["!(let* (($operator (quote " ++ encoded (primitive operator) ++
      ")) ($arguments (quote " ++ encoded (valueList arguments) ++ "))" ++
      " ($actual (gslt:ml:primitive $operator $arguments)) ($expected (quote " ++ encoded expected ++ ")))" ++
      " (println! (OCamlPrimitiveControl " ++ toString index ++ " (== $actual (Some $expected)))))\n"]
  IO.FS.writeFile output (String.join controls)
  IO.println s!"{primitiveCases.length} primitive cases and 10 integer round trips"
