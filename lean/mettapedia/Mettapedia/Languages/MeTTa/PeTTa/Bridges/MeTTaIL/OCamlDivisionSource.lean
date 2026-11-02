import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionHelper
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn

/-! Division modes map to the independent source operators. Ordinary
faults and wrapped integer results keep the exact source result codec.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionSource

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open OCamlSignedDivision

def source (modulo : Bool) : OCaml.Primitive := if modulo then .modulo else .divide
def sourceResult (modulo : Bool) (left right : Int) : OCaml.Result :=
  if right = 0 then .error .divisionByZero else .ok (.literal (.integer (OCaml.wrapInteger (compute modulo left right))))

theorem source_evaluates (modulo : Bool) (left right : Int) :
    (source modulo).eval [.literal (.integer left), .literal (.integer right)] = .ok (sourceResult modulo left right) := by
  cases modulo <;> by_cases zero : right = 0 <;> simp [source, sourceResult, compute, OCaml.Primitive.eval, zero]

theorem operator_exact (modulo : Bool) : InferenceCettaWire.encodePattern (primitive (source modulo)) =
    .application "PApp" [.string (name modulo), .symbol "LNil"] := by
  cases modulo <;> simp [source, primitive, node, name, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem result_exact (modulo : Bool) (left right : Int) : result modulo left right = .application "Some"
    [InferenceCettaWire.encodePattern (primitiveResult (sourceResult modulo left right))] := by
  by_cases zero : right = 0
  · simp only [result, sourceResult, zero, if_true]
    exact OCamlResultServices.fault_result_exact .divisionByZero
  · simp only [result, sourceResult, zero, if_false]
    exact OCamlIntegerResult.result_exact _

#print axioms source_evaluates
#print axioms operator_exact
#print axioms result_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionSource
