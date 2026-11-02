import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerArithmetic

/-! The loaded arithmetic profile maps to the independent OCaml operators.
Its target result representation is exactly the source primitive-result IR.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticSource

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open OCamlIntegerArithmetic

def source : Operator → OCaml.Primitive
  | .add => .add | .subtract => .subtract | .multiply => .multiply

theorem source_evaluates (operator : Operator) (left right : Int) :
    (source operator).eval [.literal (.integer left), .literal (.integer right)] =
      .ok (.ok (.literal (.integer (OCaml.wrapInteger (compute operator left right))))) := by
  cases operator <;> rfl

theorem operator_exact (operator : Operator) : InferenceCettaWire.encodePattern (primitive (source operator)) =
    .application "PApp" [.string (name operator), .symbol "LNil"] := by
  cases operator <;> simp only [source, primitive, node, name, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

#print axioms source_evaluates
#print axioms operator_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticSource
