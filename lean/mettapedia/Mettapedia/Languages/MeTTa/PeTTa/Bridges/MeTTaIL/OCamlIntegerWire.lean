import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16Wire
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation

/-! The integer service's sign and magnitude use exactly the existing
compact OCaml IR representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerWire

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat

def sign (number : Int) : Term := .application "PApp"
  [.string (if number < 0 then "MlNegative" else "MlNonnegative"), .symbol "LNil"]

def datum (number : Int) : Term := .application "PApp"
  [.string "MlInteger", encodeList id [sign number, Word16Wire.vectorTerm number.natAbs]]

theorem datum_exact (number : Int) : datum number = InferenceCettaWire.encodePattern
    (OCamlCompilation.literal (.integer number)) := by
  rw [datum, Word16Wire.vector_exact]
  simp only [OCamlCompilation.literal, OCamlCompilation.node, OCamlCompilation.digits,
    Radix16Word.encode, sign, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList,
    encodeList]
  rfl

#print axioms datum_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerWire
