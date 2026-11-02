import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticAdequacy

/-! Every completed encoded arithmetic answer authorizes exactly the
source row inserted into the shared primitive cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticRowAuthorization

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlIntegerArithmetic

theorem completed_row_sound (state : State) (operator : Operator) (left right : Int) (result : OCaml.Result)
    (table : GeneralPremise.ProviderSnapshot) (sound : PrimitiveRowsSound table)
    (completed : Runs runtime {state := state, control := .evaluate [] (OCamlArithmeticAdequacy.call operator left right)}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm result)] [] [])) :
    PrimitiveRowsSound (GeneralPremise.ProviderAppend.appendRows table
      [primitiveRow (OCamlArithmeticSource.source operator) [.literal (.integer left), .literal (.integer right)] result]) :=
  append_primitive_sound table _ _ result sound
    ((OCamlArithmeticAdequacy.exact_source_result state operator left right result).mp completed)

#print axioms completed_row_sound

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticRowAuthorization
