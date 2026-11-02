import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariants

/-! The public value comparator delegates variants to the same checked
tag/field helper without re-encoding or re-indexing their source identity.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariantValues

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution OCamlTagExecution

theorem returns (state : State) (leftType leftTag rightType rightTag : Nat)
    (left right : List OCaml.Value)
    (fieldsReturned : PureReturns runtime [] state
      (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareFields left right)))) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (valueTerm (.variant leftType leftTag left)), encoded (valueTerm (.variant rightType rightTag right))]) state
      (encoded (view (OCaml.compareValue (.variant leftType leftTag left) (.variant rightType rightTag right)))) := by
  have helper := OCamlCompareVariants.helper_returns state leftType leftTag rightType rightTag left right fieldsReturned
  rw [tag_exact, tag_exact] at helper
  metta_call checked
  ml_compare_eval [helper] unfolding [value_variant, encodeList]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariantValues
