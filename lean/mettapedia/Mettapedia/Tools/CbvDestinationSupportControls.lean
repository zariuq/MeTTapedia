import Mettapedia.Tools.CbvDestinationSupport

/-! # The support shortcut works without executing the codec -/

set_option autoImplicit false

namespace Mettapedia.Tools.CbvDestinationSupport.Controls

open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

attribute [local cbv_simproc ↓] encodedSupport
attribute [local cbv_opaque] encode

theorem nested_variables_survive_without_codec_evaluation :
    (encode (.expression [.var "x", .expression [.var "y", .var "x"]])).freeVars =
      (["x", "y"] : List String).toFinset := by
  cbv
  all_goals
    ext name
    simp [or_comm]

theorem quotation_is_raw_syntactic_support_here :
    (encode (.expression [.symbol "quote", .var "x"])).freeVars = {"x"} := by cbv

theorem symbols_do_not_supply_variable_support :
    (encode (.expression [.symbol "x", .grounded (.string "x")])).freeVars = ∅ := by cbv

end Mettapedia.Tools.CbvDestinationSupport.Controls
