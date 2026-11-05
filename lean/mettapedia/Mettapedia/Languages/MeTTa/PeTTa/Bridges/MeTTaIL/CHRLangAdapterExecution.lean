import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource

/-! Local execution laws of the CHR package port, over its actual loaded
source. Whole-controller adequacy is a separate obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

/-- Seed identifiers are recorded newest first; the outcome reverses them
onto the posting order. -/
theorem reverse_returns (state : State) (items done : List Term) :
    PureReturns runtime [] state
      (apply "gslt:chr-lang:reverse" [encoded (encodeList id items), encoded (encodeList id done)]) state
      (encoded (encodeList id (items.reverse ++ done))) := by
  induction items generalizing done with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [encodeList]
  | cons first rest ih =>
      have tail := ih (first :: done)
      have order : (first :: rest).reverse ++ done = rest.reverse ++ first :: done := by simp
      rw [order]
      metta_call checked
      metta_eval [tail] with checked unfolding [encodeList]

#print axioms reverse_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource
