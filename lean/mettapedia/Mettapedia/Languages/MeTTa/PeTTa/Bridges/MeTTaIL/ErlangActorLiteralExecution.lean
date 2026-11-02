import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-! The actual actor library supplies the undefined atom used by an empty
peek reply. The value agrees with the independent Erlang literal encoder;
it is neither an unresolved call nor a fixture-provided definition. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLiteralExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem undefined_returns (state : State) :
    PureReturns runtime [] state (apply "gslt:er-actor:undefined" []) state
      (encoded (InferenceCettaWire.encodePattern (ErlangCompilation.literal (.atom "undefined")))) := by
  metta_call actor_checked
  apply data_returns _ _ _ _ _ (by decide +kernel)
  decide_cbv

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLiteralExecution
