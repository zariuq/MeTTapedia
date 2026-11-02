import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeDemandEval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeMixedCapture

/-! Actual actor network calls collect their declared numeric arguments
and retain their raw message lists. Body proofs are composed at those values.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkCall

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem has_pair_returns (state : State) (sender receiver : Nat) (messages : Term) (answer : Bool)
    (body : PureReturns runtime (Library.bind ["sender", "receiver", "messages"]
      [number sender, number receiver, encoded messages]) state (actorLibrary.body "gslt:er-actor:has-pair") state (Effects.boolean answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:has-pair" [number sender, number receiver, encoded messages]) state (Effects.boolean answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:has-pair").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:has-pair").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number sender, number receiver, encoded messages] [number sender, number receiver, encoded messages] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:has-pair") (index := 0)
      (by decide +kernel) (number_returns runtime [] state sender)
      (.evaluated (by decide +kernel) (number_returns runtime [] state receiver)
        (ArgumentsReturn.raw (argument := encoded messages) (by decide +kernel) (.nil _ _)))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

theorem take_delivery_returns (state : State) (index : Nat) (before messages answer : Term)
    (body : PureReturns runtime (Library.bind ["index", "before", "messages"]
      [number index, encoded before, encoded messages]) state (actorLibrary.body "gslt:er-actor:take-delivery") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:take-delivery" [number index, encoded before, encoded messages]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:take-delivery").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:take-delivery").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number index, encoded before, encoded messages] [number index, encoded before, encoded messages] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:take-delivery") (index := 0)
      (by decide +kernel) (number_returns runtime [] state index)
      (ArgumentsReturn.raw (argument := encoded before) (by decide +kernel)
        (ArgumentsReturn.raw (argument := encoded messages) (by decide +kernel) (.nil _ _)))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

#print axioms has_pair_returns
#print axioms take_delivery_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkCall
