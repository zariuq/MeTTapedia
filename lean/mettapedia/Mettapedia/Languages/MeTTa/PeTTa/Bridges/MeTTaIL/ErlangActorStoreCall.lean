import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkCall

/-! Checked mixed-demand calls to the loaded actor process store. Pid keys
are evaluated numerically; process and replacement records remain raw data.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorStoreCall

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem get_returns (state : State) (identity : Nat) (processes answer : Term)
    (body : PureReturns runtime (Library.bind ["pid", "processes"]
      [number identity, encoded processes]) state (actorLibrary.body "gslt:er-actor:get") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:get" [number identity, encoded processes]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:get").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:get").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number identity, encoded processes] [number identity, encoded processes] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:get") (index := 0)
      (by decide +kernel) (number_returns runtime [] state identity)
      (ArgumentsReturn.raw (argument := encoded processes) (by decide +kernel) (.nil _ _))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

theorem put_returns (state : State) (identity : Nat) (replacement processes answer : Term)
    (body : PureReturns runtime (Library.bind ["pid", "replacement", "processes"]
      [number identity, encoded replacement, encoded processes]) state (actorLibrary.body "gslt:er-actor:put") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:put"
      [number identity, encoded replacement, encoded processes]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:put").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:put").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number identity, encoded replacement, encoded processes] [number identity, encoded replacement, encoded processes] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:put") (index := 0)
      (by decide +kernel) (number_returns runtime [] state identity)
      (ArgumentsReturn.raw (argument := encoded replacement) (by decide +kernel)
        (ArgumentsReturn.raw (argument := encoded processes) (by decide +kernel) (.nil _ _)))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

theorem store_returns (state : State) (identity : Nat) (box machine effect system answer : Term)
    (body : PureReturns runtime (Library.bind ["pid", "mailbox", "machine", "effect", "system"]
      [number identity, encoded box, encoded machine, encoded effect, encoded system]) state
      (actorLibrary.body "gslt:er-actor:store") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:store"
      [number identity, encoded box, encoded machine, encoded effect, encoded system]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:store").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:store").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number identity, encoded box, encoded machine, encoded effect, encoded system]
    [number identity, encoded box, encoded machine, encoded effect, encoded system] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:store") (index := 0)
      (by decide +kernel) (number_returns runtime [] state identity)
      (ArgumentsReturn.raw (argument := encoded box) (by decide +kernel)
        (ArgumentsReturn.raw (argument := encoded machine) (by decide +kernel)
          (ArgumentsReturn.raw (argument := encoded effect) (by decide +kernel)
            (ArgumentsReturn.raw (argument := encoded system) (by decide +kernel) (.nil _ _)))))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorStoreCall
