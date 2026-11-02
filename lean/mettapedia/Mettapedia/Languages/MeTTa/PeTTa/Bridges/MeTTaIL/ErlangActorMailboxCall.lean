import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorStoreCall

/-! Mixed-demand calls to the loaded mailbox callback dispatchers. Numeric
pid evaluation and raw continuation/result/world fields follow the actual
function declarations. Branch meanings are proved by their consumers. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxCall

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem mailbox_result_returns (state : State) (identity : Nat) (action mailbox machine continuation result system answer : Term)
    (body : PureReturns runtime (Library.bind ["pid", "action", "mailbox", "machine", "continuation", "result", "system"]
      [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded result, encoded system]) state (actorLibrary.body "gslt:er-actor:mailbox-result") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-result"
      [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded result, encoded system]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:mailbox-result").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:mailbox-result").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded result, encoded system] [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded result, encoded system] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:mailbox-result") (index := 0)
      (by decide +kernel) (number_returns runtime [] state identity)
      (ArgumentsReturn.raw (argument := encoded action) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded mailbox) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded machine) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded continuation) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded result) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded system) (by decide +kernel) (.nil _ _)))))))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

theorem mailbox_done_returns (state : State) (identity : Nat) (action mailbox machine continuation target account system answer : Term)
    (body : PureReturns runtime (Library.bind ["pid", "action", "mailbox", "machine", "continuation", "target", "account", "system"]
      [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded target, encoded account, encoded system]) state (actorLibrary.body "gslt:er-actor:mailbox-done") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-done"
      [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded target, encoded account, encoded system]) state (encoded answer) := by
  have present : (actorLibrary.equationOf "gslt:er-actor:mailbox-done").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady actorLibrary row = true := by
    have checked : ((actorLibrary.equationOf "gslt:er-actor:mailbox-done").map (Library.demandReady actorLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call actor_checked found ready [] state state state
    [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded target, encoded account, encoded system] [number identity, encoded action, encoded mailbox, encoded machine, encoded continuation, encoded target, encoded account, encoded system] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:er-actor:mailbox-done") (index := 0)
      (by decide +kernel) (number_returns runtime [] state identity)
      (ArgumentsReturn.raw (argument := encoded action) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded mailbox) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded machine) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded continuation) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded target) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded account) (by decide +kernel) (ArgumentsReturn.raw (argument := encoded system) (by decide +kernel) (.nil _ _))))))))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ErlangControllerSource.runtime] using collected
  · exact body

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxCall
