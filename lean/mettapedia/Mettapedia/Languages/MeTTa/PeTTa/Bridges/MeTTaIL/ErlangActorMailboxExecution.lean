import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxCall
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorWorldStoreExecution
import Mettapedia.Languages.Erlang.ActorMailboxReplies

/-! The loaded pending callback preserves every carried field. A waiting
reply commits only its administrative account while retaining the source
world. This covers these callback branches, not value-returning callbacks,
generated kernel linkage or complete actor scheduling. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorWorldWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec BridgeKit WireKit ErlangControllerSource

def boxed (label : String) (arguments : List Term) : Term :=
  .application "PApp" [.string label, encodeList id arguments]

def waitingEffect (identity : Nat) (account : Term) : Term :=
  .application "ErActorMailbox" [.natural identity, .symbol "ErWaiting", account]

theorem pending_returns (state : State) (identity : Nat)
    (action box machine continuation account system : Term) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-result"
      [number identity, encoded action, encoded box, encoded machine, encoded continuation,
        encoded (.application "ErRhoKernelPending" [account]), encoded system]) state
      (encoded (.application "ErActorMailboxPending" [.natural identity, action, box, machine, continuation,
        .application "ErRhoKernelPending" [account], system])) := by
  apply ErlangActorMailboxCall.mailbox_result_returns
  metta_literal
  metta_eval with actor_checked

theorem waiting_returns (state : State) (identity : Nat)
    (box machine continuation account system answer : Term)
    (stored : PureReturns runtime [] state (apply "gslt:er-actor:store"
      [number identity, encoded box, encoded machine, encoded (waitingEffect identity account), encoded system])
      state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-done"
      [number identity, encoded (.symbol "ErWait"), encoded box, encoded machine, encoded continuation,
        encoded (boxed "ErWaiting" [box]), encoded account, encoded system]) state (encoded answer) := by
  apply ErlangActorMailboxCall.mailbox_done_returns
  metta_literal
  metta_eval [stored] with actor_checked unfolding [boxed, encodeList, waitingEffect]

theorem waiting_result_returns (state : State) (identity : Nat)
    (box machine continuation account system answer : Term)
    (stored : PureReturns runtime [] state (apply "gslt:er-actor:store"
      [number identity, encoded box, encoded machine, encoded (waitingEffect identity account), encoded system])
      state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-result"
      [number identity, encoded (.symbol "ErWait"), encoded box, encoded machine, encoded continuation,
        encoded (.application "ErRhoKernelDone" [boxed "ErWaiting" [box], account]), encoded system]) state (encoded answer) := by
  have done := waiting_returns state identity box machine continuation account system answer stored
  apply ErlangActorMailboxCall.mailbox_result_returns
  metta_literal
  metta_eval [done] with actor_checked

theorem waiting_world_returns (box : Mailbox Value → Term) (machine : MachineState → Term) (payload : Value → Term)
    (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (continuation account history : Term) :
    PureReturns runtime [] state (apply "gslt:er-actor:mailbox-result"
      [number index, encoded (.symbol "ErWait"), encoded (box selected.mailbox), encoded (machine selected.machine),
        encoded continuation,
        encoded (.application "ErRhoKernelDone" [boxed "ErWaiting" [box selected.mailbox], account]),
        encoded (world box machine payload system history)]) state
      (encoded (world box machine payload system (record (waitingEffect index account) history))) := by
  have stored := ErlangActorWorldStoreExecution.returns box machine payload state valid found selected
    (valid.at found) (waitingEffect index account) history
  rw [ActorSystem.replace_index_selected found] at stored
  exact waiting_result_returns state index (box selected.mailbox) (machine selected.machine)
    continuation account (world box machine payload system history)
    (world box machine payload system (record (waitingEffect index account) history)) stored

theorem waiting_source_correspondence (box : Mailbox Value → Term) (machine : MachineState → Term)
    (payload : Value → Term) (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (continuation : Continuation) (requested : selected.machine = .request .waitInfinity continuation)
    (empty : selected.mailbox.unread = []) (continuationWire account history : Term) :
    system.execute? index = .ok none ∧
      PureReturns runtime [] state (apply "gslt:er-actor:mailbox-result"
        [number index, encoded (.symbol "ErWait"), encoded (box selected.mailbox), encoded (machine selected.machine),
          encoded continuationWire,
          encoded (.application "ErRhoKernelDone" [boxed "ErWaiting" [box selected.mailbox], account]),
          encoded (world box machine payload system history)]) state
        (encoded (world box machine payload system (record (waitingEffect index account) history))) :=
  ⟨ActorSystem.wait_execute_empty found continuation requested empty,
    waiting_world_returns box machine payload state valid found continuationWire account history⟩

theorem completed_waiting_readback (box : Mailbox Value → Term) (machine : MachineState → Term) (payload : Value → Term)
    (state after : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (continuation account history observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:mailbox-result"
      [number index, encoded (.symbol "ErWait"), encoded (box selected.mailbox), encoded (machine selected.machine),
        encoded continuation,
        encoded (.application "ErRhoKernelDone" [boxed "ErWaiting" [box selected.mailbox], account]),
        encoded (world box machine payload system history)])} (.complete after [encoded observed] [] [])) :
    observed = world box machine payload system (record (waitingEffect index account) history) := by
  have actual := waiting_world_returns box machine payload state valid found continuation account history
  have values := (pure_returns_derivation_iff runtime [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxExecution
