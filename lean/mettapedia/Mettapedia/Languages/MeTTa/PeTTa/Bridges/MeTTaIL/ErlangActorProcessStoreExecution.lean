import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorStoreCall
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorProcessWire

/-! The loaded pid-keyed process store agrees with the independent source
list operations. Payload encoders remain parameters, so no machine result
or mailbox interpretation is assumed by this storage correspondence. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorProcessWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem get_returns (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state : State) (identity : Nat) (processes : List LocalProcess) :
    PureReturns runtime [] state (apply "gslt:er-actor:get"
      [number identity, encoded (encodeList (process box machine) processes)]) state
      (encoded (encodeOption (process box machine) (ActorProcessStore.get identity processes))) := by
  induction processes with
  | nil =>
    apply ErlangActorStoreCall.get_returns
    metta_literal
    metta_eval with actor_checked unfolding [encodeList, ActorProcessStore.get, encodeOption]
  | cons head rest ih =>
    by_cases same : identity = head.identity
    · subst identity
      have returned : PureReturns runtime [] state (apply "gslt:er-actor:get"
          [number head.identity, encoded (encodeList (process box machine) (head :: rest))]) state
          (encoded (.application "Some" [process box machine head])) := by
        apply ErlangActorStoreCall.get_returns
        metta_literal
        metta_eval with actor_checked unfolding [process, encodeList]
      simpa [ActorProcessStore.get] using returned
    · have returned : PureReturns runtime [] state (apply "gslt:er-actor:get"
          [number identity, encoded (encodeList (process box machine) (head :: rest))]) state
          (encoded (encodeOption (process box machine) (ActorProcessStore.get identity rest))) := by
        apply ErlangActorStoreCall.get_returns
        metta_literal
        metta_eval [ih] with actor_checked unfolding [process, encodeList, same]
      simpa [ActorProcessStore.get, same] using returned

theorem put_returns (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state : State) (identity : Nat) (replacement : LocalProcess) (processes : List LocalProcess) :
    PureReturns runtime [] state (apply "gslt:er-actor:put"
      [number identity, encoded (process box machine replacement), encoded (encodeList (process box machine) processes)]) state
      (encoded (encodeList (process box machine) (ActorProcessStore.put identity replacement processes))) := by
  induction processes with
  | nil =>
    apply ErlangActorStoreCall.put_returns
    metta_literal
    metta_eval with actor_checked unfolding [ActorProcessStore.put, encodeList]
  | cons head rest ih =>
    by_cases same : identity = head.identity
    · rw [ActorProcessStore.put, if_pos same]
      apply ErlangActorStoreCall.put_returns
      metta_literal
      metta_eval with actor_checked unfolding [process, encodeList, same]
    · rw [ActorProcessStore.put, if_neg same]
      apply ErlangActorStoreCall.put_returns
      metta_literal
      metta_eval [ih] with actor_checked unfolding [process, encodeList, same]

#print axioms get_returns
#print axioms put_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreExecution
