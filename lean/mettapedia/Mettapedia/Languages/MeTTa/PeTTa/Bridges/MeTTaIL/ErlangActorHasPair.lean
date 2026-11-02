import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkCall
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorNetworkWire

/-! The loaded actor selector's channel-presence test agrees with the
independent network keys for arbitrary encoded payloads and list lengths.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorHasPair

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorNetworkWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem returns {α : Type} (encode : α → Term) (state : State) (sender receiver : Nat) (messages : List (Envelope α)) :
    PureReturns runtime [] state (apply "gslt:er-actor:has-pair"
      [number sender, number receiver, encoded (encodeList (envelope encode) messages)]) state
      (Effects.boolean (messages.any (fun message => decide (message.key = ⟨sender, receiver⟩)))) := by
  induction messages with
  | nil =>
    apply ErlangActorNetworkCall.has_pair_returns
    metta_literal
    metta_eval with actor_checked unfolding [encodeList]
  | cons message messages ih =>
    rcases message with ⟨⟨sentBy, sentTo⟩, payload⟩
    by_cases sameSender : sender = sentBy
    · subst sender
      by_cases sameReceiver : receiver = sentTo
      · subst receiver
        have returned : PureReturns runtime [] state (apply "gslt:er-actor:has-pair"
            [number sentBy, number sentTo, encoded (encodeList (envelope encode) (⟨⟨sentBy, sentTo⟩, payload⟩ :: messages))]) state (Effects.boolean true) := by
          apply ErlangActorNetworkCall.has_pair_returns
          metta_literal
          metta_eval with actor_checked unfolding [envelope, encodeList]
        simpa only [List.any_cons, decide_true, Bool.true_or] using returned
      · have returned : PureReturns runtime [] state (apply "gslt:er-actor:has-pair"
            [number sentBy, number receiver, encoded (encodeList (envelope encode) (⟨⟨sentBy, sentTo⟩, payload⟩ :: messages))]) state
            (Effects.boolean (messages.any (fun message => decide (message.key = ⟨sentBy, receiver⟩)))) := by
          apply ErlangActorNetworkCall.has_pair_returns
          metta_literal
          metta_eval [ih] with actor_checked unfolding [envelope, encodeList, sameReceiver]
        simpa [List.any_cons, ChannelKey.mk.injEq, sameReceiver, eq_comm] using returned
    · have returned : PureReturns runtime [] state (apply "gslt:er-actor:has-pair"
          [number sender, number receiver, encoded (encodeList (envelope encode) (⟨⟨sentBy, sentTo⟩, payload⟩ :: messages))]) state
          (Effects.boolean (messages.any (fun message => decide (message.key = ⟨sender, receiver⟩)))) := by
        apply ErlangActorNetworkCall.has_pair_returns
        metta_literal
        metta_eval [ih] with actor_checked unfolding [envelope, encodeList, sameSender]
      simpa [List.any_cons, ChannelKey.mk.injEq, sameSender, eq_comm] using returned

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorHasPair
