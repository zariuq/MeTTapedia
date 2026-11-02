import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorHasPair
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorListOperations

/-! The loaded delivery selector agrees with the independent network
selector. Its retained prefix is represented as a prefix of the original
network, so a later same-channel occurrence cannot bypass an earlier one.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorTakeDelivery

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorNetworkWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem returns {α : Type} (encode : α → Term) (state : State)
    (before messages : List (Envelope α)) (index : Nat) :
    PureReturns runtime [] state (apply "gslt:er-actor:take-delivery"
      [number index, encoded (encodeList (envelope encode) before), encoded (encodeList (envelope encode) messages)]) state
      (encoded (encodeOption (delivery encode) (Network.deliverAt? (before.length + index) (before ++ messages)))) := by
  induction messages generalizing before index with
  | nil =>
    simp only [List.append_nil, Network.deliverAt_prefix_nil, encodeOption_none]
    apply ErlangActorNetworkCall.take_delivery_returns
    metta_literal
    metta_eval with actor_checked unfolding [encodeList]
  | cons message messages ih =>
    rcases message with ⟨⟨sentBy, sentTo⟩, payload⟩
    cases index with
    | zero =>
      simp only [Nat.add_zero, Network.deliverAt_prefix_zero]
      have tested := ErlangActorHasPair.returns encode state sentBy sentTo before
      cases earlier : before.any (fun message => decide (message.key = ⟨sentBy, sentTo⟩)) with
      | false =>
        simp only [Bool.false_eq_true, if_false, encodeOption_some]
        rw [earlier] at tested
        have appended := ErlangActorListOperations.append_returns (envelope encode) state before messages
        apply ErlangActorNetworkCall.take_delivery_returns
        metta_literal
        metta_eval [tested, appended] with actor_checked unfolding [envelope, encodeList, delivery]
      | true =>
        simp only [if_true, encodeOption_none]
        rw [earlier] at tested
        apply ErlangActorNetworkCall.take_delivery_returns
        metta_literal
        metta_eval [tested] with actor_checked unfolding [envelope, encodeList]
    | succ index =>
      rw [Network.deliverAt_prefix_succ]
      have following := ih (before ++ [⟨⟨sentBy, sentTo⟩, payload⟩]) index
      have appended := ErlangActorListOperations.append_returns (envelope encode) state before [⟨⟨sentBy, sentTo⟩, payload⟩]
      apply ErlangActorNetworkCall.take_delivery_returns
      metta_literal
      metta_eval [appended, following] with actor_checked unfolding [envelope, encodeList]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorTakeDelivery
