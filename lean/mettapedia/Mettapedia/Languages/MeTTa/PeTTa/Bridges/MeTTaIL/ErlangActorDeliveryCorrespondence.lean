import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorTakeDelivery

/-! Actual completed delivery packets preserve and reflect the independent
FIFO delivery judgment. Observed packets retain every unselected occurrence.
This is selector correspondence; mailbox commit and actor scheduling are
separate operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorDeliveryCorrespondence

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorNetworkWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit ErlangControllerSource

theorem source_delivery_realized {α : Type} (encode : α → Term) (state : State)
    {network rest : List (Envelope α)} {message : Envelope α} (delivered : Network.Delivers network message rest) :
    ∃ index, PureReturns runtime [] state (apply "gslt:er-actor:take-delivery"
      [number index, encoded (.symbol "LNil"), encoded (encodeList (envelope encode) network)]) state
      (encoded (.application "Some" [delivery encode (message, rest)])) := by
  obtain ⟨index, selected⟩ := Network.deliverAt_complete delivered
  refine ⟨index, ?_⟩
  simpa only [List.length_nil, Nat.zero_add, List.nil_append, selected, encodeOption_some, encodeList] using
    ErlangActorTakeDelivery.returns encode state [] network index

theorem completed_delivery_authorized {α : Type} (encode : α → Term) (state after : State)
    (network : List (Envelope α)) (index : Nat) (observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:take-delivery"
      [number index, encoded (.symbol "LNil"), encoded (encodeList (envelope encode) network)])}
      (.complete after [encoded (.application "Some" [observed])] [] [])) :
    ∃ message rest, Network.deliverAt? index network = some (message, rest) ∧
      Network.Delivers network message rest ∧ delivery encode (message, rest) = observed := by
  have actual := ErlangActorTakeDelivery.returns encode state [] network index
  simp only [List.length_nil, Nat.zero_add, List.nil_append, encodeList] at actual
  have values := (pure_returns_derivation_iff runtime [] state state _ _ actual after _ [] []).mp read |>.2.1
  have same := CettaWireAtom.encode_injective _ _ (List.cons.inj values).1
  cases selected : Network.deliverAt? index network with
  | none =>
    simp only [selected, encodeOption_none] at same
    cases same
  | some result =>
    rcases result with ⟨message, rest⟩
    simp only [selected, encodeOption_some] at same
    have packet : delivery encode (message, rest) = observed := by
      first
      | exact (List.cons.inj (Term.application.inj same).2).1
      | exact ((List.cons.inj (Term.application.inj same).2).1).symm
    exact ⟨message, rest, rfl, Network.deliverAt_sound selected, packet⟩

theorem completed_delivery_fifo {α : Type} (encode : α → Term) (state after : State)
    (network : List (Envelope α)) (index : Nat) (observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:take-delivery"
      [number index, encoded (.symbol "LNil"), encoded (encodeList (envelope encode) network)])}
      (.complete after [encoded (.application "Some" [observed])] [] [])) :
    ∃ message rest, delivery encode (message, rest) = observed ∧
      Network.channel message.key network = message.payload :: Network.channel message.key rest ∧
      rest.length + 1 = network.length ∧
      ∀ key, message.key ≠ key → Network.channel key network = Network.channel key rest := by
  obtain ⟨message, rest, _, delivered, packet⟩ := completed_delivery_authorized encode state after network index observed read
  exact ⟨message, rest, packet, Network.delivered_channel_head delivered, Network.delivery_conserves_occurrences delivered,
    fun key apart => Network.delivered_other_channel delivered key apart⟩

#print axioms source_delivery_realized
#print axioms completed_delivery_authorized
#print axioms completed_delivery_fifo

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorDeliveryCorrespondence
