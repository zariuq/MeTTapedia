import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorDeliveryCorrespondence

/-! Repeated values retain channel occurrences. A later same-channel
selection is refused; another sender can be delivered independently.
An unavailable selected index does not establish network quiescence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkControls

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorNetworkWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit ErlangControllerSource

def first : Envelope Term := ⟨⟨1,2⟩, .symbol "a"⟩
def other : Envelope Term := ⟨⟨3,2⟩, .symbol "b"⟩

theorem duplicate_later_refused (state : State) :
    PureReturns runtime [] state (apply "gslt:er-actor:take-delivery"
      [number 1, encoded (.symbol "LNil"), encoded (encodeList (envelope id) [first, first])]) state (encoded (.symbol "None")) := by
  have selected : Network.deliverAt? 1 [first, first] = none := by rfl
  simpa only [List.length_nil, Nat.zero_add, List.nil_append, selected, encodeOption_none, encodeList] using
    ErlangActorTakeDelivery.returns id state [] [first, first] 1

theorem other_sender_can_pass (state : State) :
    PureReturns runtime [] state (apply "gslt:er-actor:take-delivery"
      [number 1, encoded (.symbol "LNil"), encoded (encodeList (envelope id) [first, other])]) state
      (encoded (.application "Some" [delivery id (other, [first])])) := by
  have selected : Network.deliverAt? 1 [first, other] = some (other, [first]) := by rfl
  simpa only [List.length_nil, Nat.zero_add, List.nil_append, selected, encodeOption_some, encodeList] using
    ErlangActorTakeDelivery.returns id state [] [first, other] 1

theorem unavailable_index_is_not_quiescence (state : State) :
    PureReturns runtime [] state (apply "gslt:er-actor:take-delivery"
      [number 9, encoded (.symbol "LNil"), encoded (encodeList (envelope id) [first])]) state (encoded (.symbol "None")) ∧
      Network.Delivers [first] first [] := by
  have selected : Network.deliverAt? 9 [first] = none := by rfl
  refine ⟨?_, ?_⟩
  · simpa only [List.length_nil, Nat.zero_add, List.nil_append, selected, encodeOption_none, encodeList] using
      ErlangActorTakeDelivery.returns id state [] [first] 9
  · exact .take [] [] first (by simp)

theorem blocked_index_cannot_publish_packet (state after : State) (observed : Term) :
    ¬ Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:take-delivery"
      [number 1, encoded (.symbol "LNil"), encoded (encodeList (envelope id) [first, first])])}
      (.complete after [encoded (.application "Some" [observed])] [] []) := by
  intro read
  have values := (pure_returns_derivation_iff runtime [] state state _ _ (duplicate_later_refused state) after _ [] []).mp read |>.2.1
  have impossible := CettaWireAtom.encode_injective _ _ (List.cons.inj values).1
  cases impossible

#print axioms duplicate_later_refused
#print axioms other_sender_can_pass
#print axioms unavailable_index_is_not_quiescence
#print axioms blocked_index_cannot_publish_packet

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkControls
