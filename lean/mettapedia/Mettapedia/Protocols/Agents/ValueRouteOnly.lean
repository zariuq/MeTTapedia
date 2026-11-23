import Mettapedia.Protocols.Agents.RequestEncodingRoutes

/-!
# The value route only: no second route, a named refusal

The runtime encodes every provider request on the codec's value route. It
used to fall back to the text route on an engine without the value entries.
That fallback is retired: such an engine is refused by name
(`value-codec-unavailable`) and nothing is sent.

Invariants proved here, for every codec:

* every wire the runtime sends is the value route's answer;
* on an engine that has the value entries the runtime sends what the
  retired design sent, so retiring the fallback changes nothing there;
* two engines with the same codec never send different bytes for one
  request: one may refuse it as unavailable, but no request is sent two ways;
* the route contracts' oracle is sound: on a canonical request the value
  route answers what the codec's text entries answer
  (`RequestEncodingRoutes.routes_agree_canonical`).

The counterexample is the retired fallback: with a codec whose caller-side
parse respells a number, the same request goes out as different bytes on an
engine with the value entries and on one without them.

This is an abstract contract, not a refinement proof of
`src/provider_request_cetta.metta` or of the engine's `lib/llm.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ValueRouteOnly

open RequestEncodingRoutes

variable {V T E : Type}

/-- An engine: its codec, and whether it offers the value entries. -/
structure Engine (V T E : Type) where
  codec : Codec V T E
  hasValue : Bool

/-- What the runtime does with a request. -/
inductive Answer (T E : Type) where
  | sent (wire : T)
  | refused (e : E)
  | unavailable

def ofExcept : Except E T → Answer T E
  | .ok wire => .sent wire
  | .error e => .refused e

/-- The runtime now: the value route, or a named refusal. -/
def encode (eng : Engine V T E) (req : V) : Answer T E :=
  if eng.hasValue then ofExcept (eng.codec.valueRoute req) else .unavailable

/-- The retired runtime: the text route where the value entries are missing. -/
def fallback (eng : Engine V T E) (req : V) : Answer T E :=
  ofExcept (if eng.hasValue then eng.codec.valueRoute req else eng.codec.textRoute req)

/-- Every wire the runtime sends is the value route's answer. -/
theorem sent_is_value_route (eng : Engine V T E) (req : V) (wire : T)
    (h : encode eng req = .sent wire) : eng.codec.valueRoute req = .ok wire := by
  unfold encode at h
  split at h
  · cases hv : eng.codec.valueRoute req <;> simp_all [ofExcept]
  · cases h

/-- Where the value entries exist, nothing changes. -/
theorem unchanged_with_value_entries (eng : Engine V T E) (req : V) (h : eng.hasValue = true) :
    encode eng req = fallback eng req := by
  simp [encode, fallback, h]

/-- Two engines with one codec never send one request as different bytes. -/
theorem one_wire_per_request (c : Codec V T E) (a b : Bool) (req : V) (wa wb : T)
    (ha : encode ⟨c, a⟩ req = .sent wa) (hb : encode ⟨c, b⟩ req = .sent wb) : wa = wb := by
  have va := sent_is_value_route ⟨c, a⟩ req wa ha
  have vb := sent_is_value_route ⟨c, b⟩ req wb hb
  rw [va] at vb
  cases vb
  rfl

/-- The route contracts' oracle: on a canonical request the runtime's wire
is the one the codec's text entries give. -/
theorem oracle_sound (eng : Engine V T E) (req : V) (hreq : eng.codec.Canonical req) (wire : T)
    (h : encode eng req = .sent wire) : eng.codec.textRoute req = .ok wire := by
  rw [← routes_agree_canonical eng.codec req hreq]
  exact sent_is_value_route eng req wire h

/-- The retired fallback sends one request two ways, depending on the engine. -/
theorem fallback_sends_two_ways :
    fallback ⟨spelled, true⟩ (100, false) = .sent (100, false) ∧
      fallback ⟨spelled, false⟩ (100, false) = .sent (100, true) := by
  constructor <;> rfl

/-- The value route only refuses instead. -/
theorem value_only_refuses_instead :
    encode ⟨spelled, true⟩ (100, false) = .sent (100, false) ∧
      encode ⟨spelled, false⟩ (100, false) = .unavailable := by
  constructor <;> rfl

end Mettapedia.Protocols.Agents.ValueRouteOnly
