import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mathlib.Data.Multiset.Count

/-!
# Framed answer displays and explicit answer observations

A display is a sequence of framed value payloads followed by one completion
event. Its decoder checks framing and decodes each payload; empty enumeration,
one empty collection, duplicate occurrences and incomplete enumeration are
different observations. The construction is parametric in the payload codec,
not in an assumed whole-transcript reader.

Order-preserving display is appropriate for exact occurrence enumeration.
Bag and support projections below are explicit choices of observation, not a
claim that every query has the same answer effect. A support-valued query can
deliberately forget multiplicity; a complete exact-occurrence display cannot.

This is a structural display protocol, not a proof about existing CLI text
formatters. Mapping the event markers and payload codec to concrete bytes is
a separate implementation obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AnswerDisplay

universe u v

/-- Termination status is retained even when the answer enumeration is empty. -/
inductive Completion where
  | complete
  | suspended (reason : String)
  | failed (diagnostic : String)
  deriving DecidableEq, Repr

inductive Event (Wire : Type u) where
  | answer : Wire → Event Wire
  | finish : Completion → Event Wire
  deriving Repr

variable {Value : Type u} {Wire : Type v}

def encode (encodeValue : Value → Option Wire) (values : List Value)
    (completion : Completion) : Option (List (Event Wire)) := do
  let payloads ← values.mapM encodeValue
  return payloads.map Event.answer ++ [.finish completion]

def decode (decodeValue : Wire → Option Value) :
    List (Event Wire) → Option (List Value × Completion)
  | [] => none
  | .finish completion :: [] => some ([], completion)
  | .finish _ :: _ :: _ => none
  | .answer wire :: events => do
    let value ← decodeValue wire
    let (values, completion) ← decode decodeValue events
    return (value :: values, completion)

theorem encode_total (encodeValue : Value → Option Wire)
    (total : ∀ value, ∃ wire, encodeValue value = some wire)
    (values : List Value) (completion : Completion) :
    ∃ events, encode encodeValue values completion = some events := by
  have payloads : ∃ wires, values.mapM encodeValue = some wires := by
    induction values with
    | nil => exact ⟨[], rfl⟩
    | cons value values ih =>
      obtain ⟨wire, head⟩ := total value
      obtain ⟨wires, tail⟩ := ih
      exact ⟨wire :: wires, by simp [List.mapM_cons, head, tail]⟩
  obtain ⟨wires, payloads⟩ := payloads
  exact ⟨wires.map Event.answer ++ [.finish completion], by simp [encode, payloads]⟩

theorem decode_encoded_payloads
    (encodeValue : Value → Option Wire) (decodeValue : Wire → Option Value)
    (codec : ∀ value wire, encodeValue value = some wire → decodeValue wire = some value)
    (values : List Value) (payloads : List Wire)
    (encoded : values.mapM encodeValue = some payloads) (completion : Completion) :
    decode decodeValue (payloads.map Event.answer ++ [.finish completion]) =
      some (values, completion) := by
  induction values generalizing payloads with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at encoded
    subst payloads
    rfl
  | cons value values ih =>
    cases head : encodeValue value with
    | none => simp [List.mapM_cons, head] at encoded
    | some wire =>
      cases tail : values.mapM encodeValue with
      | none => simp [List.mapM_cons, head, tail] at encoded
      | some wires =>
        simp [List.mapM_cons, head, tail] at encoded
        subst payloads
        simp [decode, codec value wire head, ih wires tail]

/-- Decoding an encoded display preserves every occurrence and the final status. -/
theorem decode_encode
    (encodeValue : Value → Option Wire) (decodeValue : Wire → Option Value)
    (codec : ∀ value wire, encodeValue value = some wire → decodeValue wire = some value)
    (values : List Value) (completion : Completion) (events : List (Event Wire))
    (encoded : encode encodeValue values completion = some events) :
    decode decodeValue events = some (values, completion) := by
  cases payloads : values.mapM encodeValue with
  | none => simp [encode, payloads] at encoded
  | some wires =>
    simp [encode, payloads] at encoded
    subst events
    exact decode_encoded_payloads encodeValue decodeValue codec values wires payloads completion

theorem encode_injective_on_domain
    (encodeValue : Value → Option Wire) (decodeValue : Wire → Option Value)
    (codec : ∀ value wire, encodeValue value = some wire → decodeValue wire = some value)
    (left right : List Value) (leftStatus rightStatus : Completion)
    (events : List (Event Wire))
    (encodedLeft : encode encodeValue left leftStatus = some events)
    (encodedRight : encode encodeValue right rightStatus = some events) :
    left = right ∧ leftStatus = rightStatus := by
  have leftRead := decode_encode encodeValue decodeValue codec left leftStatus events encodedLeft
  have rightRead := decode_encode encodeValue decodeValue codec right rightStatus events encodedRight
  rw [leftRead] at rightRead
  exact Prod.mk.inj (Option.some.inj rightRead)

/-- Any chosen answer observation is applied after exact payload recovery. -/
theorem decode_observation {Observation : Type*}
    (encodeValue : Value → Option Wire) (decodeValue : Wire → Option Value)
    (codec : ∀ value wire, encodeValue value = some wire → decodeValue wire = some value)
    (observe : List Value → Observation)
    (values : List Value) (completion : Completion) (events : List (Event Wire))
    (encoded : encode encodeValue values completion = some events) :
    (decode decodeValue events).map (fun result => (observe result.1, result.2)) =
      some (observe values, completion) := by
  rw [decode_encode encodeValue decodeValue codec values completion events encoded]
  rfl

def bagView (values : List Value) : Multiset Value :=
  AnswerEffects.listToBag.map values

def supportView [DecidableEq Value] (values : List Value) : Finset Value :=
  (bagView values).toFinset

/-- The optional bag observation forgets order, not occurrences. -/
theorem bagView_count [DecidableEq Value] (values : List Value) (value : Value) :
    (bagView values).count value = values.count value := by
  exact Multiset.coe_count value values

theorem bagView_eq_iff_perm (left right : List Value) :
    bagView left = bagView right ↔ left.Perm right := Multiset.coe_eq_coe

/-- The optional set observation reports precisely the values that occurred. -/
theorem supportView_mem [DecidableEq Value] (values : List Value) (value : Value) :
    value ∈ supportView values ↔ value ∈ values := by
  simp [supportView, bagView]

theorem bagView_retains_duplicate (value : Value) :
    bagView [value, value] ≠ bagView [value] := by
  intro equal
  have := congrArg Multiset.card equal
  simp [bagView] at this

theorem supportView_forgets_duplicate [DecidableEq Value] (value : Value) :
    supportView [value, value] = supportView [value] := by
  simp [supportView, bagView]

/-- Every occurrence of a successfully printed value remains an answer frame. -/
theorem encode_answer_count (encodeValue : Value → Option Wire)
    (values : List Value) (completion : Completion) (events : List (Event Wire))
    (encoded : encode encodeValue values completion = some events) :
    events.length = values.length + 1 := by
  cases payloads : values.mapM encodeValue with
  | none => simp [encode, payloads] at encoded
  | some wires =>
    simp [encode, payloads] at encoded
    subst events
    have length : wires.length = values.length := by
      induction values generalizing wires with
      | nil =>
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at payloads
        subst wires
        rfl
      | cons value values ih =>
        cases head : encodeValue value with
        | none => simp [List.mapM_cons, head] at payloads
        | some wire =>
          cases tail : values.mapM encodeValue with
          | none => simp [List.mapM_cons, head, tail] at payloads
          | some rest =>
            simp [List.mapM_cons, head, tail] at payloads
            subst wires
            simpa using congrArg Nat.succ (ih rest tail)
    simp [length]

theorem truncated_display_rejected (decodeValue : Wire → Option Value) :
    decode decodeValue [] = none := rfl

theorem trailing_display_rejected (decodeValue : Wire → Option Value)
    (completion : Completion) (event : Event Wire) (events : List (Event Wire)) :
    decode decodeValue (.finish completion :: event :: events) = none := rfl

theorem no_answers_has_explicit_status (decodeValue : Wire → Option Value)
    (completion : Completion) :
    decode decodeValue [.finish completion] = some ([], completion) := rfl

theorem incomplete_not_complete (reason : String) :
    Completion.suspended reason ≠ .complete := by intro h; cases h

/-- Malformed payloads cannot be hidden by a valid completion marker. -/
theorem invalid_payload_rejected (decodeValue : Wire → Option Value) (wire : Wire)
    (invalid : decodeValue wire = none) (completion : Completion) :
    decode decodeValue [.answer wire, .finish completion] = none := by
  simp [decode, invalid]

#print axioms decode_encode
#print axioms encode_injective_on_domain
#print axioms bagView_retains_duplicate
#print axioms supportView_mem

end Mettapedia.GSLT.Dynamics.AnswerDisplay
