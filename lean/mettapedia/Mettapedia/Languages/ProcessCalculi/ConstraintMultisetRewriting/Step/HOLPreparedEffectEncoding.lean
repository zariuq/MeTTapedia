import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparationEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore

/-! # Lossless packets for the shared admitted-event interface

Each packet retains its complete indexed firing and preparation witness.
Its validity is independent of permission. The event equivalence preserves
both endpoints and does not identify parallel events with equal endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedEffectEncoding

open HOLPreparationEncoding

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

abbrev Witness (s : State) (f : Firing s) := E.Prepares f
abbrev RawPreparation := RawWitnesses State Firing (Witness E)

def next (s : State) (f : Firing s) (p : Witness E s f) : State := E.preparedResult f p
def permits (allow : E.Admission) (s : State) (f : Firing s) (p : Witness E s f) : Prop := allow f p

abbrev EventPacket (allow : E.Admission) (s t : State) :=
  { pair : RawFirings State Firing × RawPreparation E //
    prepares State Firing (Witness E) (some s) pair.1 pair.2 ∧
    some t = result State Firing (Witness E) (next E) pair.2 ∧
    permission State Firing (Witness E) (permits E allow) pair.2 }

def toPacket {allow : E.Admission} {s t : State} (event : E.Event allow s t) : EventPacket E allow s t :=
  ⟨(encodeFiring State Firing event.firing, encodeWitness State Firing (Witness E) event.firing event.prepared),
    prepares_encoded State Firing (Witness E) event.firing event.prepared,
    (congrArg some event.target_eq).symm, event.permitted⟩

def ofPacket {allow : E.Admission} {s t : State} (packet : EventPacket E allow s t) : E.Event allow s t := by
  rcases packet with ⟨⟨firing, witness⟩, valid⟩
  cases witness with
  | none => cases valid.1
  | some entry =>
      rcases entry with ⟨⟨source, f⟩, p⟩
      have same : s = source := Option.some.inj valid.1.1
      cases same
      exact ⟨f, p.down, valid.2.2, (Option.some.inj valid.2.1).symm⟩

theorem of_toPacket {allow : E.Admission} {s t : State} (event : E.Event allow s t) :
    ofPacket E (toPacket E event) = event := by
  cases event with
  | mk firing prepared permitted target =>
      cases target
      rfl

theorem to_ofPacket {allow : E.Admission} {s t : State} (packet : EventPacket E allow s t) :
    toPacket E (ofPacket E packet) = packet := by
  rcases packet with ⟨⟨firing, witness⟩, prepared, target, allowed⟩
  cases witness with
  | none => cases prepared
  | some entry =>
      rcases entry with ⟨⟨source, f⟩, p⟩
      have same : s = source := Option.some.inj prepared.1
      cases same
      have firingEq : firing = encodeFiring State Firing f := prepared.2
      cases firingEq
      rfl

def eventEquiv (allow : E.Admission) (s t : State) : E.Event allow s t ≃ EventPacket E allow s t where
  toFun := toPacket E
  invFun := ofPacket E
  left_inv := of_toPacket E
  right_inv := to_ofPacket E

theorem preparation_exists_iff {s : State} (f : Firing s) :
    (∃ raw, prepares State Firing (Witness E) (some s) (encodeFiring State Firing f) raw) ↔ E.Prepares f := by
  rw [witness_exists_iff]
  exact ⟨fun ⟨p⟩ => p, fun p => ⟨p⟩⟩

#print axioms eventEquiv
#print axioms preparation_exists_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedEffectEncoding
