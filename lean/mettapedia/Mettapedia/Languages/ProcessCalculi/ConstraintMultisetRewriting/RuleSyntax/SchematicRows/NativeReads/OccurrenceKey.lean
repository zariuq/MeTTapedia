import Mathlib.Data.Nat.Pairing
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-!
# View-local occurrences can carry their full origin

A row identity includes its store, instance, captured prefix generation and
slot, independently of payload and independently opened schema unknowns.
The unbounded mathematical encoding is injective. A bounded fast path is
checked before publication and declines without truncation when it cannot
represent the key. No fixed word width is imposed on the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads

structure OccurrenceKey where
  store : Nat
  incarnation : Nat
  generation : Nat
  slot : Nat
  deriving DecidableEq, Repr

namespace OccurrenceKey

def toHandle (key : OccurrenceKey) :
    Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle (Nat × Nat) Nat :=
  ⟨(key.store, key.incarnation), key.slot, key.generation⟩

def ofHandle (handle : Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle (Nat × Nat) Nat) :
    OccurrenceKey := ⟨handle.provider.1, handle.provider.2, handle.generation, handle.resource⟩

@[simp] theorem of_to_handle (key : OccurrenceKey) : ofHandle key.toHandle = key := by
  cases key
  rfl

theorem to_handle_injective : Function.Injective toHandle := by
  intro first second same
  have restored := congrArg ofHandle same
  simpa only [of_to_handle] using restored

def encode (key : OccurrenceKey) : Nat :=
  Nat.pair key.store (Nat.pair key.incarnation (Nat.pair key.generation key.slot)) + 1

def decode (word : Nat) : Option OccurrenceKey :=
  if word = 0 then none else
    let first := Nat.unpair (word - 1)
    let second := Nat.unpair first.2
    let third := Nat.unpair second.2
    some ⟨first.1, second.1, third.1, third.2⟩

@[simp] theorem decode_encode (key : OccurrenceKey) : decode key.encode = some key := by
  cases key
  simp [encode, decode, Nat.unpair_pair]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem generation_distinguishes (first second : OccurrenceKey)
    (different : first.generation ≠ second.generation) : first.encode ≠ second.encode := by
  intro same
  exact different (congrArg OccurrenceKey.generation (encode_injective same))

theorem slot_distinguishes (first second : OccurrenceKey)
    (different : first.slot ≠ second.slot) : first.encode ≠ second.encode := by
  intro same
  exact different (congrArg OccurrenceKey.slot (encode_injective same))

def checked (capacity : Nat) (key : OccurrenceKey) : Option Nat :=
  if key.encode < capacity then some key.encode else none

theorem checked_exact (capacity : Nat) (key : OccurrenceKey) (word : Nat)
    (accepted : checked capacity key = some word) :
    0 < word ∧ word < capacity ∧ decode word = some key := by
  unfold checked at accepted
  split at accepted
  next fits =>
    obtain rfl := Option.some.inj accepted
    exact ⟨by simp [encode], fits, decode_encode key⟩
  next _ => cases accepted

theorem checked_refuses_iff (capacity : Nat) (key : OccurrenceKey) :
    checked capacity key = none ↔ capacity ≤ key.encode := by
  simp [checked]

theorem checked_cannot_alias (capacity : Nat) (first second : OccurrenceKey) (word : Nat)
    (one : checked capacity first = some word) (two : checked capacity second = some word) : first = second := by
  have a := (checked_exact capacity first word one).2.2
  have b := (checked_exact capacity second word two).2.2
  exact Option.some.inj (a.symm.trans b)

#print axioms decode_encode
#print axioms to_handle_injective
#print axioms checked_exact
#print axioms checked_cannot_alias

end OccurrenceKey
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads
