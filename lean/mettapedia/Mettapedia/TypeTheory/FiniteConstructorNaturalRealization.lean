import Mettapedia.TypeTheory.FiniteConstructorEncoding
import Mettapedia.TypeTheory.IndexedPolynomialGuardedRepresentation
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Natural-number realization of represented finite constructor layers

For constructively countable source data, a total constructor stores the tag,
the complete decoded data and every active child in a natural number. Zero is
reserved for invalid payloads. Payload recognition uses classical choice; this
is a semantic realization, not an executable recognizer for raw functions.

Field recovery is proved for represented payloads with canonical unused slots.
An arbitrary joint source condition is retained. The existing slot codec owns
canonicality; no unrestricted raw-function injectivity is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization
open IndexedPolynomial
universe u s
variable {SortCode : Type s} (Value : SortCode → Type u)
    (signature : Signature (SortCode := SortCode))

noncomputable def decodePayload (payload : Payload Value signature) : Option (Data Value signature) := by
  classical
  exact if valid : Valid Value signature payload then some valid.choose else none

theorem decodePayload_encode (data : Data Value signature) :
    decodePayload Value signature (encode Value signature data) = some data := by
  classical
  unfold decodePayload
  rw [dif_pos (show Valid Value signature (encode Value signature data) from ⟨data,rfl⟩)]
  apply congrArg some
  exact encode_injective Value signature (Exists.choose_spec (show Valid Value signature
    (encode Value signature data) from ⟨data,rfl⟩))

theorem decodePayload_sound (payload : Payload Value signature) (data : Data Value signature)
    (decoded : decodePayload Value signature payload = some data) : encode Value signature data = payload := by
  classical
  unfold decodePayload at decoded
  split at decoded
  · rename_i valid
    cases Option.some.inj decoded
    exact valid.choose_spec
  · cases decoded

def slots (count : Nat) : SlotEncoding (Fin count) Nat := SlotEncoding.finite (Equiv.refl _)

def snapshot (count : Nat) (children : Nat → Nat) : List Nat :=
  List.ofFn (fun slot : Fin count => children slot.val)

theorem snapshot_recovers {count : Nat} {first second : Nat → Nat}
    (firstCanonical : (slots count).Canonical 0 first)
    (secondCanonical : (slots count).Canonical 0 second)
    (same : snapshot count first = snapshot count second) : first = second := by
  have active : (slots count).restrict first = (slots count).restrict second := by
    exact List.ofFn_injective same
  calc
    first = (slots count).extend 0 ((slots count).restrict first) :=
      ((slots count).extend_restrict 0 first firstCanonical).symm
    _ = (slots count).extend 0 ((slots count).restrict second) := congrArg ((slots count).extend 0) active
    _ = second := (slots count).extend_restrict 0 second secondCanonical

variable [Encodable (Data Value signature)] (arity : Data Value signature → Nat)

noncomputable def construct (tag : Nat) (payload : Payload Value signature) (children : Nat → Nat) : Nat :=
  match decodePayload Value signature payload with
  | none => 0
  | some data => Nat.succ (Encodable.encode (tag,data,snapshot (arity data) children))

theorem construct_encode (tag : Nat) (data : Data Value signature) (children : Nat → Nat) :
    construct Value signature arity tag (encode Value signature data) children =
      Nat.succ (Encodable.encode (tag,data,snapshot (arity data) children)) := by
  simp only [construct,decodePayload_encode]

def decodeNode : Nat → Option (Nat × Data Value signature × List Nat)
  | 0 => none
  | n + 1 => Encodable.decode n

theorem decodeNode_construct (tag : Nat) (data : Data Value signature) (children : Nat → Nat) :
    decodeNode Value signature (construct Value signature arity tag (encode Value signature data) children) =
      some (tag,data,snapshot (arity data) children) := by
  rw [construct_encode]
  exact Encodable.encodek _

def Admitted (allowed : Nat → Data Value signature → (Nat → Nat) → Prop)
    (tag : Nat) (payload : Payload Value signature) (children : Nat → Nat) : Prop :=
  ∃ data, payload = encode Value signature data ∧ allowed tag data children ∧
    (slots (arity data)).Canonical 0 children

omit [Encodable (Data Value signature)] in
theorem admitted_encode (allowed : Nat → Data Value signature → (Nat → Nat) → Prop)
    (tag : Nat) (data : Data Value signature) (children : Nat → Nat)
    (permitted : allowed tag data children) (canonical : (slots (arity data)).Canonical 0 children) :
    Admitted Value signature arity allowed tag (encode Value signature data) children :=
  ⟨data,rfl,permitted,canonical⟩

theorem construct_nonzero (allowed : Nat → Data Value signature → (Nat → Nat) → Prop)
    (tag : Nat) (payload : Payload Value signature) (children : Nat → Nat)
    (admitted : Admitted Value signature arity allowed tag payload children) :
    construct Value signature arity tag payload children ≠ 0 := by
  obtain ⟨data,rfl,_permitted,_canonical⟩ := admitted
  rw [construct_encode]
  exact Nat.succ_ne_zero _

theorem fields_of_eq (allowed : Nat → Data Value signature → (Nat → Nat) → Prop)
    (firstTag secondTag : Nat) (firstPayload secondPayload : Payload Value signature)
    (firstChildren secondChildren : Nat → Nat)
    (firstAdmitted : Admitted Value signature arity allowed firstTag firstPayload firstChildren)
    (secondAdmitted : Admitted Value signature arity allowed secondTag secondPayload secondChildren)
    (same : construct Value signature arity firstTag firstPayload firstChildren =
      construct Value signature arity secondTag secondPayload secondChildren) :
    firstTag = secondTag ∧ firstPayload = secondPayload ∧ firstChildren = secondChildren := by
  obtain ⟨firstData,rfl,_firstAllowed,firstCanonical⟩ := firstAdmitted
  obtain ⟨secondData,rfl,_secondAllowed,secondCanonical⟩ := secondAdmitted
  rw [construct_encode,construct_encode] at same
  have encoded := Encodable.encode_injective (Nat.succ.inj same)
  have dataSame := congrArg (fun node : Nat × Data Value signature × List Nat => node.2.1) encoded
  cases dataSame
  exact ⟨congrArg Prod.fst encoded,rfl,
    snapshot_recovers firstCanonical secondCanonical (congrArg (fun node => node.2.2) encoded)⟩

omit [Encodable (Data Value signature)] in
theorem invalid_not_admitted (allowed : Nat → Data Value signature → (Nat → Nat) → Prop)
    (tag : Nat) (children : Nat → Nat) :
    ¬ Admitted Value signature arity allowed tag (unused Value signature) children := by
  rintro ⟨data,same,_⟩
  exact unused_not_valid Value signature ⟨data,same.symm⟩

theorem construct_unused (tag : Nat) (children : Nat → Nat) :
    construct Value signature arity tag (unused Value signature) children = 0 := by
  classical
  simp only [construct,decodePayload,dif_neg (unused_not_valid Value signature)]

#print axioms fields_of_eq
#print axioms decodeNode_construct
end Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization
