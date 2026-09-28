import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mathlib.Data.Countable.Defs

/-!
# Encoding terms by numbers

Terms of the presentation are encoded injectively by natural numbers, given an
injective encoding of the universe heads:

* two numbers are paired by `2 ^ a * (2 * b + 1)`;
* a string is encoded by its UTF-8 bytes, and a name by its components;
* each term former is tagged, and its immediate subterms are paired.

The encodings are elementary and their injectivity is proved without choice.
So the terms over countably many heads are countably many.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace TermEncoding

/-! ## Pairing -/

/-- The pairing `2 ^ a * (2 * b + 1)` of two natural numbers. -/
def pairing (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem pairing_zero (b : Nat) : pairing 0 b = 2 * b + 1 := by
  rw [pairing, Nat.pow_zero, Nat.one_mul]

theorem pairing_succ (a b : Nat) : pairing (a + 1) b = 2 * pairing a b := by
  rw [pairing, pairing, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

theorem pairing_ne_zero (a b : Nat) : pairing a b ≠ 0 :=
  Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos a)) (Nat.succ_ne_zero _)

theorem pairing_injective : ∀ {a b c d : Nat}, pairing a b = pairing c d → a = c ∧ b = d
  | 0, _, 0, _, h => by
      rw [pairing_zero, pairing_zero] at h
      exact ⟨rfl, by omega⟩
  | 0, _, _ + 1, _, h => by
      rw [pairing_zero, pairing_succ] at h
      omega
  | _ + 1, _, 0, _, h => by
      rw [pairing_succ, pairing_zero] at h
      omega
  | _ + 1, _, _ + 1, _, h => by
      rw [pairing_succ, pairing_succ] at h
      obtain ⟨rfl, rfl⟩ := pairing_injective (Nat.eq_of_mul_eq_mul_left (by decide) h)
      exact ⟨rfl, rfl⟩

/-! ## Strings and names -/

/-- The encoding of a list of bytes. -/
def encodeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => pairing b.toNat (encodeBytes bs)

theorem encodeBytes_injective : Function.Injective encodeBytes := by
  intro l l' h
  induction l generalizing l' with
  | nil =>
      cases l' with
      | nil => rfl
      | cons => exact absurd h.symm (pairing_ne_zero _ _)
  | cons b bs ih =>
      cases l' with
      | nil => exact absurd h (pairing_ne_zero _ _)
      | cons b' bs' =>
          obtain ⟨hb, hbs⟩ := pairing_injective h
          rw [UInt8.toNat_inj.mp hb, ih hbs]

/-- The encoding of a string: the encoding of its UTF-8 bytes. -/
def encodeString (s : String) : Nat := encodeBytes s.toByteArray.data.toList

theorem encodeString_injective : Function.Injective encodeString := fun _ _ h =>
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (encodeBytes_injective h)))

/-- The encoding of a name, component by component. -/
def encodeName : Lean.Name → Nat
  | .anonymous => 0
  | .str p s => pairing 0 (pairing (encodeName p) (encodeString s))
  | .num p i => pairing 1 (pairing (encodeName p) i)

theorem encodeName_injective : Function.Injective encodeName := by
  intro x y h
  induction x generalizing y with
  | anonymous =>
      cases y with
      | anonymous => rfl
      | _ => exact absurd h.symm (pairing_ne_zero _ _)
  | str p s ih =>
      cases y with
      | anonymous => exact absurd h (pairing_ne_zero _ _)
      | str p' s' =>
          obtain ⟨hp, hs⟩ := pairing_injective (pairing_injective h).2
          rw [ih hp, encodeString_injective hs]
      | num => exact absurd (pairing_injective h).1 (by decide)
  | num p i ih =>
      cases y with
      | anonymous => exact absurd h (pairing_ne_zero _ _)
      | str => exact absurd (pairing_injective h).1 (by decide)
      | num p' i' =>
          obtain ⟨hp, hi⟩ := pairing_injective (pairing_injective h).2
          rw [ih hp, hi]

end TermEncoding

open TermEncoding

/-! ## Terms -/

variable {Head : Type}

/-- The encoding of a term, given an encoding of the heads: a tag for the former,
paired with the encodings of its immediate parts. -/
def Tm.encode (h : Head → Nat) : {n : Nat} → Tm Head n → Nat
  | _, .var i => pairing 0 i.val
  | _, .const c => pairing 1 (encodeName c)
  | _, .head x => pairing 2 (h x)
  | _, .pi A B => pairing 3 (pairing (Tm.encode h A) (Tm.encode h B))
  | _, .sigma A B => pairing 4 (pairing (Tm.encode h A) (Tm.encode h B))
  | _, .id A a b => pairing 5 (pairing (Tm.encode h A) (pairing (Tm.encode h a) (Tm.encode h b)))
  | _, .lam body => pairing 6 (Tm.encode h body)
  | _, .app f a => pairing 7 (pairing (Tm.encode h f) (Tm.encode h a))
  | _, .pair a b => pairing 8 (pairing (Tm.encode h a) (Tm.encode h b))
  | _, .fst p => pairing 9 (Tm.encode h p)
  | _, .snd p => pairing 10 (Tm.encode h p)
  | _, .refl a => pairing 11 (Tm.encode h a)

/-- Distinct terms have distinct encodings when distinct heads do. -/
theorem Tm.encode_injective {h : Head → Nat} (injective : Function.Injective h) :
    ∀ {n : Nat} {t t' : Tm Head n}, Tm.encode h t = Tm.encode h t' → t = t' := by
  intro n t
  induction t with
  | var i =>
      intro t' e
      cases t' with
      | var j => exact congrArg Tm.var (Fin.ext (pairing_injective e).2)
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | const c =>
      intro t' e
      cases t' with
      | const c' => exact congrArg Tm.const (encodeName_injective (pairing_injective e).2)
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | head x =>
      intro t' e
      cases t' with
      | head x' => exact congrArg Tm.head (injective (pairing_injective e).2)
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | pi A B ihA ihB =>
      intro t' e
      cases t' with
      | pi A' B' =>
          obtain ⟨eA, eB⟩ := pairing_injective (pairing_injective e).2
          rw [ihA eA, ihB eB]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | sigma A B ihA ihB =>
      intro t' e
      cases t' with
      | sigma A' B' =>
          obtain ⟨eA, eB⟩ := pairing_injective (pairing_injective e).2
          rw [ihA eA, ihB eB]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | id A a b ihA iha ihb =>
      intro t' e
      cases t' with
      | id A' a' b' =>
          obtain ⟨eA, e'⟩ := pairing_injective (pairing_injective e).2
          obtain ⟨ea, eb⟩ := pairing_injective e'
          rw [ihA eA, iha ea, ihb eb]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | lam body ih =>
      intro t' e
      cases t' with
      | lam body' => rw [ih (pairing_injective e).2]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | app f a ihf iha =>
      intro t' e
      cases t' with
      | app f' a' =>
          obtain ⟨ef, ea⟩ := pairing_injective (pairing_injective e).2
          rw [ihf ef, iha ea]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | pair a b iha ihb =>
      intro t' e
      cases t' with
      | pair a' b' =>
          obtain ⟨ea, eb⟩ := pairing_injective (pairing_injective e).2
          rw [iha ea, ihb eb]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | fst p ih =>
      intro t' e
      cases t' with
      | fst p' => rw [ih (pairing_injective e).2]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | snd p ih =>
      intro t' e
      cases t' with
      | snd p' => rw [ih (pairing_injective e).2]
      | _ => exact absurd (pairing_injective e).1 (by decide)
  | refl a ih =>
      intro t' e
      cases t' with
      | refl a' => rw [ih (pairing_injective e).2]
      | _ => exact absurd (pairing_injective e).1 (by decide)

instance instCountableName : Countable Lean.Name := ⟨⟨encodeName, encodeName_injective⟩⟩

/-- The terms over countably many heads are countably many. -/
instance instCountableTm {n : Nat} [Countable Head] : Countable (Tm Head n) := by
  obtain ⟨h, injective⟩ := Countable.exists_injective_nat Head
  exact ⟨⟨Tm.encode h, fun _ _ e => Tm.encode_injective injective e⟩⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
