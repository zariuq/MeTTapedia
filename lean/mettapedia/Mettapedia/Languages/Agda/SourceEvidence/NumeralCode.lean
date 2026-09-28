import Mettapedia.Languages.Agda.SourceEvidence.RawCode

/-!
A direct constructive numeral encoding of finite binary codes. Diagonal
pairing is decoded by its primitive recursive traversal. The proofs use only
natural-number induction and checked arithmetic; no choice-based pairing
bijection or generic Encodable derivation is used. This reference codec makes
no efficiency claim about numeral search or large serialized trees.
-/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec.Numeral

/-- The index of the beginning of a diagonal. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n + 1

def pair (a b : Nat) : Nat := triangle (a + b) + b

/-- Enumerate each diagonal in its fixed left-to-right order. -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => match unpair n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

theorem walk {m a b : Nat} (start : unpair m = (a, b)) :
    ∀ k, k ≤ a → unpair (m + k) = (a - k, b + k)
  | 0, _ => by simpa using start
  | k + 1, h => by
    have previous := walk start k (by omega)
    have positive : 0 < a - k := by omega
    rw [Nat.add_succ, unpair, previous]
    cases e : a - k with
    | zero => omega
    | succ c =>
        simp only
        have remaining : a - (k + 1) = c := by omega
        simp only [remaining, Nat.add_succ]

theorem diagonal_start (n : Nat) : unpair (triangle n) = (n, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have last := walk ih n (Nat.le_refl n)
      simp only [Nat.sub_self, Nat.zero_add] at last
      simp only [triangle, unpair, last]

@[simp] theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have traversed := walk (diagonal_start (a + b)) b (by omega)
  simpa only [pair, Nat.add_sub_cancel, Nat.zero_add] using traversed

theorem sum_le (n : Nat) : (unpair n).1 + (unpair n).2 ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases h : unpair n with
      | mk a b =>
          rw [h] at ih
          cases a with
          | zero => simpa only [unpair, h, Nat.zero_add, Nat.add_zero] using Nat.succ_le_succ ih
          | succ a => simp only [unpair, h] at ih ⊢; omega

def encode : Code → Nat
  | .atom n => 2 * n
  | .pair a b => 2 * pair (encode a) (encode b) + 1

def decode (n : Nat) : Code :=
  if even : n % 2 = 0 then .atom (n / 2)
  else
    let components := unpair (n / 2)
    .pair (decode components.1) (decode components.2)
termination_by n
decreasing_by
  all_goals
    have bound := sum_le (n / 2)
    have positive : 0 < n := by omega
    have half : n / 2 < n := Nat.div_lt_self positive (by decide)
    omega

@[simp] theorem decode_encode (code : Code) : decode (encode code) = code := by
  induction code with
  | atom n => rw [encode, decode]; simp
  | pair a b left right =>
      have half : (2 * pair (encode a) (encode b) + 1) / 2 = pair (encode a) (encode b) := by
        omega
      rw [encode, decode]
      simp [half, left, right]

end Mettapedia.Languages.Agda.SourceEvidence.Codec.Numeral

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec

instance codeEncodable : Encodable Code where
  encode := Numeral.encode
  decode := some ∘ Numeral.decode
  encodek code := congrArg some (Numeral.decode_encode code)

end Mettapedia.Languages.Agda.SourceEvidence.Codec
