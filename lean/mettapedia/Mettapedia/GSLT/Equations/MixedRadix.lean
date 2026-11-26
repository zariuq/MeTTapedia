import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log

/-! # Pack the remaining choices, not a separate word for each choice

Given a dictionary for each position (for example the spellings of the
known quotient class), the ranks form a mixed-radix number. This executable
codec attains the exact fixed-width bit floor for independent choices.
It does not include the dictionaries, framing, or indexing metadata in
that conditional budget, and does not promise constant-time random access.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.MixedRadix

def Digits : List Nat → Type
  | [] => Unit
  | k :: ks => Fin k × Digits ks

/-- Use ordinary mixed-radix positional rank; division and remainder
recover the first position and the rest. Zero-sized fibres have no codes. -/
def rank : (radices : List Nat) → Digits radices ≃ Fin radices.prod
  | [] => {
      toFun := fun _ => (0 : Fin 1)
      invFun := fun _ => ()
      left_inv := fun x => Subsingleton.elim (α := Unit) _ x
      right_inv := fun x => Subsingleton.elim (α := Fin 1) _ x }
  | k :: ks =>
    (Equiv.prodCongr (Equiv.refl (Fin k)) (rank ks)).trans finProdFinEquiv

def width (radices : List Nat) : Nat := Nat.clog 2 radices.prod

theorem capacity (radices : List Nat) : radices.prod ≤ 2 ^ width radices :=
  Nat.le_pow_clog (by decide) _

def encode (radices : List Nat) (digits : Digits radices) : BitVec (width radices) :=
  ⟨(Fin.castLE (capacity radices)) (rank radices digits)⟩

def decode (radices : List Nat) (word : BitVec (width radices)) : Option (Digits radices) :=
  if valid : word.toNat < radices.prod then
    some ((rank radices).symm ⟨word.toNat, valid⟩)
  else none

@[simp] theorem encode_value (radices : List Nat) (digits : Digits radices) :
    (encode radices digits).toNat = (rank radices digits).val := rfl

@[simp] theorem decode_encode (radices : List Nat) (digits : Digits radices) :
    decode radices (encode radices digits) = some digits := by
  unfold decode
  rw [encode_value, dif_pos (rank radices digits).isLt]
  exact congrArg some ((rank radices).left_inv digits)

theorem unused_codes_refused (radices : List Nat) (word : BitVec (width radices))
    (unused : radices.prod ≤ word.toNat) : decode radices word = none := by
  simp [decode, not_lt_of_ge unused]

/-- No smaller fixed-width lossless encoding of this whole fibre domain
exists. A b-bit word has exactly 2^b values, represented here as Fin. -/
theorem fixed_width_optimal (radices : List Nat) (bits : Nat) :
    Nonempty (Digits radices ↪ Fin (2 ^ bits)) ↔ width radices ≤ bits := by
  rw [width, Nat.clog_le_iff_le_pow (by decide)]
  constructor
  · rintro ⟨enc⟩
    have fits := Fintype.card_le_of_embedding ((rank radices).symm.toEmbedding.trans enc)
    simpa using fits
  · intro enough
    exact ⟨(rank radices).toEmbedding.trans (Fin.castLEEmb enough)⟩

end Mettapedia.GSLT.Equations.MixedRadix
