import Mettapedia.Computability.PNP.ExactZABDecisionListFamily
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# P vs NP grassroots: the exact visible data domain when `z` is already bit-valued

When the latent local datum is already a bitvector `z : BitVec r`, the full
exact visible data domain `(z, a, b)` admits a canonical raw bitvector view of
length `r + 2k`.

This file records that concrete visible-data map and its cardinality.  It does
not prove the switched family is small; it only removes one layer of
abstraction from the optimistic route.
-/

namespace Mettapedia.Computability.PNP

section

variable {r k : ℕ}

/-- The full exact visible data domain as one raw bitvector when `z : BitVec r`. -/
abbrev BitVecZABVisibleState (r k : ℕ) := BitVec (r + (k + k))

/-- The corresponding raw visible-data map. -/
def bitVecZABVisibleData
    (u : ExactVisiblePostSwitchData (BitVec r) k) : BitVecZABVisibleState r k :=
  exactZABVisibleData (Z := BitVec r) (r := r) (k := k) (fun z => z) u

@[simp] theorem bitVecZABVisibleData_eq
    (u : ExactVisiblePostSwitchData (BitVec r) k) :
    bitVecZABVisibleData (r := r) (k := k) u = Fin.append u.z (Fin.append u.a u.b) := by
  rfl

@[simp] theorem bitVecZABVisibleData_tiInputMap
    (u : ExactVisiblePostSwitchData (BitVec r) k) :
    bitVecZABVisibleData (r := r) (k := k) (tiInputMap u) =
      Fin.append u.z (Fin.append u.a (vvToggle u.a u.b)) := by
  rfl

theorem card_bitVecZABVisibleState (r k : ℕ) :
    Fintype.card (BitVecZABVisibleState r k) = 2 ^ (r + 2 * k) := by
  calc
    Fintype.card (BitVecZABVisibleState r k) = 2 ^ (r + (k + k)) := by
      simp [BitVecZABVisibleState, BitVec]
    _ = 2 ^ (r + 2 * k) := by simp [two_mul]

end

end Mettapedia.Computability.PNP
