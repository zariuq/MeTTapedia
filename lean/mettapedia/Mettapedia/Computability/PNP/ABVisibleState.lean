import Mettapedia.Computability.PNP.VisiblePostSwitchData
import Mathlib.Data.Fin.Tuple.Basic

/-!
# P vs NP grassroots: the reduced raw visible data domain `(a, b)`

The exact post-switch input is `u = (z, a, b)`. This file isolates the raw bit
data domain obtained by dropping the latent local datum `z` and keeping only the
visible bit coordinates `(a, b)`.

The point is not to claim that the switched family truly ignores `z`. The point
is to make that prospective factorization target explicit.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ}

/-- The reduced raw visible bit data domain keeping only `(a, b)`. -/
abbrev ABVisibleState (k : ℕ) := BitVec k × BitVec k

/-- The raw `(a, b)` projection from the exact post-switch data domain. -/
def abVisibleData (u : ExactVisiblePostSwitchData Z k) : ABVisibleState k :=
  (u.a, u.b)

@[simp] theorem abVisibleData_eq (u : ExactVisiblePostSwitchData Z k) :
    abVisibleData u = (u.a, u.b) := rfl

@[simp] theorem abVisibleData_tiInputMap (u : ExactVisiblePostSwitchData Z k) :
    abVisibleData (tiInputMap u) = (u.a, vvToggle u.a u.b) := by
  rfl

/-- Concatenate the two raw visible bit blocks into one `2k`-bit vector. -/
def abVisibleBits (x : ABVisibleState k) : BitVec (k + k) :=
  Fin.append x.1 x.2

@[simp] theorem abVisibleBits_mk (a b : BitVec k) :
    abVisibleBits (k := k) (a, b) = Fin.append a b := rfl

theorem exactABVisibleData_bits (u : ExactVisiblePostSwitchData Z k) :
    abVisibleBits (k := k) (abVisibleData u) = Fin.append u.a u.b := by
  rfl

theorem card_abVisibleDataDomain (k : ℕ) :
    Fintype.card (ABVisibleState k) = 2 ^ (2 * k) := by
  calc
    Fintype.card (ABVisibleState k) = 2 ^ k * 2 ^ k := by
      simp [ABVisibleState, BitVec]
    _ = 2 ^ (k + k) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * k) := by simp [two_mul]

end

end Mettapedia.Computability.PNP
