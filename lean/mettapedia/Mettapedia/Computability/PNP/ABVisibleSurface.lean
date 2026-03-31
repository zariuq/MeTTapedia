import Mettapedia.Computability.PNP.VisiblePostSwitchSurface
import Mathlib.Data.Fin.Tuple.Basic

/-!
# P vs NP grassroots: the reduced raw visible surface `(a, b)`

The exact post-switch input is `u = (z, a, b)`. This file isolates the raw bit
surface obtained by dropping the latent local datum `z` and keeping only the
visible bit coordinates `(a, b)`.

The point is not to claim that the switched family truly ignores `z`. The point
is to make that prospective factorization target explicit.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ}

/-- The reduced raw visible bit surface keeping only `(a, b)`. -/
abbrev ABVisibleSurface (k : ℕ) := BitVec k × BitVec k

/-- The raw `(a, b)` projection from the exact post-switch surface. -/
def abVisibleData (u : ExactVisiblePostSwitchSurface Z k) : ABVisibleSurface k :=
  (u.a, u.b)

@[simp] theorem abVisibleData_eq (u : ExactVisiblePostSwitchSurface Z k) :
    abVisibleData u = (u.a, u.b) := rfl

@[simp] theorem abVisibleData_tiInputMap (u : ExactVisiblePostSwitchSurface Z k) :
    abVisibleData (tiInputMap u) = (u.a, vvToggle u.a u.b) := by
  rfl

/-- Concatenate the two raw visible bit blocks into one `2k`-bit vector. -/
def abVisibleBits (x : ABVisibleSurface k) : BitVec (k + k) :=
  Fin.append x.1 x.2

@[simp] theorem abVisibleBits_mk (a b : BitVec k) :
    abVisibleBits (k := k) (a, b) = Fin.append a b := rfl

theorem exactABVisibleData_bits (u : ExactVisiblePostSwitchSurface Z k) :
    abVisibleBits (k := k) (abVisibleData u) = Fin.append u.a u.b := by
  rfl

theorem card_abVisibleSurface (k : ℕ) :
    Fintype.card (ABVisibleSurface k) = 2 ^ (2 * k) := by
  calc
    Fintype.card (ABVisibleSurface k) = 2 ^ k * 2 ^ k := by
      simp [ABVisibleSurface, BitVec]
    _ = 2 ^ (k + k) := by rw [← Nat.pow_add]
    _ = 2 ^ (2 * k) := by simp [two_mul]

end

end Mettapedia.Computability.PNP
