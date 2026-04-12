import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

namespace Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1

/-!
# Seven Sketches, Chapter 1: Orders and Adjunctions

This file starts the Codex-side Chapter 1 development with one of the cleanest
set-level adjunction examples: direct image and inverse image between powersets.
-/

open Set

variable {X Y : Type*}

/-- Direct image along a function, regarded as a monotone map between powersets. -/
def directImage (f : X → Y) : Set X → Set Y := fun S => f '' S

/-- Inverse image along a function, regarded as a monotone map between powersets. -/
def inverseImage (f : X → Y) : Set Y → Set X := fun T => f ⁻¹' T

theorem directImage_monotone (f : X → Y) : Monotone (directImage f) := by
  intro A B hAB y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hAB hx, rfl⟩

theorem inverseImage_monotone (f : X → Y) : Monotone (inverseImage f) := by
  intro A B hAB x hx
  exact hAB hx

/-- Image/preimage form a Galois connection on powersets. -/
theorem directImage_inverseImage_gc (f : X → Y) :
    GaloisConnection (directImage f) (inverseImage f) := by
  intro S T
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx

/-- Positive example: every set is contained in the inverse image of its direct image. -/
theorem subset_inverseImage_directImage (f : X → Y) (S : Set X) :
    S ⊆ inverseImage f (directImage f S) :=
  (directImage_inverseImage_gc f).le_u_l S

/-- Positive example: the direct image of an inverse image is contained in the target set. -/
theorem directImage_inverseImage_subset (f : X → Y) (T : Set Y) :
    directImage f (inverseImage f T) ⊆ T :=
  (directImage_inverseImage_gc f).l_u_le T

/-- Negative example canary: if `f x ∉ T`, then `x` is not in the inverse image of `T`. -/
theorem not_mem_inverseImage_of_not_mem (f : X → Y) {T : Set Y} {x : X}
    (h : f x ∉ T) :
    x ∉ inverseImage f T := h

end Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1
