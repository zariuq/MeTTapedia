import Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1.PowerSetAdjunction
import Mathlib.Data.Set.Lattice

namespace Mettapedia.AutoBooks.Codex.ModalHoTT.Chapter4

/-!
# Modal HoTT, Chapter 4: Modalities as Monads

This file formalizes the set-level adjoint-triple story from the opening of
Corfield's Chapter 4. Given a map `f : X → Y`, properties of `Y` pull back to
properties of `X`; this pullback sits between existential and universal image
operators. Composing these adjoints yields possibility-style and
necessity-style operators on properties of `X`.
-/

open Set
open Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1

variable {X Y : Type*}

/-- Universal image along a function, right adjoint to inverse image on powersets. -/
def universalImage (f : X → Y) : Set X → Set Y :=
  fun S => {y | ∀ ⦃x⦄, f x = y → x ∈ S}

theorem universalImage_monotone (f : X → Y) : Monotone (universalImage f) := by
  intro A B hAB y hy x hx
  exact hAB (hy hx)

/-- Pullback along `f` is left adjoint to universal image along `f`. -/
theorem inverseImage_universalImage_gc (f : X → Y) :
    GaloisConnection (inverseImage f) (universalImage f) := by
  intro A S
  constructor
  · intro h y hy x hx
    exact h (by simpa [inverseImage, hx] using hy)
  · intro h x hx
    exact h hx rfl

/-- The possibility-style operator induced by variation along `f`. -/
def possibleAlong (f : X → Y) : Set X → Set X :=
  fun S => inverseImage f (directImage f S)

/-- The necessity-style operator induced by variation along `f`. -/
def necessaryAlong (f : X → Y) : Set X → Set X :=
  fun S => inverseImage f (universalImage f S)

theorem possibleAlong_monotone (f : X → Y) : Monotone (possibleAlong f) := by
  intro A B hAB
  exact (inverseImage_monotone f) ((directImage_monotone f) hAB)

theorem necessaryAlong_monotone (f : X → Y) : Monotone (necessaryAlong f) := by
  intro A B hAB
  exact (inverseImage_monotone f) ((universalImage_monotone f) hAB)

/-- Membership in the induced possibility modality means sharing a fibre with some witness. -/
theorem mem_possibleAlong_iff (f : X → Y) {S : Set X} {x : X} :
    x ∈ possibleAlong f S ↔ ∃ x', x' ∈ S ∧ f x' = f x := by
  constructor
  · intro hx
    change f x ∈ directImage f S at hx
    rcases hx with ⟨x', hx', hfx⟩
    exact ⟨x', hx', hfx⟩
  · rintro ⟨x', hx', hfx⟩
    change f x ∈ directImage f S
    exact ⟨x', hx', hfx⟩

/-- Membership in the induced necessity modality means the entire fibre lies in the property. -/
theorem mem_necessaryAlong_iff (f : X → Y) {S : Set X} {x : X} :
    x ∈ necessaryAlong f S ↔ ∀ x', f x' = f x → x' ∈ S := by
  rfl

/-- `S ⊆ ♢_f S`: an actual witness is a possible witness. -/
theorem subset_possibleAlong (f : X → Y) (S : Set X) :
    S ⊆ possibleAlong f S :=
  (directImage_inverseImage_gc f).le_u_l S

/-- `□_f S ⊆ S`: necessity along `f` is stronger than actuality. -/
theorem necessaryAlong_subset (f : X → Y) (S : Set X) :
    necessaryAlong f S ⊆ S :=
  (inverseImage_universalImage_gc f).l_u_le S

theorem possibleAlong_possibleAlong_subset (f : X → Y) (S : Set X) :
    possibleAlong f (possibleAlong f S) ⊆ possibleAlong f S := by
  change inverseImage f (directImage f (inverseImage f (directImage f S))) ⊆
      inverseImage f (directImage f S)
  exact (inverseImage_monotone f) (directImage_inverseImage_subset f (directImage f S))

theorem subset_possibleAlong_possibleAlong (f : X → Y) (S : Set X) :
    possibleAlong f S ⊆ possibleAlong f (possibleAlong f S) :=
  (possibleAlong_monotone f) (subset_possibleAlong f S)

/-- `♢_f` is idempotent, matching the closure-style behavior discussed in the text. -/
theorem possibleAlong_idempotent (f : X → Y) (S : Set X) :
    possibleAlong f (possibleAlong f S) = possibleAlong f S := by
  ext x
  constructor
  · intro hx
    exact possibleAlong_possibleAlong_subset f S hx
  · intro hx
    exact subset_possibleAlong_possibleAlong f S hx

theorem necessaryAlong_necessaryAlong_subset (f : X → Y) (S : Set X) :
    necessaryAlong f (necessaryAlong f S) ⊆ necessaryAlong f S :=
  (necessaryAlong_monotone f) (necessaryAlong_subset f S)

theorem subset_necessaryAlong_necessaryAlong (f : X → Y) (S : Set X) :
    necessaryAlong f S ⊆ necessaryAlong f (necessaryAlong f S) := by
  change inverseImage f (universalImage f S) ⊆
      inverseImage f (universalImage f (inverseImage f (universalImage f S)))
  exact (inverseImage_monotone f)
    ((inverseImage_universalImage_gc f).le_u_l (universalImage f S))

/-- `□_f` is idempotent, matching the interior-style dual behavior. -/
theorem necessaryAlong_idempotent (f : X → Y) (S : Set X) :
    necessaryAlong f (necessaryAlong f S) = necessaryAlong f S := by
  ext x
  constructor
  · intro hx
    exact necessaryAlong_necessaryAlong_subset f S hx
  · intro hx
    exact subset_necessaryAlong_necessaryAlong f S hx

end Mettapedia.AutoBooks.Codex.ModalHoTT.Chapter4
