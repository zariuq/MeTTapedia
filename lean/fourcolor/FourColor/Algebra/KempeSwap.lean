import Mathlib.Data.ZMod.Basic  
import Mathlib.Data.Finset.Card
import FourColor.Tait

/-!
# Kempe Swap Algebra for F₂²

This module provides the algebraic foundation for Kempe chain switches.
The key insight: swapping α ↔ β preserves vertex sums when the swap set
has even incidence at each vertex.

Based on the even-incidence swap principle from GPT-5 guidance.
-/

namespace FourColor

/-- Scalar field F₂. -/
abbrev F2 := ZMod 2

namespace Color

/-- Swap two distinguished colors, leaving others unchanged. -/
def swap (α β x : Color) : Color :=
  if x = α then β else if x = β then α else x

/-- The two-element set `{α,β}`. -/
def twoColor (α β : Color) : Set Color := {x | x = α ∨ x = β}

/-- Elementary delta for a swap: add α+β exactly on αβ. -/
def delta (α β x : Color) : Color :=
  if x ∈ twoColor α β then α + β else (0, 0)

@[simp] lemma swap_eq_add_delta (α β x : Color) :
    swap α β x = x + delta α β x := by
  unfold swap delta twoColor
  by_cases hα : x = α
  · subst hα; simp
    -- β = α + (α + β) in F₂²
    ext <;> ring_nf <;> rfl
  · by_cases hβ : x = β
    · subst hβ; simp [hα]
      -- α = β + (α + β) in F₂²
      ext <;> ring_nf <;> rfl
    · simp [hα, hβ]; rfl

end Color

/-- In F₂², summing a value an even number of times gives zero. -/
lemma nsmul_even_eq_zero {α : Color} {n : ℕ} (h : Even n) :
    n • α = (0, 0) := by
  rcases h with ⟨k, rfl⟩
  simp [two_nsmul]
  ext <;> simp

/-- Sum of constant over a finset equals card • constant. -/
lemma sum_const {E : Type*} [Fintype E] [DecidableEq E] 
    (S : Finset E) (c : Color) :
    ∑ _e ∈ S, c = S.card • c := by
  induction S using Finset.induction with
  | empty => simp
  | insert e S he ih =>
    rw [Finset.sum_insert he, ih, Finset.card_insert_of_not_mem he]
    simp [succ_nsmul]

/-- Sum at a vertex is preserved if the swap set has even αβ-incidence. -/
lemma swap_preserves_vertex_sum
    {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V]
    (incident : V → Finset E)
    (x : E → Color) (C : Finset E) (α β : Color)
    (even_at : ∀ v : V, Even ((C ∩ incident v).filter (fun e => x e = α ∨ x e = β)).card) :
  ∀ v, ∑ e ∈ incident v, x e
      = ∑ e ∈ incident v, (if e ∈ C then Color.swap α β (x e) else x e) := by
  intro v
  let S := (C ∩ incident v).filter (fun e => x e = α ∨ x e = β)

  -- Each swapped term equals original + conditional delta
  have h_swap : ∀ e, (if e ∈ C then Color.swap α β (x e) else x e)
                   = x e + (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0)) := by
    intro e
    by_cases he : e ∈ C
    · simp [he, Color.swap_eq_add_delta, Color.delta, Color.twoColor]
    · simp [he]

  symm
  calc
    ∑ e ∈ incident v, x e
      = (∑ e ∈ incident v, x e) + (0, 0) := by
          simp [Bits.zero_add]
    _ = (∑ e ∈ incident v, x e) + S.card • (α + β) := by
          rw [← nsmul_even_eq_zero (even_at v)]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ S, (α + β)) := by
          rw [← sum_const]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ incident v, (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          congr 1
          -- Sum over S = sum over incident v with conditional
          rw [← Finset.sum_filter]
          congr 1
          simp [S]
    _ = ∑ e ∈ incident v, (x e + (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          exact Finset.sum_add_distrib.symm
    _ = ∑ e ∈ incident v, (if e ∈ C then Color.swap α β (x e) else x e) := by
          congr 1; ext e; exact (h_swap e).symm

end FourColor
