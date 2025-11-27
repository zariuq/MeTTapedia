-- Manual proof of double-counting using Finset.card_eq_sum_card_fiberwise
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

-- The double-counting theorem using fiberwise decomposition
theorem double_counting_manual {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  -- Define the edge set
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)

  -- Count E by grouping by first coordinate
  have h1 : E.card = ∑ a ∈ A, (B.filter (R a)).card := by
    -- E is the disjoint union of fibers over A
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)]
    · congr 1
      ext a
      simp [E]
      ext b
      simp [mem_filter, mem_product]
      constructor
      · intro ⟨⟨ha, hb⟩, hr, _⟩; exact ⟨hb, hr⟩
      · intro ⟨hb, hr⟩; refine ⟨⟨?_, hb⟩, hr, rfl⟩; simp [E] at *; exact ⟨⟨rfl, hb⟩, hr⟩
    · intro ⟨a, b⟩ h
      simp [E] at h
      exact h.1.1

  -- Count E by grouping by second coordinate
  have h2 : E.card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
    -- E is the disjoint union of fibers over B
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := B)]
    · congr 1
      ext b
      simp [E, mem_filter, mem_product]
    · intro ⟨a, b⟩ h
      simp [E, mem_filter, mem_product] at h
      exact h.1.2

  -- Combine: both equal E.card
  omega
