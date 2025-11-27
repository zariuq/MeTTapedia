-- Proof using Finset.sum_fiberwise
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

-- sum_fiberwise says: ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i
-- This is exactly what we need for double-counting!

theorem double_counting_fiberwise {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  -- Define edge set
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)

  -- Count E by first coordinate using sum_fiberwise
  have h1 : E.card = ∑ a, (E.filter (fun p => p.1 = a)).card := by
    rw [← sum_fiberwise E Prod.fst (fun _ => 1)]
    simp [card_eq_sum_ones]

  -- Simplify: filter by first coordinate
  have h1' : ∑ a, (E.filter (fun p => p.1 = a)).card = ∑ a ∈ A, (B.filter (R a)).card := by
    sorry

  -- Count E by second coordinate using sum_fiberwise
  have h2 : E.card = ∑ b, (E.filter (fun p => p.2 = b)).card := by
    rw [← sum_fiberwise E Prod.snd (fun _ => 1)]
    simp [card_eq_sum_ones]

  -- Simplify: filter by second coordinate
  have h2' : ∑ b, (E.filter (fun p => p.2 = b)).card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
    sorry

  omega
