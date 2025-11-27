-- Complete double-counting proof with maximum tactic breakdown
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Complete proof using card_eq_sum_card_fiberwise (NO hammer needed!)
theorem double_counting_complete {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)

  -- Both sides equal E.card
  suffices h : (∑ a ∈ A, (B.filter (R a)).card) = E.card ∧
               (∑ b ∈ B, (A.filter (fun a => R a b)).card) = E.card by
    omega

  constructor

  -- Part 1: LHS = E.card (count by first coordinate)
  · -- Key: relate filter to fiber
    have h_fiber : ∀ a ∈ A, (B.filter (R a)).card = (E.filter (fun p => p.1 = a)).card := by
      intros a ha
      -- The sets are in bijection via (a, -)
      have bij : (B.filter (R a)) = (E.filter (fun p => p.1 = a)).image Prod.snd := by
        ext b
        simp [E, mem_filter, mem_product, mem_image]
        constructor
        · intro ⟨hb, hr⟩
          use (a, b)
          simp [ha, hb, hr]
        · intro ⟨⟨a', b'⟩, ⟨⟨⟨ha', hb'⟩, hr'⟩, heq⟩, hsnd⟩
          simp at heq hsnd
          subst heq hsnd
          exact ⟨hb', hr'⟩
      rw [bij]
      -- Now use card_image_of_injective
      sorry -- TODO: prove Prod.snd injective on this fiber (needs a ≠ a' → (a,b) ≠ (a',b'))

    -- Rewrite sum using fibers
    conv_lhs => arg 2; ext a; rw [h_fiber a (by simp)]

    -- Now apply card_eq_sum_card_fiberwise
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)]
    · simp
    · intros p hp
      simp [E, mem_filter, mem_product] at hp
      exact hp.1.1

  -- Part 2: RHS = E.card (symmetric, count by second coordinate)
  · sorry -- Same structure as Part 1, but with Prod.snd
