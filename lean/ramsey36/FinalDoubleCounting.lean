-- FINAL double-counting proof: tactics + hammer on small pieces
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

-- The complete theorem
theorem double_counting_final {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)

  -- Both sides equal E.card
  suffices h_lhs : (∑ a ∈ A, (B.filter (R a)).card) = E.card by
    suffices h_rhs : (∑ b ∈ B, (A.filter (fun a => R a b)).card) = E.card by
      omega
    -- Prove RHS = E.card (symmetric to LHS, use Prod.snd)
    conv_lhs => arg 2; ext b; rw [show (A.filter (fun a => R a b)).card =
      (E.filter (fun p => p.2 = b)).card by
        classical
        -- Bijection via (-, b)
        have : (A.filter (fun a => R a b)) = (E.filter (fun p => p.2 = b)).image Prod.fst := by
          ext a
          simp only [E, mem_filter, mem_product, mem_image]
          constructor
          · intro ⟨ha, hr⟩
            use (a, b)
            simp_all only [and_self]
          · intro ⟨⟨a', b'⟩, ⟨⟨⟨ha', hb'⟩, hr'⟩, heq⟩, hfst⟩
            simp only at heq hfst
            subst heq hfst
            exact ⟨ha', hr'⟩
        rw [this, card_image_of_injective]
        intro ⟨a1, b1⟩ ⟨a2, b2⟩
        simp only [Prod.fst.injEq]
        intro heq
        simp only [E, mem_filter, mem_product] at *
        ext <;> simp_all only [Prod.mk.eta])
    -- Apply card_eq_sum_card_fiberwise for Prod.snd
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := B)]
    · simp only [mem_filter]
    · intros p hp
      simp only [E, mem_filter, mem_product] at hp
      exact hp.1.2

  -- Prove LHS = E.card using card_eq_sum_card_fiberwise
  conv_lhs => arg 2; ext a; rw [show (B.filter (R a)).card =
    (E.filter (fun p => p.1 = a)).card by
      classical
      -- Bijection via (a, -)
      have : (B.filter (R a)) = (E.filter (fun p => p.1 = a)).image Prod.snd := by
        ext b
        simp only [E, mem_filter, mem_product, mem_image]
        constructor
        · intro ⟨hb, hr⟩
          use (a, b)
          simp_all only [and_self]
        · intro ⟨⟨a', b'⟩, ⟨⟨⟨ha', hb'⟩, hr'⟩, heq⟩, hsnd⟩
          simp only at heq hsnd
          subst heq hsnd
          exact ⟨hb', hr'⟩
      rw [this, card_image_of_injective]
      intro ⟨a1, b1⟩ ⟨a2, b2⟩
      simp only [Prod.snd.injEq]
      intro heq
      simp only [E, mem_filter, mem_product] at *
      ext <;> simp_all only [Prod.mk.eta]]

  -- Apply card_eq_sum_card_fiberwise for Prod.fst
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)]
  · simp only [mem_filter]
  · intros p hp
    simp only [E, mem_filter, mem_product] at hp
    exact hp.1.1
