import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic

open Finset BigOperators

-- Search for the double-counting lemma in mathlib
-- This is also known as "handshake lemma" or "Fubini for finite sums"

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

-- Check if any of these exist
#check Finset.sum_comm
#check Finset.card_sum
#check Finset.sum_card_filter
#check Finset.card_bipartite
#check Finset.card_product
#check Finset.sum_bij

-- The goal: prove this exists in mathlib already
theorem double_count_edges
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    A.sum (fun a => (B.filter (R a)).card) =
    B.sum (fun b => (A.filter (fun a => R a b)).card) := by
  sorry  -- Does mathlib have this?
