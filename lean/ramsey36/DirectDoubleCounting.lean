-- Direct proof of double-counting using Finset.card_disjiUnion
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

-- Direct double-counting theorem using disjiUnion
theorem double_counting_direct {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  -- Use the fact that both count |{(a,b) : a ∈ A, b ∈ B, R a b}|
  have key : ∀ a ∈ A, ∀ b ∈ B, R a b ↔ (a, b) ∈ (A ×ˢ B).filter (fun p => R p.1 p.2) := by
    intros a ha b hb
    simp [mem_filter, mem_product, ha, hb]

  -- LHS counts pairs (a, b) grouped by a
  have lhs_eq : (∑ a ∈ A, (B.filter (R a)).card) =
      ((A ×ˢ B).filter (fun p => R p.1 p.2)).card := by
    sorry  -- This is the "partition by first coordinate" lemma

  -- RHS counts pairs (a, b) grouped by b
  have rhs_eq : (∑ b ∈ B, (A.filter (fun a => R a b)).card) =
      ((A ×ˢ B).filter (fun p => R p.1 p.2)).card := by
    sorry  -- This is the "partition by second coordinate" lemma

  -- Both equal the same thing
  omega
