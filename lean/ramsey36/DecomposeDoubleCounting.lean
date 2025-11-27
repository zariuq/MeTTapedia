-- Decompose the double-counting lemma into sub-goals for hammer
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Step 1: Define the product space of pairs
lemma step1_product_def {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    ∃ (E : Finset (α × β)), E = (A ×ˢ B).filter (fun p => R p.1 p.2) := by
  use (A ×ˢ B).filter (fun p => R p.1 p.2)

-- Step 2: Count from first coordinate
lemma step2_count_from_first {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    E.card = ∑ a ∈ A, (B.filter (R a)).card := by
  hammer (config := { aesopPremises := 64, autoPremises := 32 })

-- Step 3: Count from second coordinate
lemma step3_count_from_second {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    E.card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
  hammer (config := { aesopPremises := 64, autoPremises := 32 })

-- Step 4: Combine to get the double-counting equality
theorem double_counting_decomposed {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  have h1 := step2_count_from_first A B R
  have h2 := step3_count_from_second A B R
  omega  -- Should follow from h1 = h2 via transitivity
