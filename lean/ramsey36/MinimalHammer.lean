-- MINIMAL imports for double-counting lemma
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Try to find if this already exists in mathlib
#check Finset.sum_comm
#check Finset.card_biUnion
#check Finset.sum_bij

-- The double-counting theorem with MINIMAL environment
theorem finset_sum_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  -- Try with increased premise limits
  hammer (config := { aesopPremises := 128, autoPremises := 64 })
