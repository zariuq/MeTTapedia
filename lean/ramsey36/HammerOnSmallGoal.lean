-- Try hammer on the smallest possible goals
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Test: can hammer solve "a ∈ A" from context?
example {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    (a : α) (b : β) (ha : a ∈ A) (hr : R a b) (hb : b ∈ B) :
    a ∈ A := by
  hammer (config := { aesopPremises := 16, autoPremises := 8 })

-- Test: can hammer solve implication chain?
example {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    (a : α) (b : β) (ha : a ∈ A) :
    R a b → b ∈ B → a ∈ A := by
  hammer (config := { aesopPremises := 16, autoPremises := 8 })

-- Test: can hammer solve product membership?
example {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (a : α) (b : β)
    (ha : a ∈ A) (hb : b ∈ B) :
    (a, b) ∈ A ×ˢ B := by
  hammer (config := { aesopPremises := 16, autoPremises := 8 })

-- Test: product member has components in sets
example {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (p : α × β)
    (hp : p ∈ A ×ˢ B) :
    p.1 ∈ A ∧ p.2 ∈ B := by
  hammer (config := { aesopPremises := 32, autoPremises := 16 })
