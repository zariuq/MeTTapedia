/-
Quick Hammer Test - Minimal dependencies, tests patterns from FourColor project
-/
import Hammer
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

open Finset BigOperators

variable {α : Type*} [DecidableEq α]

/-! ## Pattern 1: Finset Filter Properties (Used in face counting) -/

-- Filter singleton when unique
example (S : Finset α) (a : α) (ha : a ∈ S)
    (h_unique : ∀ b ∈ S, b = a) :
    S = {a} := by
  hammer

-- Filter preserves membership
example (S : Finset α) (P : α → Prop) [DecidablePred P] (a : α)
    (ha : a ∈ S) (hP : P a) :
    a ∈ S.filter P := by
  hammer

-- Card of filter bounded by card of set
example (S : Finset α) (P : α → Prop) [DecidablePred P] :
    (S.filter P).card ≤ S.card := by
  hammer

/-! ## Pattern 2: Erase Properties (Used in leaf peeling) -/

-- Card of erase
example (S : Finset α) (a : α) (ha : a ∈ S) :
    (S.erase a).card = S.card - 1 := by
  hammer

-- Erase is subset
example (S : Finset α) (a : α) :
    S.erase a ⊆ S := by
  hammer

-- Element not in erased set
example (S : Finset α) (a : α) :
    a ∉ S.erase a := by
  hammer

-- Erase preserves other elements
example (S : Finset α) (a b : α) (hne : a ≠ b) (hb : b ∈ S) :
    b ∈ S.erase a := by
  hammer

/-! ## Pattern 3: Intersection Properties (Used in dual adjacency) -/

-- Shared element means nonempty intersection
example (s t : Finset α) (a : α) (hs : a ∈ s) (ht : a ∈ t) :
    (s ∩ t).Nonempty := by
  hammer

-- Element in both means in intersection
example (s t : Finset α) (a : α) (hs : a ∈ s) (ht : a ∈ t) :
    a ∈ s ∩ t := by
  hammer

/-! ## Pattern 4: Sum Properties (Used in toggleSum, zeroBoundary) -/

-- Sum over singleton
example (a : α) (f : α → ℕ) :
    ∑ x ∈ ({a} : Finset α), f x = f a := by
  hammer

-- Sum over empty set
example (f : α → ℕ) :
    ∑ x ∈ (∅ : Finset α), f x = 0 := by
  hammer

-- Sum of constant
example (S : Finset α) (c : ℕ) :
    ∑ _ ∈ S, c = S.card * c := by
  hammer

/-! ## Pattern 5: ZMod 2 Properties (Used in Color = ZMod 2 × ZMod 2) -/

-- ZMod 2 has characteristic 2
example : (1 : ZMod 2) + 1 = 0 := by
  hammer

-- ZMod 2 is self-inverse
example (x : ZMod 2) : x + x = 0 := by
  hammer

/-! ## Pattern 6: Subset Transitivity (Used in face containment) -/

example (s t u : Finset α) (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u := by
  hammer

example (s t : Finset α) (h : s ⊆ t) : s.card ≤ t.card := by
  hammer

/-! ## Pattern 7: Fintype Uniqueness (From InductiveFourColor sorry) -/

-- If Fintype.card = 1, then any two elements are equal
example {V : Type*} [Fintype V] (h : Fintype.card V = 1) (u v : V) : u = v := by
  hammer

/-! ## Summary -/

#check "All quick hammer tests passed!"
