/-
# Boolean to Heyting Bridge: Categorical Semantics

## Overview

This file formalizes the categorical relationship between Boolean events and
Heyting evidence in PLN. The key insight:

- Boolean σ-algebras are where EVENTS live (ground truth)
- Heyting algebras are where EVIDENCE lives (epistemic states)
- There's a forgetful functor: Boolean → Heyting (any Boolean is a Heyting)
- And a "sufficient statistic" map: Events × Observations → BinaryEvidence

## Connection to PLN

The two-level architecture:
1. Event level: Boolean σ-algebra (Ω, 𝓕, P) with standard probability
2. BinaryEvidence level: Heyting lattice of BinaryEvidence (n⁺, n⁻) values

De Finetti's theorem provides the bridge: exchangeable observations
(from Boolean events) collapse to counts (BinaryEvidence).

## References

- MacLane, "Categories for the Working Mathematician" (1971)
- nLab: Boolean algebra, Heyting algebra, forgetful functor
-/

import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic

namespace Mettapedia.Logic.BooleanHeytingBridge

open CategoryTheory

/-! ## Categories of Lattices

We define categories where:
- Objects are types with lattice structure
- Morphisms are lattice homomorphisms
-/

/-- A morphism of Heyting algebras preserves ⊓, ⊔, ⊥, ⊤, and ⇨ -/
structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] where
  toFun : α → β
  map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_sup : ∀ a b, toFun (a ⊔ b) = toFun a ⊔ toFun b
  map_bot : toFun ⊥ = ⊥
  map_top : toFun ⊤ = ⊤
  map_himp : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

namespace HeytingHom

variable {α β γ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]

instance : CoeFun (HeytingHom α β) (fun _ => α → β) := ⟨HeytingHom.toFun⟩

/-- The identity Heyting homomorphism -/
def id : HeytingHom α α where
  toFun := _root_.id
  map_inf _ _ := rfl
  map_sup _ _ := rfl
  map_bot := rfl
  map_top := rfl
  map_himp _ _ := rfl

/-- Composition of Heyting homomorphisms -/
def comp (g : HeytingHom β γ) (f : HeytingHom α β) : HeytingHom α γ where
  toFun := g.toFun ∘ f.toFun
  map_inf a b := by simp [f.map_inf, g.map_inf]
  map_sup a b := by simp [f.map_sup, g.map_sup]
  map_bot := by simp [f.map_bot, g.map_bot]
  map_top := by simp [f.map_top, g.map_top]
  map_himp a b := by simp [f.map_himp, g.map_himp]

end HeytingHom

/-- A morphism of Boolean algebras preserves ⊓, ⊔, ⊥, ⊤, and ᶜ -/
structure BooleanHom (α β : Type*) [BooleanAlgebra α] [BooleanAlgebra β] where
  toFun : α → β
  map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_sup : ∀ a b, toFun (a ⊔ b) = toFun a ⊔ toFun b
  map_bot : toFun ⊥ = ⊥
  map_top : toFun ⊤ = ⊤
  map_compl : ∀ a, toFun aᶜ = (toFun a)ᶜ

namespace BooleanHom

variable {α β γ : Type*} [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

instance : CoeFun (BooleanHom α β) (fun _ => α → β) := ⟨BooleanHom.toFun⟩

/-- The identity Boolean homomorphism -/
def id : BooleanHom α α where
  toFun := _root_.id
  map_inf _ _ := rfl
  map_sup _ _ := rfl
  map_bot := rfl
  map_top := rfl
  map_compl _ := rfl

/-- Composition of Boolean homomorphisms -/
def comp (g : BooleanHom β γ) (f : BooleanHom α β) : BooleanHom α γ where
  toFun := g.toFun ∘ f.toFun
  map_inf a b := by simp [f.map_inf, g.map_inf]
  map_sup a b := by simp [f.map_sup, g.map_sup]
  map_bot := by simp [f.map_bot, g.map_bot]
  map_top := by simp [f.map_top, g.map_top]
  map_compl a := by simp [f.map_compl, g.map_compl]

/-- Every Boolean homomorphism induces a Heyting homomorphism -/
def toHeytingHom (f : BooleanHom α β) : HeytingHom α β where
  toFun := f.toFun
  map_inf := f.map_inf
  map_sup := f.map_sup
  map_bot := f.map_bot
  map_top := f.map_top
  map_himp a b := by
    -- In Boolean algebra: a ⇨ b = aᶜ ⊔ b
    simp only [himp_eq, f.map_compl, f.map_sup]

end BooleanHom

/-! ## The Forgetful Functor: Boolean → Heyting

Every Boolean algebra is a Heyting algebra (with aᶜ = a ⇨ ⊥).
This defines a forgetful functor from the category of Boolean algebras
to the category of Heyting algebras.
-/

/-- Any Boolean algebra is a Heyting algebra -/
example {α : Type*} [BooleanAlgebra α] : HeytingAlgebra α := inferInstance

/-- Boolean homomorphisms become Heyting homomorphisms
    (this is the action of the forgetful functor on morphisms) -/
def forget_preserves_morphisms {α β : Type*}
    [BooleanAlgebra α] [BooleanAlgebra β]
    (f : BooleanHom α β) : HeytingHom α β :=
  f.toHeytingHom

/-! ## BinaryEvidence as Collapse of Boolean Events

The key bridge in PLN: Boolean events (from σ-algebra) collapse to
BinaryEvidence counts via sufficient statistics.

For exchangeable Boolean observations X₁, X₂, ..., Xₙ:
- Each Xᵢ ∈ {True, False} (Boolean)
- Sufficient statistic: (count True, count False) = (n⁺, n⁻)
- This is the BinaryEvidence value!

The BinaryEvidence lattice is Heyting (not Boolean), so we have:
Boolean events → (sufficient statistic) → Heyting evidence
-/

/-- Counts of positive and negative observations -/
@[ext]
structure ObservationCounts where
  positive : ℕ
  negative : ℕ
  deriving DecidableEq

namespace ObservationCounts

/-- Zero counts -/
def zero : ObservationCounts := ⟨0, 0⟩

/-- Add a positive observation -/
def addPositive (c : ObservationCounts) : ObservationCounts :=
  ⟨c.positive + 1, c.negative⟩

/-- Add a negative observation -/
def addNegative (c : ObservationCounts) : ObservationCounts :=
  ⟨c.positive, c.negative + 1⟩

/-- Combine counts from two independent sources -/
def combine (c₁ c₂ : ObservationCounts) : ObservationCounts :=
  ⟨c₁.positive + c₂.positive, c₁.negative + c₂.negative⟩

instance : Add ObservationCounts := ⟨combine⟩

/-- Total observations -/
def total (c : ObservationCounts) : ℕ := c.positive + c.negative

/-- The order: more information (both components larger) -/
instance : LE ObservationCounts where
  le c₁ c₂ := c₁.positive ≤ c₂.positive ∧ c₁.negative ≤ c₂.negative

/-- Counts form a partial order with incomparable elements -/
instance : PartialOrder ObservationCounts where
  le_refl c := ⟨le_refl _, le_refl _⟩
  le_trans c₁ c₂ c₃ h₁₂ h₂₃ := ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩
  le_antisymm c₁ c₂ h₁₂ h₂₁ := by
    ext
    · exact le_antisymm h₁₂.1 h₂₁.1
    · exact le_antisymm h₁₂.2 h₂₁.2

/-- BinaryEvidence (3, 2) and (2, 3) are incomparable -/
theorem counts_incomparable :
    let c₁ : ObservationCounts := ⟨3, 2⟩
    let c₂ : ObservationCounts := ⟨2, 3⟩
    ¬(c₁ ≤ c₂) ∧ ¬(c₂ ≤ c₁) := by
  constructor
  · intro h
    have : (3 : ℕ) ≤ 2 := h.1
    omega
  · intro h
    have : (3 : ℕ) ≤ 2 := h.2
    omega

/-- Counts are NOT totally ordered -/
theorem counts_not_total : ¬∀ c₁ c₂ : ObservationCounts, c₁ ≤ c₂ ∨ c₂ ≤ c₁ := by
  push_neg
  exact ⟨⟨3, 2⟩, ⟨2, 3⟩, counts_incomparable.1, counts_incomparable.2⟩

end ObservationCounts

/-! ## The Sufficient Statistic Map

Given a sequence of Boolean observations, compute the counts.
This is the bridge from Boolean events to Heyting evidence.
-/

/-- Compute counts from a list of Boolean observations (alternative definition) -/
def countsOfList' (obs : List Bool) : ObservationCounts :=
  ⟨obs.count true, obs.count false⟩

/-- The step function for computing counts -/
def countStep (c : ObservationCounts) (b : Bool) : ObservationCounts :=
  if b then c.addPositive else c.addNegative

/-- Original foldl definition -/
def countsOfList (obs : List Bool) : ObservationCounts :=
  obs.foldl countStep ObservationCounts.zero

/-- Helper: foldl with offset -/
private theorem foldl_aux (obs : List Bool) (p n : ℕ) :
    obs.foldl countStep ⟨p, n⟩ = ⟨p + obs.count true, n + obs.count false⟩ := by
  induction obs generalizing p n with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.count_cons]
    cases b
    · -- b = false: (false == true) is false, (false == false) is true
      simp only [countStep, Bool.false_eq_true, ↓reduceIte, ObservationCounts.addNegative]
      rw [ih]
      simp only [ObservationCounts.mk.injEq, beq_iff_eq, Bool.false_eq_true,
                 ite_false, add_zero, ite_true]
      exact ⟨trivial, by omega⟩
    · -- b = true: (true == true) is true, (true == false) is false
      simp only [countStep, ↓reduceIte, ObservationCounts.addPositive]
      rw [ih]
      simp only [ObservationCounts.mk.injEq, beq_iff_eq, Bool.true_eq_false,
                 ite_false, add_zero, ite_true]
      exact ⟨by omega, trivial⟩

/-- countsOfList equals countsOfList' -/
theorem countsOfList_eq_countsOfList' (obs : List Bool) :
    countsOfList obs = countsOfList' obs := by
  simp only [countsOfList, countsOfList', ObservationCounts.zero]
  rw [foldl_aux]
  simp

/-- The counts depend only on the number of True/False, not order (exchangeability) -/
theorem countsOfList_permutation (l₁ l₂ : List Bool) (h : l₁.Perm l₂) :
    countsOfList l₁ = countsOfList l₂ := by
  simp only [countsOfList_eq_countsOfList', countsOfList']
  ext
  · exact h.count_eq true
  · exact h.count_eq false

/-! ## Summary: The Two-Level Architecture

1. **Boolean level** (Events):
   - Objects: Boolean algebras (σ-algebras of events)
   - Morphisms: Boolean homomorphisms
   - This is where probability rules are derived (K&S product/sum rules)

2. **Heyting level** (BinaryEvidence):
   - Objects: Heyting algebras (BinaryEvidence lattices)
   - Morphisms: Heyting homomorphisms
   - This is where epistemic states live

3. **The Bridge** (Sufficient Statistics):
   - Boolean observations → counts (n⁺, n⁻)
   - Exchangeability → order doesn't matter (de Finetti)
   - BinaryEvidence is the sufficient statistic for Beta posterior

4. **The Forgetful Functor**:
   - Boolean algebras embed into Heyting algebras
   - Every Boolean hom becomes a Heyting hom
   - This shows Boolean is a special case of Heyting

5. **BinaryEvidence is MORE GENERAL**:
   - BinaryEvidence has incomparable elements (Boolean doesn't)
   - The 2D structure (n⁺, n⁻) captures more than 1D probability
   - This is WHY PLN uses BinaryEvidence, not just probabilities
-/

end Mettapedia.Logic.BooleanHeytingBridge
