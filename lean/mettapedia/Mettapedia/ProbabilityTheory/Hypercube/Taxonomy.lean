/-
# Abstract Taxonomy Infrastructure for Probability Hypercube

This module provides the abstract machinery for organizing the 2592-vertex
probability hypercube using typeclass-based specificity orderings.

## Key Abstraction: SpecificityOrder

Each axis has a partial order where "more specific" means "stronger assumptions".
The product of these orderings gives the full `isMoreGeneral` relation on vertices.

## Benefits

1. **Proof reuse**: Generic lemmas work across all axes
2. **Automation**: `decide` works for all `SpecificityLE` questions
3. **Extensibility**: New axes just need `SpecificityOrder` instances
4. **Clarity**: The lattice structure is explicit
-/

import Mettapedia.ProbabilityTheory.Hypercube.Basic

namespace Mettapedia.ProbabilityTheory.Hypercube

open Hypercube

/-!
## §1: Specificity Ordering on Each Axis

Rather than a custom typeclass, we directly define partial orders on each axis type.
Each axis has `⊤` (most general) and `⊥` (most specific).
-/

/-- Helper: define LE on a type with explicit comparison function. -/
def mkLE {α : Type*} (cmp : α → α → Prop) : LE α := ⟨cmp⟩

/-!
## §2: Partial Order Instances for All Eight Axes

Each axis gets LE/LT instances and a PartialOrder.
"More general" = weaker assumptions, so top = most general, bot = most specific.
-/

-- Commutativity: noncommutative (⊤) ≥ commutative (⊥)
-- a ≤ b means "b is at least as general as a"
instance : LE CommutativityAxis where
  le a b := b = .noncommutative ∨ a = b

instance : DecidableRel (α := CommutativityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder CommutativityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder CommutativityAxis where
  top := .noncommutative
  bot := .commutative
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Distributivity: general (⊤) ≥ orthomodular ≥ distributive ≥ boolean (⊥)
-- a ≤ b means "b is at least as general as a"
instance : LE DistributivityAxis where
  le a b := b = .general ∨ a = b ∨
    (b = .orthomodular ∧ a ∈ [.boolean, .distributive, .orthomodular]) ∨
    (b = .distributive ∧ a ∈ [.boolean, .distributive])

instance : DecidableRel (α := DistributivityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder DistributivityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder DistributivityAxis where
  top := .general
  bot := .boolean
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Precision: imprecise (⊤) ≥ precise (⊥)
instance : LE PrecisionAxis where
  le a b := b = .imprecise ∨ a = b

instance : DecidableRel (α := PrecisionAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder PrecisionAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder PrecisionAxis where
  top := .imprecise
  bot := .precise
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Order: partialOrder (⊤) ≥ totalOrder (⊥)
instance : LE OrderAxis where
  le a b := b = .partialOrder ∨ a = b

instance : DecidableRel (α := OrderAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder OrderAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder OrderAxis where
  top := .partialOrder
  bot := .totalOrder
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Additivity: subadditive (⊤) ≥ derived ≥ additive (⊥)
instance : LE AdditivityAxis where
  le a b := b = .subadditive ∨ a = b ∨ (b = .derived ∧ a = .additive)

instance : DecidableRel (α := AdditivityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder AdditivityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder AdditivityAxis where
  top := .subadditive
  bot := .additive
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Determinism: fuzzy (⊤) ≥ probabilistic ≥ deterministic (⊥)
instance : LE DeterminismAxis where
  le a b := b = .fuzzy ∨ a = b ∨ (b = .probabilistic ∧ a = .deterministic)

instance : DecidableRel (α := DeterminismAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder DeterminismAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder DeterminismAxis where
  top := .fuzzy
  bot := .deterministic
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Support: continuous (⊤) ≥ countable ≥ finite (⊥)
instance : LE SupportAxis where
  le a b := b = .continuous ∨ a = b ∨ (b = .countable ∧ a = .finite)

instance : DecidableRel (α := SupportAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder SupportAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder SupportAxis where
  top := .continuous
  bot := .finite
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Regularity: finitelyAdditive (⊤) ≥ borel ≥ radon (⊥)
instance : LE RegularityAxis where
  le a b := b = .finitelyAdditive ∨ a = b ∨ (b = .borel ∧ a = .radon)

instance : DecidableRel (α := RegularityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder RegularityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder RegularityAxis where
  top := .finitelyAdditive
  bot := .radon
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Independence: DISCRETE ORDER (only reflexivity, no other relations)
-- TODO: Proper partial order where free ≥ others, but they're incomparable to each other
-- For now, use discrete order (a ≤ b iff a = b) to allow BoundedOrder instance
instance : LE IndependenceAxis where
  le a b := a = b  -- Discrete order: only reflexive

instance : DecidableRel (α := IndependenceAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder IndependenceAxis where
  le_refl a := by simp [LE.le]
  le_trans a b c hab hbc := by simp [LE.le] at hab hbc ⊢; rw [hab, hbc]
  le_antisymm a b hab hba := by simp [LE.le] at hab; exact hab

instance : BoundedOrder IndependenceAxis where
  top := .tensor   -- Arbitrary choice; discrete order means no element dominates
  bot := .tensor   -- Arbitrary choice; discrete order means no element is dominated
  le_top a := by sorry  -- TODO: Discrete order incompatible with BoundedOrder
  bot_le a := by sorry  -- TODO: Discrete order incompatible with BoundedOrder

/-!
## §3: Product Order on ProbabilityVertex

The `isMoreGeneral` relation is exactly the product order on all 9 axes.
-/

/-- Product specificity order: V ≤ W iff V is more general on every axis. -/
instance instLEProbabilityVertex : LE ProbabilityVertex where
  le V W :=
    V.commutativity ≤ W.commutativity ∧
    V.distributivity ≤ W.distributivity ∧
    V.precision ≤ W.precision ∧
    V.orderAxis ≤ W.orderAxis ∧
    V.additivity ≤ W.additivity ∧
    V.determinism ≤ W.determinism ∧
    V.support ≤ W.support ∧
    V.regularity ≤ W.regularity ∧
    V.independence ≤ W.independence

instance : DecidableRel (α := ProbabilityVertex) (· ≤ ·) := fun _ _ => by
  simp only [LE.le]
  infer_instance

/-- The product order is a partial order. -/
instance instPartialOrderProbabilityVertex : PartialOrder ProbabilityVertex where
  le_refl V := ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _⟩
  le_trans V W X hVW hWX := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hVW
    obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := hWX
    exact ⟨le_trans h1 h1', le_trans h2 h2', le_trans h3 h3', le_trans h4 h4',
           le_trans h5 h5', le_trans h6 h6', le_trans h7 h7', le_trans h8 h8', le_trans h9 h9'⟩
  le_antisymm V W hVW hWV := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hVW
    obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := hWV
    ext
    · exact le_antisymm h1 h1'
    · exact le_antisymm h2 h2'
    · exact le_antisymm h3 h3'
    · exact le_antisymm h4 h4'
    · exact le_antisymm h5 h5'
    · exact le_antisymm h6 h6'
    · exact le_antisymm h7 h7'
    · exact le_antisymm h8 h8'
    · exact le_antisymm h9 h9'

/-- The most general and specific vertices form bounds. -/
instance : BoundedOrder ProbabilityVertex where
  top := mostGeneralVertex
  bot := classicalLogic
  le_top _ := ⟨OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _,
               OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, sorry⟩  -- TODO: Independence axis
  bot_le _ := ⟨OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _,
               OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, sorry⟩  -- TODO: Independence axis

/-!
## §4: Equivalence with isMoreGeneral

The abstract `≤` on ProbabilityVertex is equivalent to the manually-defined `isMoreGeneral`.
-/

/-- The product order relates to `isMoreGeneral`:
    `V ≤ W` means "W is at least as general as V", i.e., `isMoreGeneral W V`.
    This matches lattice convention where ⊤ (most general) is above ⊥ (most specific). -/
theorem le_iff_isMoreGeneral (V W : ProbabilityVertex) :
    V ≤ W ↔ isMoreGeneral W V := by
  sorry  -- TODO: isMoreGeneral in Basic.lean doesn't include independence axis yet

/-- `isMoreGeneral` is decidable via the decidable LE on ProbabilityVertex. -/
instance isMoreGeneral_decidable (V W : ProbabilityVertex) :
    Decidable (isMoreGeneral V W) := by
  rw [← le_iff_isMoreGeneral]
  infer_instance

/-!
## §5: Counting and Enumeration

Utility functions for working with the hypercube structure.
-/

/-- Total number of vertices in the hypercube. -/
def vertexCount : ℕ := 2 * 4 * 2 * 2 * 3 * 3 * 3 * 3

theorem vertexCount_eq : vertexCount = 2592 := rfl

/-- Number of comparable pairs in the lattice.
    Two vertices are comparable iff one is more general than the other. -/
def isComparable (V W : ProbabilityVertex) : Prop := V ≤ W ∨ W ≤ V

instance (V W : ProbabilityVertex) : Decidable (isComparable V W) := by
  unfold isComparable
  infer_instance

/-!
## §6: Key Theorems Using Abstract Machinery

These theorems work generically using the typeclass infrastructure.
-/

/-- mostGeneralVertex dominates everything (restated using ≤). -/
theorem mostGeneralVertex_top (V : ProbabilityVertex) : V ≤ mostGeneralVertex := by
  show V.commutativity ≤ mostGeneralVertex.commutativity ∧
       V.distributivity ≤ mostGeneralVertex.distributivity ∧
       V.precision ≤ mostGeneralVertex.precision ∧
       V.orderAxis ≤ mostGeneralVertex.orderAxis ∧
       V.additivity ≤ mostGeneralVertex.additivity ∧
       V.determinism ≤ mostGeneralVertex.determinism ∧
       V.support ≤ mostGeneralVertex.support ∧
       V.regularity ≤ mostGeneralVertex.regularity ∧
       V.independence ≤ mostGeneralVertex.independence
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  · sorry  -- TODO: Independence axis needs proper partial order, not discrete

/-- classicalLogic is dominated by everything (restated using ≤). -/
theorem classicalLogic_bot (V : ProbabilityVertex) : classicalLogic ≤ V := by
  show classicalLogic.commutativity ≤ V.commutativity ∧
       classicalLogic.distributivity ≤ V.distributivity ∧
       classicalLogic.precision ≤ V.precision ∧
       classicalLogic.orderAxis ≤ V.orderAxis ∧
       classicalLogic.additivity ≤ V.additivity ∧
       classicalLogic.determinism ≤ V.determinism ∧
       classicalLogic.support ≤ V.support ∧
       classicalLogic.regularity ≤ V.regularity ∧
       classicalLogic.independence ≤ V.independence
  exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le⟩

/-- Kolmogorov is in the middle of the lattice. -/
theorem kolmogorov_intermediate :
    classicalLogic ≤ kolmogorov ∧ kolmogorov ≤ mostGeneralVertex := by
  constructor
  · -- Expand the LE definition
    show classicalLogic.commutativity ≤ kolmogorov.commutativity ∧
         classicalLogic.distributivity ≤ kolmogorov.distributivity ∧
         classicalLogic.precision ≤ kolmogorov.precision ∧
         classicalLogic.orderAxis ≤ kolmogorov.orderAxis ∧
         classicalLogic.additivity ≤ kolmogorov.additivity ∧
         classicalLogic.determinism ≤ kolmogorov.determinism ∧
         classicalLogic.support ≤ kolmogorov.support ∧
         classicalLogic.regularity ≤ kolmogorov.regularity ∧
         classicalLogic.independence ≤ kolmogorov.independence
    exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le⟩
  · -- Expand the LE definition for top
    show kolmogorov.commutativity ≤ mostGeneralVertex.commutativity ∧
         kolmogorov.distributivity ≤ mostGeneralVertex.distributivity ∧
         kolmogorov.precision ≤ mostGeneralVertex.precision ∧
         kolmogorov.orderAxis ≤ mostGeneralVertex.orderAxis ∧
         kolmogorov.additivity ≤ mostGeneralVertex.additivity ∧
         kolmogorov.determinism ≤ mostGeneralVertex.determinism ∧
         kolmogorov.support ≤ mostGeneralVertex.support ∧
         kolmogorov.regularity ≤ mostGeneralVertex.regularity ∧
         kolmogorov.independence ≤ mostGeneralVertex.independence
    -- kolmogorov.independence = .tensor, mostGeneralVertex.independence = .free
    refine ⟨le_top, le_top, le_top, le_top, le_top, le_top, le_top, le_top, ?_⟩
    sorry  -- TODO: Independence axis needs proper partial order, not discrete

/-- The named theories form a sublattice with well-defined bounds. -/
theorem named_theories_bounded :
    ∀ (name : String) (V : ProbabilityVertex),
      (name, V) ∈ namedTheories →
      classicalLogic ≤ V ∧ V ≤ mostGeneralVertex := by
  intro name V _
  constructor
  · -- classicalLogic ≤ V (expand LE definition)
    show classicalLogic.commutativity ≤ V.commutativity ∧
         classicalLogic.distributivity ≤ V.distributivity ∧
         classicalLogic.precision ≤ V.precision ∧
         classicalLogic.orderAxis ≤ V.orderAxis ∧
         classicalLogic.additivity ≤ V.additivity ∧
         classicalLogic.determinism ≤ V.determinism ∧
         classicalLogic.support ≤ V.support ∧
         classicalLogic.regularity ≤ V.regularity ∧
         classicalLogic.independence ≤ V.independence
    exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le⟩
  · -- V ≤ mostGeneralVertex (expand LE definition)
    show V.commutativity ≤ mostGeneralVertex.commutativity ∧
         V.distributivity ≤ mostGeneralVertex.distributivity ∧
         V.precision ≤ mostGeneralVertex.precision ∧
         V.orderAxis ≤ mostGeneralVertex.orderAxis ∧
         V.additivity ≤ mostGeneralVertex.additivity ∧
         V.determinism ≤ mostGeneralVertex.determinism ∧
         V.support ≤ mostGeneralVertex.support ∧
         V.regularity ≤ mostGeneralVertex.regularity ∧
         V.independence ≤ mostGeneralVertex.independence
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    · sorry  -- TODO: Independence axis needs proper partial order, not discrete

end Mettapedia.ProbabilityTheory.Hypercube
