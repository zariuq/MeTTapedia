/-
# Abstract Taxonomy Infrastructure for Probability Hypercube

This module provides the abstract machinery for organizing the 373248-vertex
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
import Mettapedia.ProbabilityTheory.Hypercube.DensityAxisStory

namespace Mettapedia.ProbabilityTheory.Hypercube

open Hypercube

/-!
## §1: Specificity Ordering on Each Axis

Rather than a custom typeclass, we directly define partial orders on each axis type.
Each axis has `⊤` (most general) and `⊥` (most specific).
-/

/-- Helper: define LE on a type with explicit comparison function. -/
@[instance_reducible] def mkLE {α : Type*} (cmp : α → α → Prop) : LE α := ⟨cmp⟩

/-!
## §2: Partial Order Instances for All Thirteen Axes

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

-- Density: nondense (⊤) ≥ dense (⊥)
instance : LE DensityAxis where
  le a b := b = .nondense ∨ a = b

instance : DecidableRel (α := DensityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder DensityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder DensityAxis where
  top := .nondense
  bot := .dense
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Completeness: incomplete (⊤) ≥ conditionallyComplete (⊥)
instance : LE CompletenessAxis where
  le a b := b = .incomplete ∨ a = b

instance : DecidableRel (α := CompletenessAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder CompletenessAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder CompletenessAxis where
  top := .incomplete
  bot := .conditionallyComplete
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

-- Separation: none (⊤) ≥ ksSeparation ≥ ksSeparationStrict (⊥)
instance : LE SeparationAxis where
  le a b := b = .none ∨ a = b ∨ (b = .ksSeparation ∧ a = .ksSeparationStrict)

instance : DecidableRel (α := SeparationAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder SeparationAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder SeparationAxis where
  top := .none
  bot := .ksSeparationStrict
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

-- Invertibility: semigroup (⊤) ≥ monoid ≥ group (⊥)
instance : LE InvertibilityAxis where
  le a b := b = .semigroup ∨ a = b ∨ (b = .monoid ∧ a = .group)

instance : DecidableRel (α := InvertibilityAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder InvertibilityAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder InvertibilityAxis where
  top := .semigroup
  bot := .group
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

-- Independence: noncommutative independences are not totally ordered.
--
-- We use a simple bounded partial order with:
-- - `⊤ = free` (treated as “most general / least constrained”)
-- - `⊥ = tensor` (treated as “most specific / most classical”)
-- - `boolean` and `monotone` incomparable except via ⊤/⊥
instance : LE IndependenceAxis where
  le a b := b = .free ∨ a = .tensor ∨ a = b

instance : DecidableRel (α := IndependenceAxis) (· ≤ ·) := fun a b => by
  simp only [LE.le]; infer_instance

instance : PartialOrder IndependenceAxis where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]
  le_antisymm a b := by cases a <;> cases b <;> simp [LE.le]

instance : BoundedOrder IndependenceAxis where
  top := .free
  bot := .tensor
  le_top a := by cases a <;> simp [LE.le]
  bot_le a := by cases a <;> simp [LE.le]

/-!
## §3: Product Order on ProbabilityVertex

  The `isMoreGeneral` relation is exactly the product order on all 13 axes.
-/

/-- **Strength / specificity order** on vertices.

We take `⊥ = classicalLogic` (maximally constrained / strongest) and `⊤ = mostGeneralVertex`
(maximally permissive / weakest). Thus:

- `V ≤ W` means **`V` is at least as strong/specific as `W`** (i.e. `W` is at least as general as `V`).
- This matches the categorical “weakness” convention from Goertzel’s Weakness notes:
  one typically regards arrows as going from weaker contexts to stronger ones, i.e. uses the
  opposite category of this poset when treating `≤` as morphisms.
-/
instance instLEProbabilityVertex : LE ProbabilityVertex where
  le V W :=
    V.commutativity ≤ W.commutativity ∧
    V.distributivity ≤ W.distributivity ∧
    V.precision ≤ W.precision ∧
    V.orderAxis ≤ W.orderAxis ∧
    V.density ≤ W.density ∧
    V.completeness ≤ W.completeness ∧
    V.separation ≤ W.separation ∧
    V.additivity ≤ W.additivity ∧
    V.invertibility ≤ W.invertibility ∧
    V.determinism ≤ W.determinism ∧
    V.support ≤ W.support ∧
    V.regularity ≤ W.regularity ∧
    V.independence ≤ W.independence

instance : DecidableRel (α := ProbabilityVertex) (· ≤ ·) := fun _ _ => by
  simp only [LE.le]
  infer_instance

/-- The product order is a partial order. -/
instance instPartialOrderProbabilityVertex : PartialOrder ProbabilityVertex where
  le_refl V := ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _,
    le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _⟩
  le_trans V W X hVW hWX := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hVW
    obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13'⟩ := hWX
    exact ⟨le_trans h1 h1', le_trans h2 h2', le_trans h3 h3', le_trans h4 h4',
           le_trans h5 h5', le_trans h6 h6', le_trans h7 h7', le_trans h8 h8',
           le_trans h9 h9', le_trans h10 h10', le_trans h11 h11', le_trans h12 h12',
           le_trans h13 h13'⟩
  le_antisymm V W hVW hWV := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hVW
    obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13'⟩ := hWV
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
    · exact le_antisymm h10 h10'
    · exact le_antisymm h11 h11'
    · exact le_antisymm h12 h12'
    · exact le_antisymm h13 h13'

/-- The most general and specific vertices form bounds. -/
instance : BoundedOrder ProbabilityVertex where
  top := mostGeneralVertex
  bot := classicalLogic
  le_top _ := ⟨OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _,
               OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _,
               OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _, OrderTop.le_top _,
               OrderTop.le_top _⟩
  bot_le _ := ⟨OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _,
               OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _,
               OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _, OrderBot.bot_le _,
               OrderBot.bot_le _⟩

/-!
## §4: Equivalence with isMoreGeneral

The abstract `≤` on ProbabilityVertex is equivalent to the manually-defined `isMoreGeneral`.
-/

/-- The product order relates to `isMoreGeneral`:
    `V ≤ W` means "W is at least as general as V", i.e., `isMoreGeneral W V`.
    This matches lattice convention where ⊤ (most general) is above ⊥ (most specific). -/
theorem le_iff_isMoreGeneral (V W : ProbabilityVertex) :
    V ≤ W ↔ isMoreGeneral W V := by
  constructor
  · intro h
    rcases h with ⟨hcomm, hdist, hprec, hord, hden, hcomp, hsep, hadd, hinv, hdet, hsup, hreg, hind⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- commutativity
      simpa [LE.le, eq_comm] using hcomm
    · -- distributivity
      simpa [LE.le, eq_comm] using hdist
    · -- precision
      simpa [LE.le, eq_comm] using hprec
    · -- order
      simpa [LE.le, eq_comm] using hord
    · -- density
      simpa [LE.le, eq_comm] using hden
    · -- completeness
      simpa [LE.le, eq_comm] using hcomp
    · -- separation
      simpa [LE.le, eq_comm] using hsep
    · -- additivity
      simpa [LE.le, eq_comm] using hadd
    · -- invertibility
      simpa [LE.le, eq_comm] using hinv
    · -- determinism
      simpa [LE.le, eq_comm] using hdet
    · -- support
      simpa [LE.le, eq_comm] using hsup
    · -- regularity
      simpa [LE.le, eq_comm] using hreg
    · -- independence
      simpa [LE.le, eq_comm] using hind
  · intro h
    rcases h with ⟨hcomm, hdist, hprec, hord, hden, hcomp, hsep, hadd, hinv, hdet, hsup, hreg, hind⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [LE.le, eq_comm] using hcomm
    · simpa [LE.le, eq_comm] using hdist
    · simpa [LE.le, eq_comm] using hprec
    · simpa [LE.le, eq_comm] using hord
    · simpa [LE.le, eq_comm] using hden
    · simpa [LE.le, eq_comm] using hcomp
    · simpa [LE.le, eq_comm] using hsep
    · simpa [LE.le, eq_comm] using hadd
    · simpa [LE.le, eq_comm] using hinv
    · simpa [LE.le, eq_comm] using hdet
    · simpa [LE.le, eq_comm] using hsup
    · simpa [LE.le, eq_comm] using hreg
    · simpa [LE.le, eq_comm] using hind

/-- `isMoreGeneral` is decidable via the decidable LE on ProbabilityVertex. -/
instance isMoreGeneral_decidable (V W : ProbabilityVertex) :
    Decidable (isMoreGeneral V W) := by
  rw [← le_iff_isMoreGeneral]
  infer_instance

/-!
## §4.1: “Collapse” Lemmas Exposed from `classifyVertex`

`Basic.lean`’s `classifyVertex` marks certain vertices as *impossible* because they are
definitionally / semantically incoherent with the Knuth–Skilling separation (“sandwich”) axioms.

This section exposes these checks as reusable lemmas, so other files can depend on them without
repeating the `classifyVertex`-pattern matching manually.
-/

/-- Convenience predicate: `classifyVertex v` reports `v` as impossible. -/
def ClassifiedImpossible (v : ProbabilityVertex) : Prop :=
  ∃ msg : String, classifyVertex v = .impossible msg

/-- Collapse rule: Boolean event structure cannot be paired with noncommutative combination. -/
theorem classifiedImpossible_of_noncommutative_boolean (v : ProbabilityVertex)
    (hcomm : v.commutativity = .noncommutative) (hbool : v.distributivity = .boolean) :
    ClassifiedImpossible v := by
  refine ⟨"Boolean algebra is always commutative", ?_⟩
  have h0 : v.commutativity = .noncommutative ∧ v.distributivity = .boolean := ⟨hcomm, hbool⟩
  simp [classifyVertex, h0]

/-- Collapse rule: Orthomodular lattices are the noncommutative generalization, so the commutative
vertex is marked impossible by the classifier. -/
theorem classifiedImpossible_of_commutative_orthomodular (v : ProbabilityVertex)
    (hcomm : v.commutativity = .commutative) (homl : v.distributivity = .orthomodular) :
    ClassifiedImpossible v := by
  refine ⟨"Orthomodular is the non-commutative generalization", ?_⟩
  have h1 : v.commutativity = .commutative ∧ v.distributivity = .orthomodular := ⟨hcomm, homl⟩
  simp [classifyVertex, hcomm, h1]

/-- Collapse rule: Deterministic logic has precise (two-valued) truth values, so a deterministic
but imprecise vertex is marked impossible. -/
theorem classifiedImpossible_of_deterministic_imprecise (v : ProbabilityVertex)
    (hdet : v.determinism = .deterministic) (himp : v.precision = .imprecise) :
    ClassifiedImpossible v := by
  classical
  by_cases h0 : v.commutativity = .noncommutative ∧ v.distributivity = .boolean
  · exact ⟨"Boolean algebra is always commutative", by simp [classifyVertex, h0]⟩
  by_cases h1 : v.commutativity = .commutative ∧ v.distributivity = .orthomodular
  · exact ⟨"Orthomodular is the non-commutative generalization", by simp [classifyVertex, h1]⟩
  refine ⟨"Deterministic logic has precise truth values", ?_⟩
  have h2 : v.determinism = .deterministic ∧ v.precision = .imprecise := ⟨hdet, himp⟩
  simp [classifyVertex, h0, h1, h2]

theorem classifiedImpossible_of_badSeparationPrereq (v : ProbabilityVertex)
    (hsep : v.separation ≠ .none)
    (hbad :
      v.orderAxis = .partialOrder ∨ v.invertibility = .semigroup ∨ v.commutativity = .noncommutative) :
    ClassifiedImpossible v := by
  classical
  -- The first three `classifyVertex` impossibility branches take priority; discharge them first.
  by_cases h0 : v.commutativity = .noncommutative ∧ v.distributivity = .boolean
  · refine ⟨"Boolean algebra is always commutative", ?_⟩
    simp [classifyVertex, h0]
  by_cases h1 : v.commutativity = .commutative ∧ v.distributivity = .orthomodular
  · refine ⟨"Orthomodular is the non-commutative generalization", ?_⟩
    simp [classifyVertex, h1]
  by_cases h2 : v.determinism = .deterministic ∧ v.precision = .imprecise
  · refine ⟨"Deterministic logic has precise truth values", ?_⟩
    simp [classifyVertex, h0, h1, h2]

  -- Now we are in the separation-specific part of the classifier.
  by_cases hord : v.orderAxis = .partialOrder
  · refine ⟨"KSSeparation is defined only for total (trichotomous) plausibility orders", ?_⟩
    simp [classifyVertex, h0, h1, h2, hsep, hord]
  by_cases hinv : v.invertibility = .semigroup
  · refine ⟨"KSSeparation assumes an identity element (at least a monoid)", ?_⟩
    simp [classifyVertex, h0, h1, h2, hsep, hord, hinv]

  -- Remaining case: separation is asserted, order is total, invertibility is not semigroup.
  -- So `hbad` can only be satisfied by noncommutativity.
  have hcomm : v.commutativity = .noncommutative := by
    rcases hbad with hord' | hinv' | hcomm'
    · exact (hord hord').elim
    · exact (hinv hinv').elim
    · exact hcomm'
  refine ⟨"KSSeparation forces commutativity (see KnuthSkilling/Separation/SandwichSeparation.lean)", ?_⟩
  have hbool : v.distributivity ≠ .boolean := by
    intro hdis
    exact h0 ⟨hcomm, hdis⟩
  simp [classifyVertex, h2, hsep, hord, hinv, hcomm, hbool]

theorem classifiedImpossible_of_sep_partialOrder (v : ProbabilityVertex)
    (hsep : v.separation ≠ .none) (hord : v.orderAxis = .partialOrder) :
    ClassifiedImpossible v :=
  classifiedImpossible_of_badSeparationPrereq v hsep (Or.inl hord)

theorem classifiedImpossible_of_sep_semigroup (v : ProbabilityVertex)
    (hsep : v.separation ≠ .none) (hinv : v.invertibility = .semigroup) :
    ClassifiedImpossible v :=
  classifiedImpossible_of_badSeparationPrereq v hsep (Or.inr (Or.inl hinv))

theorem classifiedImpossible_of_sep_noncommutative (v : ProbabilityVertex)
    (hsep : v.separation ≠ .none) (hcomm : v.commutativity = .noncommutative) :
    ClassifiedImpossible v :=
  classifiedImpossible_of_badSeparationPrereq v hsep (Or.inr (Or.inr hcomm))

/-!
## §4.2: Collapse Lemma for Finite Support vs σ-Additivity

`classifyVertex` treats the following combination as “impossible” because it is not a genuinely
distinct theory:

* finite support, plus
* only “finitely additive” regularity, plus
* full additivity

On finite sample spaces, σ-additivity and finite additivity coincide, so this vertex collapses to a
neighbor with stronger regularity.
-/

theorem classifiedImpossible_of_finiteSupport_finitelyAdditive_additive (v : ProbabilityVertex)
    (hsup : v.support = .finite) (hreg : v.regularity = .finitelyAdditive)
    (hadd : v.additivity = .additive) :
    ClassifiedImpossible v := by
  classical
  -- Discharge earlier classifier branches first (they take priority).
  by_cases h0 : v.commutativity = .noncommutative ∧ v.distributivity = .boolean
  · exact ⟨"Boolean algebra is always commutative", by simp [classifyVertex, h0]⟩
  by_cases h1 : v.commutativity = .commutative ∧ v.distributivity = .orthomodular
  · exact
      ⟨"Orthomodular is the non-commutative generalization", by simp [classifyVertex, h1]⟩
  by_cases h2 : v.determinism = .deterministic ∧ v.precision = .imprecise
  · exact ⟨"Deterministic logic has precise truth values", by simp [classifyVertex, h0, h1, h2]⟩
  by_cases h3 : v.separation ≠ .none ∧ v.orderAxis = .partialOrder
  · exact
      ⟨"KSSeparation is defined only for total (trichotomous) plausibility orders",
        by simp [classifyVertex, h0, h1, h2, h3]⟩
  by_cases h4 : v.separation ≠ .none ∧ v.invertibility = .semigroup
  · refine ⟨"KSSeparation assumes an identity element (at least a monoid)", ?_⟩
    have hsep : v.separation ≠ .none := h4.1
    have hord : ¬ v.orderAxis = .partialOrder := by
      intro hord
      exact h3 ⟨hsep, hord⟩
    simp [classifyVertex, h0, h1, h2, hsep, hord, h4.2]
  by_cases h5 : v.separation ≠ .none ∧ v.commutativity = .noncommutative
  · refine
      ⟨"KSSeparation forces commutativity (see KnuthSkilling/Separation/SandwichSeparation.lean)",
        ?_⟩
    have hsep : v.separation ≠ .none := h5.1
    have hcomm : v.commutativity = .noncommutative := h5.2
    have hbool : ¬ v.distributivity = .boolean := by
      intro hdis
      exact h0 ⟨hcomm, hdis⟩
    have hord : ¬ v.orderAxis = .partialOrder := by
      intro hord
      exact h3 ⟨hsep, hord⟩
    have hinv : ¬ v.invertibility = .semigroup := by
      intro hinv
      exact h4 ⟨hsep, hinv⟩
    simp [classifyVertex, h2, hbool, hsep, hord, hinv, hcomm]

  refine ⟨"Finite support with σ-additivity equals finite additivity", ?_⟩
  have h6 : v.support = .finite ∧ v.regularity = .finitelyAdditive ∧ v.additivity = .additive :=
    ⟨hsup, hreg, hadd⟩
  simp [classifyVertex, h0, h1, h2, h3, h4, h5, h6]

/-!
## §5: Counting and Enumeration

Utility functions for working with the hypercube structure.
-/

/-- Total number of vertices in the hypercube. -/
def vertexCount : ℕ := 2 * 4 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 3 * 3 * 3 * 4

theorem vertexCount_eq : vertexCount = 373248 := rfl

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
       V.density ≤ mostGeneralVertex.density ∧
       V.completeness ≤ mostGeneralVertex.completeness ∧
       V.separation ≤ mostGeneralVertex.separation ∧
       V.additivity ≤ mostGeneralVertex.additivity ∧
       V.invertibility ≤ mostGeneralVertex.invertibility ∧
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
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  constructor; · exact le_top
  · exact le_top

/-- classicalLogic is dominated by everything (restated using ≤). -/
theorem classicalLogic_bot (V : ProbabilityVertex) : classicalLogic ≤ V := by
  show classicalLogic.commutativity ≤ V.commutativity ∧
       classicalLogic.distributivity ≤ V.distributivity ∧
       classicalLogic.precision ≤ V.precision ∧
       classicalLogic.orderAxis ≤ V.orderAxis ∧
       classicalLogic.density ≤ V.density ∧
       classicalLogic.completeness ≤ V.completeness ∧
       classicalLogic.separation ≤ V.separation ∧
       classicalLogic.additivity ≤ V.additivity ∧
       classicalLogic.invertibility ≤ V.invertibility ∧
       classicalLogic.determinism ≤ V.determinism ∧
       classicalLogic.support ≤ V.support ∧
       classicalLogic.regularity ≤ V.regularity ∧
       classicalLogic.independence ≤ V.independence
  exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le,
    bot_le, bot_le⟩

/-- Kolmogorov is in the middle of the lattice. -/
theorem kolmogorov_intermediate :
    classicalLogic ≤ kolmogorov ∧ kolmogorov ≤ mostGeneralVertex := by
  constructor
  · -- Expand the LE definition
    show classicalLogic.commutativity ≤ kolmogorov.commutativity ∧
         classicalLogic.distributivity ≤ kolmogorov.distributivity ∧
         classicalLogic.precision ≤ kolmogorov.precision ∧
         classicalLogic.orderAxis ≤ kolmogorov.orderAxis ∧
         classicalLogic.density ≤ kolmogorov.density ∧
         classicalLogic.completeness ≤ kolmogorov.completeness ∧
         classicalLogic.separation ≤ kolmogorov.separation ∧
         classicalLogic.additivity ≤ kolmogorov.additivity ∧
         classicalLogic.invertibility ≤ kolmogorov.invertibility ∧
         classicalLogic.determinism ≤ kolmogorov.determinism ∧
         classicalLogic.support ≤ kolmogorov.support ∧
         classicalLogic.regularity ≤ kolmogorov.regularity ∧
         classicalLogic.independence ≤ kolmogorov.independence
    exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le,
      bot_le, bot_le⟩
  · -- Expand the LE definition for top
    show kolmogorov.commutativity ≤ mostGeneralVertex.commutativity ∧
         kolmogorov.distributivity ≤ mostGeneralVertex.distributivity ∧
         kolmogorov.precision ≤ mostGeneralVertex.precision ∧
         kolmogorov.orderAxis ≤ mostGeneralVertex.orderAxis ∧
         kolmogorov.density ≤ mostGeneralVertex.density ∧
         kolmogorov.completeness ≤ mostGeneralVertex.completeness ∧
         kolmogorov.separation ≤ mostGeneralVertex.separation ∧
         kolmogorov.additivity ≤ mostGeneralVertex.additivity ∧
         kolmogorov.invertibility ≤ mostGeneralVertex.invertibility ∧
         kolmogorov.determinism ≤ mostGeneralVertex.determinism ∧
         kolmogorov.support ≤ mostGeneralVertex.support ∧
         kolmogorov.regularity ≤ mostGeneralVertex.regularity ∧
         kolmogorov.independence ≤ mostGeneralVertex.independence
    -- kolmogorov.independence = .tensor, mostGeneralVertex.independence = .free
    exact ⟨le_top, le_top, le_top, le_top, le_top, le_top, le_top, le_top, le_top, le_top, le_top,
      le_top, le_top⟩

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
         classicalLogic.density ≤ V.density ∧
         classicalLogic.completeness ≤ V.completeness ∧
         classicalLogic.separation ≤ V.separation ∧
         classicalLogic.additivity ≤ V.additivity ∧
         classicalLogic.invertibility ≤ V.invertibility ∧
         classicalLogic.determinism ≤ V.determinism ∧
         classicalLogic.support ≤ V.support ∧
         classicalLogic.regularity ≤ V.regularity ∧
         classicalLogic.independence ≤ V.independence
    exact ⟨bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le, bot_le,
      bot_le, bot_le⟩
  · -- V ≤ mostGeneralVertex (expand LE definition)
    show V.commutativity ≤ mostGeneralVertex.commutativity ∧
         V.distributivity ≤ mostGeneralVertex.distributivity ∧
         V.precision ≤ mostGeneralVertex.precision ∧
         V.orderAxis ≤ mostGeneralVertex.orderAxis ∧
         V.density ≤ mostGeneralVertex.density ∧
         V.completeness ≤ mostGeneralVertex.completeness ∧
         V.separation ≤ mostGeneralVertex.separation ∧
         V.additivity ≤ mostGeneralVertex.additivity ∧
         V.invertibility ≤ mostGeneralVertex.invertibility ∧
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
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    constructor; · exact le_top
    · exact le_top

/-
## §X: Collapse Rules (Semantic, Not Poset-Theoretic)

`Hypercube/Taxonomy.lean` defines the **weakness/strength** order on vertices purely by comparing
which axioms are assumed on each axis.

Some relationships between axes only appear once we interpret a vertex *semantically* (e.g. after
deriving a real-valued representation `Θ`).  A common example is the “discrete vs dense” dichotomy
for additive subgroups of an archimedean ordered group.

We re-export the key lemmas from `Hypercube/DensityAxisStory.lean` here so that downstream modules
that already import `Hypercube/Taxonomy.lean` can use them without an extra import.
-/

section DensityCollapse

open DensityAxisStory

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

theorem densityAxisOfSubgroup_eq_dense_iff (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .dense ↔ Dense (S : Set G) :=
  DensityAxisStory.densityAxisOfSubgroup_eq_dense_iff (G := G) (S := S)

theorem densityAxisOfSubgroup_eq_nondense_iff (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .nondense ↔ ¬ Dense (S : Set G) :=
  DensityAxisStory.densityAxisOfSubgroup_eq_nondense_iff (G := G) (S := S)

section Ordered

variable [LinearOrder G] [IsOrderedAddMonoid G] [OrderTopology G] [Archimedean G]

section DenseVsZ

variable [Nontrivial G] [DenselyOrdered G]

theorem densityAxisOfSubgroup_eq_dense_iff_ne_zmultiples (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .dense ↔
      ∀ g : G, S ≠ AddSubgroup.zmultiples g :=
  DensityAxisStory.densityAxisOfSubgroup_eq_dense_iff_ne_zmultiples (G := G) (S := S)

end DenseVsZ

theorem densityAxisOfSubgroup_eq_nondense_implies_zmultiples (S : AddSubgroup G)
    (h : densityAxisOfSubgroup (G := G) S = .nondense) :
    ∃ g : G, S = AddSubgroup.zmultiples g :=
  DensityAxisStory.densityAxisOfSubgroup_eq_nondense_implies_zmultiples (G := G) (S := S) h

end Ordered

end DensityCollapse

end Mettapedia.ProbabilityTheory.Hypercube
