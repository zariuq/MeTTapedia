import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Germ.Basic

/-!
# Cofinite reduced powers and relative infinity

The germ of a sequence at the cofinite filter is a reduced power requiring no
choice of a free ultrafilter.  The identity sequence defines an element above
every constant natural-number germ and outside the diagonal image.

This is a choice-free relative-infinity baseline, not an ultraproduct.  The
eventual order is only partial: two oscillating germs are explicitly
incomparable.  Passing to a free ultrafilter can make the order total and supply
first-order transfer, but that is an additional classical profile rather than a
property of the cofinite construction.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.CofiniteReducedPower

open Filter

/-- Sequences modulo eventual equality outside a finite set. -/
abbrev Carrier (Value : Type*) : Type _ :=
  Filter.Germ (Filter.cofinite : Filter Nat) Value

/-- Embed a value as the germ of its constant sequence. -/
def diagonal {Value : Type*} (value : Value) : Carrier Value :=
  (value : Carrier Value)

/-- The germ of the identity sequence. -/
def growing : Carrier Nat :=
  (fun index : Nat => index : Carrier Nat)

/-- Constant germs remain distinct. -/
theorem diagonal_injective :
    Function.Injective (diagonal : Nat → Carrier Nat) := by
  intro first second equalGerms
  exact Filter.Germ.const_inj.mp equalGerms

/-- Every standard natural is eventually below the growing germ. -/
theorem diagonal_le_growing (value : Nat) :
    diagonal value ≤ growing := by
  change ∀ᶠ index : Nat in Filter.cofinite, value ≤ index
  rw [Nat.cofinite_eq_atTop]
  exact Filter.eventually_ge_atTop value

/-- The growing germ is not any constant germ. -/
theorem growing_ne_diagonal (value : Nat) :
    growing ≠ diagonal value := by
  intro equalGerms
  have eventuallyConstant :
      (fun index : Nat => index) =ᶠ[Filter.cofinite]
        (fun _index : Nat => value) :=
    Filter.Germ.coe_eq.mp equalGerms
  rw [Nat.cofinite_eq_atTop] at eventuallyConstant
  change (∀ᶠ index : Nat in Filter.atTop, index = value) at eventuallyConstant
  rw [Filter.eventually_atTop] at eventuallyConstant
  obtain ⟨threshold, constantAfter⟩ := eventuallyConstant
  have impossible := constantAfter (max threshold (value + 1))
    (le_max_left threshold (value + 1))
  omega

/-- The relative infinity is strictly above every standard diagonal point. -/
theorem diagonal_lt_growing (value : Nat) :
    diagonal value < growing := by
  rw [lt_iff_le_and_ne]
  exact ⟨diagonal_le_growing value, (growing_ne_diagonal value).symm⟩

/-- The diagonal embedding does not exhaust the cofinite reduced power. -/
theorem diagonal_not_surjective :
    ¬ Function.Surjective (diagonal : Nat → Carrier Nat) := by
  intro diagonalSurjective
  obtain ⟨value, valueMaps⟩ := diagonalSurjective growing
  exact growing_ne_diagonal value valueMaps.symm

/-! ## The price of avoiding a free ultrafilter -/

/-- An oscillating representative which is high at even indices. -/
def evenHigh : Carrier Nat :=
  (fun index : Nat => if index % 2 = 0 then 1 else 0 : Carrier Nat)

/-- An oscillating representative which is high at odd indices. -/
def oddHigh : Carrier Nat :=
  (fun index : Nat => if index % 2 = 0 then 0 else 1 : Carrier Nat)

/-- The even-high germ is not eventually below the odd-high germ. -/
theorem not_evenHigh_le_oddHigh : ¬ evenHigh ≤ oddHigh := by
  intro eventuallyBelow
  change
    (∀ᶠ index : Nat in Filter.cofinite,
      (if index % 2 = 0 then 1 else 0) ≤
        (if index % 2 = 0 then 0 else 1)) at eventuallyBelow
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at eventuallyBelow
  obtain ⟨threshold, belowAfter⟩ := eventuallyBelow
  have atEven := belowAfter (2 * threshold) (by omega)
  have evenRemainder : (2 * threshold) % 2 = 0 := by omega
  simp only [evenRemainder, ↓reduceIte] at atEven
  omega

/-- The odd-high germ is not eventually below the even-high germ. -/
theorem not_oddHigh_le_evenHigh : ¬ oddHigh ≤ evenHigh := by
  intro eventuallyBelow
  change
    (∀ᶠ index : Nat in Filter.cofinite,
      (if index % 2 = 0 then 0 else 1) ≤
        (if index % 2 = 0 then 1 else 0)) at eventuallyBelow
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at eventuallyBelow
  obtain ⟨threshold, belowAfter⟩ := eventuallyBelow
  have atOdd := belowAfter (2 * threshold + 1) (by omega)
  have oddRemainder : (2 * threshold + 1) % 2 ≠ 0 := by omega
  simp only [oddRemainder, ↓reduceIte] at atOdd
  omega

/-- Negative canary: the eventual order is genuinely partial.  A free
ultrafilter is additional structure precisely because it decides such
cofinite-indeterminate oscillations. -/
theorem oscillators_incomparable :
    (¬ evenHigh ≤ oddHigh) ∧ (¬ oddHigh ≤ evenHigh) :=
  ⟨not_evenHigh_le_oddHigh, not_oddHigh_le_evenHigh⟩

/-- The positive relative-infinity theorem paired with non-surjectivity. -/
theorem cofinite_relative_infinity :
    (∀ value : Nat, diagonal value < growing) ∧
      ¬ Function.Surjective (diagonal : Nat → Carrier Nat) :=
  ⟨diagonal_lt_growing, diagonal_not_surjective⟩

/-! ## An explicit choice-free tail presentation

Mathlib's generic filter-basis implementation is classical.  The following
equivalent tail presentation isolates the mathematical core directly: two
sequences agree when a concrete threshold bounds all their disagreements.  Its
proofs use quotient soundness and propositional extensionality, but no classical
choice and no ultrafilter-selection principle.
-/

namespace Tail

universe u

/-- Eventual equality presented by an explicit tail threshold. -/
def EventuallyEqual {Value : Type u} (first second : Nat → Value) : Prop :=
  ∃ threshold : Nat, ∀ index : Nat, threshold ≤ index →
    first index = second index

theorem eventuallyEqual_refl {Value : Type u} (sequence : Nat → Value) :
    EventuallyEqual sequence sequence :=
  ⟨0, fun _index _bound => rfl⟩

theorem eventuallyEqual_symm {Value : Type u}
    {first second : Nat → Value}
    (equal : EventuallyEqual first second) :
    EventuallyEqual second first := by
  obtain ⟨threshold, equalAfter⟩ := equal
  exact ⟨threshold, fun index bound => (equalAfter index bound).symm⟩

theorem eventuallyEqual_trans {Value : Type u}
    {first second third : Nat → Value}
    (firstSecond : EventuallyEqual first second)
    (secondThird : EventuallyEqual second third) :
    EventuallyEqual first third := by
  obtain ⟨firstThreshold, firstAfter⟩ := firstSecond
  obtain ⟨secondThreshold, secondAfter⟩ := secondThird
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro index bound
  exact (firstAfter index ((le_max_left ..).trans bound)).trans
    (secondAfter index ((le_max_right ..).trans bound))

/-- The explicit tail-equivalence relation on sequences. -/
def sequenceSetoid (Value : Type u) : Setoid (Nat → Value) where
  r := EventuallyEqual
  iseqv :=
    ⟨fun sequence => eventuallyEqual_refl sequence,
      fun {_first _second} equal => eventuallyEqual_symm equal,
      fun {_first _second _third} firstSecond secondThird =>
        eventuallyEqual_trans firstSecond secondThird⟩

/-- Sequences modulo equality after one explicit finite threshold. -/
def Carrier (Value : Type u) : Type u :=
  Quotient (sequenceSetoid Value)

/-- Form a tail class from a sequence. -/
def ofSequence {Value : Type u} (sequence : Nat → Value) : Carrier Value :=
  Quotient.mk (sequenceSetoid Value) sequence

/-- Embed a value as a constant tail class. -/
def diagonal {Value : Type u} (value : Value) : Carrier Value :=
  ofSequence fun _index => value

/-- The identity sequence as an explicit tail class. -/
def growing : Carrier Nat :=
  ofSequence fun index => index

/-- Eventually-below, also with an explicit threshold. -/
def EventuallyLE {Value : Type u} [LE Value]
    (first second : Nat → Value) : Prop :=
  ∃ threshold : Nat, ∀ index : Nat, threshold ≤ index →
    first index ≤ second index

theorem eventuallyLE_transport {Value : Type u} [LE Value]
    {first first' second second' : Nat → Value}
    (firstEqual : EventuallyEqual first first')
    (secondEqual : EventuallyEqual second second')
    (below : EventuallyLE first second) :
    EventuallyLE first' second' := by
  obtain ⟨belowThreshold, belowAfter⟩ := below
  obtain ⟨firstThreshold, firstAfter⟩ := firstEqual
  obtain ⟨secondThreshold, secondAfter⟩ := secondEqual
  refine ⟨max belowThreshold (max firstThreshold secondThreshold), ?_⟩
  intro index bound
  have belowBound : belowThreshold ≤ index :=
    (le_max_left belowThreshold (max firstThreshold secondThreshold)).trans bound
  have firstBound : firstThreshold ≤ index :=
    (le_max_of_le_right (le_max_left firstThreshold secondThreshold)).trans bound
  have secondBound : secondThreshold ≤ index :=
    (le_max_of_le_right (le_max_right firstThreshold secondThreshold)).trans bound
  rw [← firstAfter index firstBound, ← secondAfter index secondBound]
  exact belowAfter index belowBound

theorem eventuallyLE_congr {Value : Type u} [LE Value]
    {first first' second second' : Nat → Value}
    (firstEqual : EventuallyEqual first first')
    (secondEqual : EventuallyEqual second second') :
    EventuallyLE first second ↔ EventuallyLE first' second' :=
  ⟨eventuallyLE_transport firstEqual secondEqual,
    eventuallyLE_transport
      (eventuallyEqual_symm firstEqual)
      (eventuallyEqual_symm secondEqual)⟩

/-- Lift eventual order to tail classes. -/
def le {Value : Type u} [LE Value]
    (first second : Carrier Value) : Prop :=
  Quotient.liftOn₂ first second EventuallyLE
    (fun _first _second _first' _second' firstEqual secondEqual =>
      propext (eventuallyLE_congr firstEqual secondEqual))

instance {Value : Type u} [LE Value] : LE (Carrier Value) :=
  ⟨le⟩

instance {Value : Type u} [Preorder Value] : Preorder (Carrier Value) where
  le_refl value := by
    refine Quotient.inductionOn' value ?_
    intro sequence
    exact ⟨0, fun index _bound => le_refl (sequence index)⟩
  le_trans first second third := by
    refine Quotient.inductionOn₃' first second third ?_
    intro firstSequence secondSequence thirdSequence firstBelow secondBelow
    obtain ⟨firstThreshold, firstAfter⟩ := firstBelow
    obtain ⟨secondThreshold, secondAfter⟩ := secondBelow
    refine ⟨max firstThreshold secondThreshold, ?_⟩
    intro index bound
    exact (firstAfter index ((le_max_left ..).trans bound)).trans
      (secondAfter index ((le_max_right ..).trans bound))

instance {Value : Type u} [PartialOrder Value] : PartialOrder (Carrier Value) where
  le_antisymm first second := by
    refine Quotient.inductionOn₂' first second ?_
    intro firstSequence secondSequence firstBelow secondBelow
    apply Quotient.sound
    obtain ⟨firstThreshold, firstAfter⟩ := firstBelow
    obtain ⟨secondThreshold, secondAfter⟩ := secondBelow
    refine ⟨max firstThreshold secondThreshold, ?_⟩
    intro index bound
    exact le_antisymm
      (firstAfter index ((le_max_left ..).trans bound))
      (secondAfter index ((le_max_right ..).trans bound))

theorem diagonal_injective :
    Function.Injective (diagonal : Nat → Carrier Nat) := by
  intro first second equalClasses
  have equalAfter : EventuallyEqual
      (fun _index : Nat => first) (fun _index : Nat => second) :=
    Quotient.eq''.mp equalClasses
  obtain ⟨threshold, equalAt⟩ := equalAfter
  exact equalAt threshold (le_refl threshold)

theorem diagonal_le_growing (value : Nat) :
    diagonal value ≤ growing :=
  ⟨value, fun _index bound => bound⟩

theorem growing_ne_diagonal (value : Nat) :
    growing ≠ diagonal value := by
  intro equalClasses
  have equalAfter : EventuallyEqual
      (fun index : Nat => index) (fun _index : Nat => value) :=
    Quotient.eq''.mp equalClasses
  obtain ⟨threshold, equalAt⟩ := equalAfter
  have impossible : max threshold (value + 1) = value :=
    equalAt (max threshold (value + 1))
      (le_max_left threshold (value + 1))
  omega

theorem diagonal_lt_growing (value : Nat) :
    diagonal value < growing := by
  rw [lt_iff_le_and_ne]
  exact ⟨diagonal_le_growing value, (growing_ne_diagonal value).symm⟩

theorem diagonal_not_surjective :
    ¬ Function.Surjective (diagonal : Nat → Carrier Nat) := by
  intro diagonalSurjective
  obtain ⟨value, valueMaps⟩ := diagonalSurjective growing
  exact growing_ne_diagonal value valueMaps.symm

/-- Even-high and odd-high sequences remain incomparable without an ultrafilter
choosing one parity class as large. -/
def evenHigh : Carrier Nat :=
  ofSequence fun index => if index % 2 = 0 then 1 else 0

def oddHigh : Carrier Nat :=
  ofSequence fun index => if index % 2 = 0 then 0 else 1

theorem not_evenHigh_le_oddHigh : ¬ evenHigh ≤ oddHigh := by
  intro below
  obtain ⟨threshold, belowAfter⟩ := below
  have atEven := belowAfter (2 * threshold) (by omega)
  have evenRemainder : (2 * threshold) % 2 = 0 := by omega
  simp only [evenRemainder, ↓reduceIte] at atEven
  omega

theorem not_oddHigh_le_evenHigh : ¬ oddHigh ≤ evenHigh := by
  intro below
  obtain ⟨threshold, belowAfter⟩ := below
  have atOdd := belowAfter (2 * threshold + 1) (by omega)
  have oddRemainder : (2 * threshold + 1) % 2 ≠ 0 := by omega
  simp only [oddRemainder, ↓reduceIte] at atOdd
  omega

theorem oscillators_incomparable :
    (¬ evenHigh ≤ oddHigh) ∧ (¬ oddHigh ≤ evenHigh) :=
  ⟨not_evenHigh_le_oddHigh, not_oddHigh_le_evenHigh⟩

theorem relative_infinity :
    (∀ value : Nat, diagonal value < growing) ∧
      ¬ Function.Surjective (diagonal : Nat → Carrier Nat) :=
  ⟨diagonal_lt_growing, diagonal_not_surjective⟩

#print axioms diagonal_injective
#print axioms diagonal_le_growing
#print axioms growing_ne_diagonal
#print axioms diagonal_lt_growing
#print axioms diagonal_not_surjective
#print axioms oscillators_incomparable
#print axioms relative_infinity

end Tail

#print axioms diagonal_injective
#print axioms diagonal_le_growing
#print axioms growing_ne_diagonal
#print axioms diagonal_lt_growing
#print axioms diagonal_not_surjective
#print axioms oscillators_incomparable
#print axioms cofinite_relative_infinity

end Mettapedia.UniversalAlgebra.CofiniteReducedPower
