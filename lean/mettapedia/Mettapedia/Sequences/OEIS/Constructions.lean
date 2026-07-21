import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Basic

/-!
# Reusable constructors for OEIS sequence specifications

The constructors in this module keep offsets, finite domains, and recurrence
positions explicit.  They are deliberately independent of any program
language or synthesized candidate.
-/

namespace Mettapedia.Sequences.OEIS.Constructions

open scoped BigOperators

/-- A total natural-valued sequence with a mathematical OEIS offset. -/
def totalNatSpec (offset : Int) (values : Nat → Nat) : SequenceSpec where
  offset := offset
  Domain := fun index => offset ≤ index
  value := fun index => Int.ofNat (values (index - offset).toNat)

/-- A total integer-valued sequence with a mathematical OEIS offset. -/
def totalIntSpec (offset : Int) (values : Nat → Int) : SequenceSpec where
  offset := offset
  Domain := fun index => offset ≤ index
  value := fun index => values (index - offset).toNat

/-- A bounded natural-valued sequence computed from a function on positions. -/
def boundedNatSpec (offset : Int) (length : Nat) (values : Nat → Nat) :
    SequenceSpec where
  offset := offset
  Domain := fun index =>
    offset ≤ index ∧ (index - offset).toNat < length
  value := fun index => Int.ofNat (values (index - offset).toNat)

/-- A finite sequence whose exact values are part of the mathematical source. -/
def finiteNatSpec (offset : Int) (values : List Nat) : SequenceSpec :=
  boundedNatSpec offset values.length (fun position => values.getD position 0)

/-- Iterate a first-order recurrence from its seed. -/
def firstOrder {Value : Type*} (seed : Value) (step : Value → Value) : Nat → Value
  | 0 => seed
  | position + 1 => step (firstOrder seed step position)

@[simp] theorem firstOrder_zero {Value : Type*} (seed : Value) (step : Value → Value) :
    firstOrder seed step 0 = seed := rfl

@[simp] theorem firstOrder_succ {Value : Type*} (seed : Value) (step : Value → Value)
    (position : Nat) :
    firstOrder seed step (position + 1) =
      step (firstOrder seed step position) := rfl

/-- Iterate a first-order recurrence whose transition can inspect the next
zero-based position. -/
def indexedFirstOrder {Value : Type*} (seed : Value)
    (step : Nat → Value → Value) : Nat → Value
  | 0 => seed
  | position + 1 => step (position + 1) (indexedFirstOrder seed step position)

@[simp] theorem indexedFirstOrder_zero {Value : Type*} (seed : Value)
    (step : Nat → Value → Value) :
    indexedFirstOrder seed step 0 = seed := rfl

@[simp] theorem indexedFirstOrder_succ {Value : Type*} (seed : Value)
    (step : Nat → Value → Value) (position : Nat) :
    indexedFirstOrder seed step (position + 1) =
      step (position + 1) (indexedFirstOrder seed step position) := rfl

/-- State-pair implementation of a second-order recurrence. -/
def secondOrderPair {Value : Type*} (first second : Value)
    (step : Value → Value → Value) : Nat → Value × Value
  | 0 => (first, second)
  | position + 1 =>
      let previous := secondOrderPair first second step position
      (previous.2, step previous.1 previous.2)

/-- The value stream of a second-order recurrence. -/
def secondOrder {Value : Type*} (first second : Value)
    (step : Value → Value → Value) (position : Nat) : Value :=
  (secondOrderPair first second step position).1

@[simp] theorem secondOrder_zero {Value : Type*} (first second : Value)
    (step : Value → Value → Value) :
    secondOrder first second step 0 = first := rfl

@[simp] theorem secondOrder_one {Value : Type*} (first second : Value)
    (step : Value → Value → Value) :
    secondOrder first second step 1 = second := rfl

theorem secondOrderPair_eq_values {Value : Type*} (first second : Value)
    (step : Value → Value → Value) (position : Nat) :
    secondOrderPair first second step position =
      (secondOrder first second step position,
        secondOrder first second step (position + 1)) := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      simp only [secondOrderPair, secondOrder]

@[simp] theorem secondOrder_succ_succ {Value : Type*} (first second : Value)
    (step : Value → Value → Value) (position : Nat) :
    secondOrder first second step (position + 2) =
      step (secondOrder first second step position)
        (secondOrder first second step (position + 1)) := by
  unfold secondOrder
  rw [show position + 2 = (position + 1) + 1 by omega]
  simp only [secondOrderPair]

/-- Product of `term 1` through `term position`; at position zero the product
is empty and equals one. -/
def initialProduct (term : Nat → Nat) (position : Nat) : Nat :=
  ∏ index ∈ Finset.range position, term (index + 1)

@[simp] theorem initialProduct_zero (term : Nat → Nat) :
    initialProduct term 0 = 1 := by simp [initialProduct]

theorem initialProduct_succ (term : Nat → Nat) (position : Nat) :
    initialProduct term (position + 1) =
      initialProduct term position * term (position + 1) := by
  simp [initialProduct, Finset.prod_range_succ]

/-! Domain boundary fixtures. -/

theorem finiteNatSpec_first_in_domain (offset : Int) (head : Nat) (tail : List Nat) :
    (finiteNatSpec offset (head :: tail)).Domain
      ((finiteNatSpec offset (head :: tail)).index 0) := by
  simp [finiteNatSpec, boundedNatSpec, SequenceSpec.index]

theorem finiteNatSpec_end_out_of_domain (offset : Int) (values : List Nat) :
    ¬ (finiteNatSpec offset values).Domain
      ((finiteNatSpec offset values).index values.length) := by
  simp only [finiteNatSpec, boundedNatSpec, SequenceSpec.index, not_and]
  intro _
  rw [show offset + Int.ofNat values.length - offset =
      Int.ofNat values.length by ring]
  simp

#print axioms secondOrder_succ_succ
#print axioms initialProduct_succ
#print axioms finiteNatSpec_end_out_of_domain

end Mettapedia.Sequences.OEIS.Constructions
