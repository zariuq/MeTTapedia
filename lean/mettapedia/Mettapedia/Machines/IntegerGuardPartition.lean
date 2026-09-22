import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
# Complementary integer guards and ordered branch answers

These are list/algebra laws for completed, pure Boolean tests on actual integer
values. A successful guard returns the unchanged caller environment once; a
false guard completes with no answers. Branch continuations may return any
ordered list of answers and final environments, including duplicates or none.

The source shape is two guarded alternatives. The target shape is one lazy
conditional. Their equality preserves the complete ordered answer/environment
list, not merely its set of values. This module defines no term syntax or
calculus and imports no Horn or BNF semantics.

Applying the law to a generated program still requires an exact source bridge:
ground integer operands, matching comparison/successor shapes, pure completed
guards, exact installed provider occurrences, and preserved alternative
placement. A per-equation semideterminism result does not prove whole-program
uniqueness. Errors, unsupported inputs, effects, native overflow, and infinite
enumerations are not silently interpreted as false tests.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IntegerGuardPartition

universe u v w

variable {Caller : Type u} {Answer : Type v} {Occurrence : Type w}

/-- A completed pure guard passes the exact caller unchanged, zero or one time. -/
def guard (accepted : Bool) (caller : Caller) : List Caller :=
  if accepted then [caller] else []

theorem guard_preserves_caller (accepted : Bool) (caller after : Caller)
    (member : after ∈ guard accepted caller) : after = caller := by
  cases accepted <;> simp_all [guard]

/-- Following a pure guard preserves ordinary ordered-list composition. -/
theorem guard_flatMap (accepted : Bool) (caller : Caller)
    (branch : Caller → List (Answer × Caller)) :
    (guard accepted caller).flatMap branch =
      if accepted then branch caller else [] := by
  cases accepted <;> simp [guard]

/-- Independent complementary guards can be replaced by one conditional.
Both branches retain all their answer occurrences and final environments. -/
theorem complementary_guard_fusion (accepted : Bool) (caller : Caller)
    (yes no : Caller → List (Answer × Caller)) :
    (guard accepted caller).flatMap yes ++
        (guard (!accepted) caller).flatMap no =
      if accepted then yes caller else no caller := by
  cases accepted <;> simp [guard]

/-- The source may list the negative alternative first: mutual exclusion
still selects exactly the same branch, without reordering that branch's list. -/
theorem complementary_guard_fusion_negative_first (accepted : Bool) (caller : Caller)
    (yes no : Caller → List (Answer × Caller)) :
    (guard (!accepted) caller).flatMap no ++
        (guard accepted caller).flatMap yes =
      if accepted then yes caller else no caller := by
  cases accepted <;> simp [guard]

/-- A contiguous pair can be fused inside a larger ordered answer sequence.
This does not authorize moving it across an intervening producing alternative. -/
theorem complementary_guard_fusion_in_context (accepted : Bool) (caller : Caller)
    (yes no : Caller → List (Answer × Caller))
    (before after : List (Answer × Caller)) :
    before ++ ((guard accepted caller).flatMap yes ++
        (guard (!accepted) caller).flatMap no) ++ after =
      before ++ (if accepted then yes caller else no caller) ++ after := by
  rw [complementary_guard_fusion]

/-- Integer order, independently of any provider name, gives exact complementary
Boolean results. -/
theorem not_less_complements_less (left right : Int) :
    decide (right ≤ left) = !decide (left < right) := by
  by_cases below : left < right
  · have notAbove : ¬ right ≤ left := by omega
    simp [below, notAbove]
  · have above : right ≤ left := by omega
    simp [below, above]

theorem integer_guard_fusion (left right : Int) (caller : Caller)
    (yes no : Caller → List (Answer × Caller)) :
    (guard (decide (left < right)) caller).flatMap yes ++
        (guard (decide (right ≤ left)) caller).flatMap no =
      if left < right then yes caller else no caller := by
  rw [not_less_complements_less, complementary_guard_fusion]
  simp

/-- The gap/no-gap pair compares the SAME successor value on both sides. -/
theorem successor_guard_fusion (left right : Int) (caller : Caller)
    (yes no : Caller → List (Answer × Caller)) :
    (guard (decide (left + 1 < right)) caller).flatMap yes ++
        (guard (decide (right ≤ left + 1)) caller).flatMap no =
      if left + 1 < right then yes caller else no caller :=
  integer_guard_fusion (left + 1) right caller yes no

/-- A finite integer backend can allow successor only when the intermediate
also fits. The bound is derived from a strict upper bound on the operand. -/
theorem bounded_successor_guard_fusion (lower upper left right : Int)
    (leftBound : lower ≤ left ∧ left < upper)
    (rightBound : lower ≤ right ∧ right ≤ upper)
    (caller : Caller) (yes no : Caller → List (Answer × Caller)) :
    ((guard (decide (left + 1 < right)) caller).flatMap yes ++
        (guard (decide (right ≤ left + 1)) caller).flatMap no =
      if left + 1 < right then yes caller else no caller) ∧
      lower ≤ left + 1 ∧ left + 1 ≤ upper ∧ lower ≤ right ∧ right ≤ upper := by
  refine ⟨successor_guard_fusion left right caller yes no, ?_⟩
  exact ⟨Int.le_add_one leftBound.1, Int.add_one_le_of_lt leftBound.2, rightBound⟩

/-- Each installed provider occurrence executes independently. IDs are not
deduplicated, even if their source equations or returned values look equal. -/
def guardOccurrences (occurrences : List Occurrence) (accepted : Bool)
    (caller : Caller) : List Caller :=
  occurrences.flatMap (fun _ => guard accepted caller)

theorem guardOccurrences_singleton (occurrence : Occurrence) (accepted : Bool)
    (caller : Caller) :
    guardOccurrences [occurrence] accepted caller = guard accepted caller := by
  simp [guardOccurrences]

theorem guardOccurrences_length (occurrences : List Occurrence) (accepted : Bool)
    (caller : Caller) :
    (guardOccurrences occurrences accepted caller).length =
      if accepted then occurrences.length else 0 := by
  cases accepted <;> induction occurrences <;> simp_all [guardOccurrences, guard]

/-- Exact singleton inventories permit fusion. This premise is separate from
the behavior of an individual selected provider equation. -/
theorem singleton_provider_fusion (lessOccurrence notLessOccurrence : Occurrence)
    (left right : Int) (caller : Caller)
    (yes no : Caller → List (Answer × Caller)) :
    (guardOccurrences [lessOccurrence] (decide (left < right)) caller).flatMap yes ++
        (guardOccurrences [notLessOccurrence] (decide (right ≤ left)) caller).flatMap no =
      if left < right then yes caller else no caller := by
  simp only [guardOccurrences_singleton]
  exact integer_guard_fusion left right caller yes no

/-- Two successful source occurrences cannot be replaced by one successful
call merely because each individual occurrence is semideterministic. -/
theorem duplicate_provider_occurrences_not_singleton
    (first second : Occurrence) (caller : Caller) :
    guardOccurrences [first, second] true caller ≠ guard true caller := by
  intro same
  have counts := congrArg List.length same
  simp [guardOccurrences_length, guard] at counts

/-- Branch order and multiplicity are preserved, including changed final
environments: this law does not assume that branch bodies are state-free. -/
example :
    (guard (decide ((2 : Int) < 5)) (7 : Nat)).flatMap
        (fun state => [("a", state + 1), ("a", state + 1), ("b", state + 2)]) ++
      (guard (decide ((5 : Int) ≤ 2)) (7 : Nat)).flatMap
        (fun state => [("unused", state)]) =
      [("a", 8), ("a", 8), ("b", 9)] := by decide

/-- Boundary control: moving a conditional across an intervening answer is
not licensed by complementary-guard fusion. -/
example :
    (if false then ["yes"] else []) ++ ["middle"] ++
        (if !false then ["no"] else []) ≠
      (if false then ["yes"] else ["no"]) ++ ["middle"] := by decide

/-- Mixing gap with ordinary not-less is not complementary: both guards can
fail. The arithmetic operand shapes must agree before fusion is admitted. -/
example :
    guard (decide ((2 : Int) + 1 < 3)) (7 : Nat) ++
      guard (decide ((3 : Int) ≤ 2)) (7 : Nat) = [] := by decide

end Mettapedia.Machines.IntegerGuardPartition
