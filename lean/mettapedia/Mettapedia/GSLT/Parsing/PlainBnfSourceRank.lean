import Batteries.Data.PairingHeap
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Structural source-position ranks for plain-BNF discovery

Bijective binary ranks have digits one and two, with the low digit outermost.
Successor and comparison inspect constructors only. Natural-number values are
the independent specification used by the proofs, not an execution provider.

The queue interpretation is the existing Batteries pairing heap with this
proved total comparator. No source/compiler realization or heap-content
preservation theorem is asserted by the comparator construction.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfSourceRank

inductive Rank where
  | zero
  | one (rest : Rank)
  | two (rest : Rank)
  deriving DecidableEq, Repr

def value : Rank → Nat
  | .zero => 0
  | .one rest => 2 * value rest + 1
  | .two rest => 2 * value rest + 2

def successor : Rank → Rank
  | .zero => .one .zero
  | .one rest => .two rest
  | .two rest => .one (successor rest)

theorem value_successor (rank : Rank) : value (successor rank) = value rank + 1 := by
  induction rank with
  | zero => rfl
  | one rest _ => simp [successor, value]
  | two rest ih => simp [successor, value, ih]; omega

def compareRank : Rank → Rank → Ordering
  | .zero, .zero => .eq
  | .zero, .one _ | .zero, .two _ => .lt
  | .one _, .zero | .two _, .zero => .gt
  | .one left, .one right | .two left, .two right => compareRank left right
  | .one left, .two right =>
      match compareRank left right with
      | .eq => .lt
      | result => result
  | .two left, .one right =>
      match compareRank left right with
      | .eq => .gt
      | result => result

theorem compareRank_eq_value (left right : Rank) :
    compareRank left right = compare (value left) (value right) := by
  induction left generalizing right with
  | zero =>
      cases right <;> simp [compareRank, value, Nat.compare_eq_ite_lt]
  | one left ih =>
      cases right with
      | zero => simp [compareRank, value, Nat.compare_eq_ite_lt]
      | one right =>
          rw [compareRank, ih]
          simp only [value, Nat.compare_eq_ite_lt]
          split_ifs <;> first | rfl | omega
      | two right =>
          rw [compareRank, ih]
          simp only [value, Nat.compare_eq_ite_lt]
          split_ifs <;> first | rfl | omega
  | two left ih =>
      cases right with
      | zero => simp [compareRank, value, Nat.compare_eq_ite_lt]
      | one right =>
          rw [compareRank, ih]
          simp only [value, Nat.compare_eq_ite_lt]
          split_ifs <;> first | rfl | omega
      | two right =>
          rw [compareRank, ih]
          simp only [value, Nat.compare_eq_ite_lt]
          split_ifs <;> first | rfl | omega

theorem value_injective : Function.Injective value := by
  intro left
  induction left with
  | zero =>
      intro right same
      cases right <;> simp [value] at same ⊢
  | one left ih =>
      intro right same
      cases right with
      | zero => simp [value] at same
      | one right =>
          have tails : value left = value right := by simp [value] at same; omega
          exact congrArg Rank.one (ih tails)
      | two right => simp [value] at same; omega
  | two left ih =>
      intro right same
      cases right with
      | zero => simp [value] at same
      | one right => simp [value] at same; omega
      | two right =>
          have tails : value left = value right := by simp [value] at same; omega
          exact congrArg Rank.two (ih tails)

theorem value_surjective : Function.Surjective value := by
  intro number
  induction number with
  | zero => exact ⟨.zero, rfl⟩
  | succ number ih =>
      obtain ⟨rank, represented⟩ := ih
      exact ⟨successor rank, by rw [value_successor, represented]⟩

theorem compareRank_eq_iff (left right : Rank) : compareRank left right = .eq ↔ left = right := by
  rw [compareRank_eq_value, Nat.compare_eq_eq]
  exact value_injective.eq_iff

theorem compareRank_lt_iff (left right : Rank) :
    compareRank left right = .lt ↔ value left < value right := by
  rw [compareRank_eq_value, Nat.compare_eq_lt]

theorem compareRank_gt_iff (left right : Rank) :
    compareRank left right = .gt ↔ value right < value left := by
  rw [compareRank_eq_value, Nat.compare_eq_gt]

def rankLE (left right : Rank) : Bool := (compareRank left right).isLE

theorem rankLE_iff (left right : Rank) : rankLE left right = true ↔ value left ≤ value right := by
  simp [rankLE, compareRank_eq_value, Ordering.isLE_iff_ne_gt, Nat.compare_ne_gt]

instance rankLE_total : Batteries.TotalBLE rankLE where
  total {a b} := by
    rcases Nat.le_total (value a) (value b) with before | after
    · exact Or.inl ((rankLE_iff a b).mpr before)
    · exact Or.inr ((rankLE_iff b a).mpr after)

theorem rankLE_trans {a b c : Rank} (ab : rankLE a b = true) (bc : rankLE b c = true) :
    rankLE a c = true :=
  (rankLE_iff a c).mpr (Nat.le_trans ((rankLE_iff a b).mp ab) ((rankLE_iff b c).mp bc))

abbrev Queue := Batteries.PairingHeap Rank rankLE

theorem carry_is_structural :
    successor (.two (.two .zero)) = .one (.one (.one .zero)) := rfl

/-- Ordering the outer digit before the tail gives the wrong numeric order. -/
theorem outer_digit_order_is_not_rank_order :
    compareRank (.one (.two .zero)) (.two .zero) = .gt ∧
      value (.one (.two .zero)) = 5 ∧ value (.two .zero) = 2 := by decide

theorem equal_tails_break_by_digit :
    compareRank (.one (.two .zero)) (.two (.two .zero)) = .lt ∧
      compareRank (.two (.two .zero)) (.one (.two .zero)) = .gt := by decide

theorem equal_rank_occurrences_are_retained :
    (Batteries.PairingHeap.ofList rankLE
      [.one .zero, .one .zero, .two .zero]).size = 3 := by decide

theorem duplicate_minima_are_both_returned :
    let queue : Queue := Batteries.PairingHeap.ofList rankLE
      [.two .zero, .one .zero, .one .zero]
    queue.head? = some (.one .zero) ∧ queue.tail.head? = some (.one .zero) ∧
      queue.tail.tail.head? = some (.two .zero) ∧ queue.tail.tail.tail.isEmpty = true := by decide

/-- The raw Batteries merge deliberately ignores sibling roots. Its callers
must use single-root heaps; a forest must instead pass through combine. -/
theorem merging_a_forest_loses_its_sibling :
    let forest : Batteries.PairingHeapImp.Heap Rank :=
      .node (.one .zero) .nil (.node (.two .zero) .nil .nil)
    forest.size = 2 ∧ (forest.merge rankLE .nil).size = 1 ∧
      (forest.combine rankLE).size = 2 := by decide

end Mettapedia.GSLT.Parsing.PlainBnfSourceRank
