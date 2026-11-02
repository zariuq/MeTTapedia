import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Counted balanced merge sorting by a supplied key

The comparison ledger follows the actual merge recursion. Splitting is by
contiguous halves. Sufficient depth is derived from the input size, rather
than assuming that an externally provided sorting oracle has logarithmic
cost. The bound counts key comparisons, not allocator or cache costs.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.CountedKeySort

variable {Row Key : Type*} [LinearOrder Key]

structure Result (Row : Type*) where
  rows : List Row
  comparisons : Nat
  deriving Repr, DecidableEq

def merge (key : Row → Key) : List Row → List Row → Result Row
  | [], right => ⟨right, 0⟩
  | left, [] => ⟨left, 0⟩
  | a :: left, b :: right =>
      if key a ≤ key b then
        let tail := merge key left (b :: right)
        ⟨a :: tail.rows, tail.comparisons + 1⟩
      else
        let tail := merge key (a :: left) right
        ⟨b :: tail.rows, tail.comparisons + 1⟩
termination_by left right => left.length + right.length

theorem merge_exact (key : Row → Key) (left right : List Row) :
    (merge key left right).rows = List.merge left right (fun a b => decide (key a ≤ key b)) ∧
      (merge key left right).comparisons ≤ left.length + right.length := by
  induction size : left.length + right.length using Nat.strong_induction_on generalizing left right with
  | h size ih =>
      cases left with
      | nil => simp [merge]
      | cons a left =>
          cases right with
          | nil => simp [merge]
          | cons b right =>
              by_cases before : key a ≤ key b
              · have tail := ih (left.length + (b :: right).length) (by simp_all; omega)
                  left (b :: right) rfl
                rw [merge, if_pos before, List.cons_merge_cons]
                simp only [decide_eq_true before, ↓reduceIte, tail.1]
                refine ⟨trivial, ?_⟩
                simp only [List.length_cons] at size tail
                omega
              · have tail := ih ((a :: left).length + right.length) (by simp_all; omega)
                  (a :: left) right rfl
                rw [merge, if_neg before, List.cons_merge_cons]
                simp only [decide_eq_false before, Bool.false_eq_true, ↓reduceIte, tail.1]
                refine ⟨trivial, ?_⟩
                simp only [List.length_cons] at size tail
                omega

def sort (key : Row → Key) : Nat → List Row → Option (Result Row)
  | fuel, rows =>
      if rows.length ≤ 1 then some ⟨rows, 0⟩
      else match fuel with
        | 0 => none
        | fuel + 1 => do
            let left ← sort key fuel (rows.take (rows.length / 2))
            let right ← sort key fuel (rows.drop (rows.length / 2))
            let merged := merge key left.rows right.rows
            pure ⟨merged.rows, left.comparisons + right.comparisons + merged.comparisons⟩

theorem sort_spec (key : Row → Key) (fuel : Nat) (rows : List Row)
    (enough : rows.length ≤ 2 ^ fuel) :
    ∃ result, sort key fuel rows = some result ∧ result.rows.Perm rows ∧
      result.rows.Pairwise (fun left right => key left ≤ key right) ∧
      result.comparisons ≤ rows.length * fuel := by
  induction fuel generalizing rows with
  | zero =>
      have short : rows.length ≤ 1 := by simpa using enough
      refine ⟨⟨rows, 0⟩, by simp [sort, short], List.Perm.refl _, ?_, Nat.zero_le _⟩
      cases rows with
      | nil => simp
      | cons row rest =>
          have empty : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at short; omega)
          simp [empty]
  | succ fuel ih =>
      by_cases short : rows.length ≤ 1
      · refine ⟨⟨rows, 0⟩, by simp [sort, short], List.Perm.refl _, ?_, Nat.zero_le _⟩
        cases rows with
        | nil => simp
        | cons row rest =>
            have empty : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at short; omega)
            simp [empty]
      · have half : rows.length / 2 ≤ rows.length := Nat.div_le_self _ _
        have leftSize : (rows.take (rows.length / 2)).length ≤ 2 ^ fuel := by
          rw [List.length_take, min_eq_left half]
          rw [pow_succ] at enough
          omega
        have rightSize : (rows.drop (rows.length / 2)).length ≤ 2 ^ fuel := by
          rw [List.length_drop]
          rw [pow_succ] at enough
          omega
        obtain ⟨left, leftRun, leftPerm, leftSorted, leftCost⟩ := ih _ leftSize
        obtain ⟨right, rightRun, rightPerm, rightSorted, rightCost⟩ := ih _ rightSize
        let merged := merge key left.rows right.rows
        have mergeFacts := merge_exact key left.rows right.rows
        have mergePerm : merged.rows.Perm (left.rows ++ right.rows) := by
          rw [show merged.rows = List.merge left.rows right.rows (fun a b => decide (key a ≤ key b)) from mergeFacts.1]
          exact List.merge_perm_append _
        have permutation : merged.rows.Perm rows := by
          exact (mergePerm.trans (leftPerm.append rightPerm)).trans
            (List.Perm.of_eq (List.take_append_drop _ _))
        refine ⟨⟨merged.rows, left.comparisons + right.comparisons + merged.comparisons⟩,
          ?_, permutation, ?_, ?_⟩
        · simp only [sort, if_neg short, leftRun, rightRun]
          rfl
        · rw [show merged.rows = List.merge left.rows right.rows (fun a b => decide (key a ≤ key b)) from mergeFacts.1]
          have mergedSorted := List.pairwise_merge (le := fun a b => decide (key a ≤ key b))
            (fun a b c first second => by simp only [decide_eq_true_eq] at *; exact first.trans second)
            (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (key a) (key b))
            left.rows right.rows (by simpa only [decide_eq_true_eq] using leftSorted)
            (by simpa only [decide_eq_true_eq] using rightSorted)
          simpa only [decide_eq_true_eq] using mergedSorted
        · have leftLength := leftPerm.length_eq
          have rightLength := rightPerm.length_eq
          have mergedCost := mergeFacts.2
          change merged.comparisons ≤ left.rows.length + right.rows.length at mergedCost
          rw [List.length_take, min_eq_left half] at leftLength leftCost
          rw [List.length_drop] at rightLength rightCost
          have sizes : rows.length / 2 + (rows.length - rows.length / 2) = rows.length := by omega
          have product := congrArg (fun n => n * fuel) sizes
          simp only [Nat.add_mul] at product
          change left.comparisons + right.comparisons + merged.comparisons ≤ rows.length * (fuel + 1)
          nlinarith

def depth (size : Nat) : Nat := Nat.log 2 size + 1

theorem logarithmic_sort (key : Row → Key) (rows : List Row) :
    ∃ result, sort key (depth rows.length) rows = some result ∧ result.rows.Perm rows ∧
      result.rows.Pairwise (fun left right => key left ≤ key right) ∧
      result.comparisons ≤ rows.length * depth rows.length :=
  sort_spec key _ rows (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) rows.length))

/-- The supplied depth is always sufficient. The default is unreachable by
`run_spec`; the option-valued worker above still exposes insufficient fuel. -/
def run (key : Row → Key) (rows : List Row) : Result Row :=
  (sort key (depth rows.length) rows).getD ⟨rows, 0⟩

theorem run_spec (key : Row → Key) (rows : List Row) :
    (run key rows).rows.Perm rows ∧
      (run key rows).rows.Pairwise (fun left right => key left ≤ key right) ∧
      (run key rows).comparisons ≤ rows.length * depth rows.length := by
  obtain ⟨result, completed, permutation, sorted, bound⟩ := logarithmic_sort key rows
  simpa only [run, completed, Option.getD_some] using And.intro permutation (And.intro sorted bound)

namespace Controls

theorem sorted_duplicate_occurrences :
    (sort Prod.fst 3 [(2, 20), (1, 10), (2, 21), (1, 11)]).map Result.rows =
      some [(1, 10), (1, 11), (2, 20), (2, 21)] := by decide +kernel

theorem insufficient_depth_declines : sort id 0 [2, 1] = none := by decide +kernel
theorem already_singleton_needs_no_comparisons : sort id 0 [2] = some ⟨[2], 0⟩ := by decide +kernel

end Controls

end Mettapedia.Algorithms.CountedKeySort
