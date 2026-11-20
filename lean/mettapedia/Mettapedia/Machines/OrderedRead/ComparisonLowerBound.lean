import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A comparison-only lower bound for complete ordered delivery

An input permutation assigns distinct ranks to occurrence positions. A leaf
returns a permutation of positions; correctness requires the inverse input
permutation, not a constant sorted list of rank values. Nodes may inspect only
one pairwise comparison. A work cap on every actual input implies `n! ≤ 2^cap`.

This is a total comparison-work bound. It is not a per-pop lower bound and
does not apply to direct addressing, radix operations, maintained order or
previously paid sorting. Unreachable branches are removed before counting.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead.ComparisonLowerBound

abbrev Input (number : Nat) := Equiv.Perm (Fin number)
abbrev Question (number : Nat) := Fin number × Fin number

def ask {number : Nat} (input : Input number) (question : Question number) : Bool :=
  decide (input question.1 ≤ input question.2)

inductive Tree (number : Nat) where
  | leaf (order : Input number)
  | compare (question : Question number) (yes no : Tree number)

def evaluate {number : Nat} : Tree number → Input number → Input number
  | .leaf order, _ => order
  | .compare question yes no, input =>
      if ask input question then evaluate yes input else evaluate no input

def comparisons {number : Nat} : Tree number → Input number → Nat
  | .leaf _, _ => 0
  | .compare question yes no, input =>
      (if ask input question then comparisons yes input else comparisons no input) + 1

def height {number : Nat} : Tree number → Nat
  | .leaf _ => 0
  | .compare _ yes no => max (height yes) (height no) + 1

def leaves {number : Nat} : Tree number → List (Input number)
  | .leaf order => [order]
  | .compare _ yes no => leaves yes ++ leaves no

def Correct {number : Nat} (tree : Tree number) : Prop :=
  ∀ input, evaluate tree input = input.symm

theorem evaluate_mem_leaves {number : Nat} (tree : Tree number) (input : Input number) :
    evaluate tree input ∈ leaves tree := by
  induction tree with
  | leaf order => simp [evaluate, leaves]
  | compare question yes no ihYes ihNo =>
      unfold evaluate
      split
      · exact List.mem_append_left _ ihYes
      · exact List.mem_append_right _ ihNo

theorem comparisons_le_height {number : Nat} (tree : Tree number) (input : Input number) :
    comparisons tree input ≤ height tree := by
  induction tree with
  | leaf order => rfl
  | compare question yes no ihYes ihNo =>
      simp only [comparisons, height]
      split <;> omega

theorem leaf_count_le_power_height {number : Nat} (tree : Tree number) :
    (leaves tree).length ≤ 2 ^ height tree := by
  induction tree with
  | leaf order => rfl
  | compare question yes no ihYes ihNo =>
      have left := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left (height yes) (height no))
      have right := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right (height yes) (height no))
      simp only [leaves, height, List.length_append, pow_succ]
      omega

theorem factorial_le_leaves {number : Nat} (tree : Tree number) (correct : Correct tree) :
    number.factorial ≤ (leaves tree).length := by
  classical
  have cover : (Finset.univ : Finset (Input number)) ⊆ (leaves tree).toFinset := by
    intro order _
    have present := evaluate_mem_leaves tree order.symm
    rw [correct order.symm, Equiv.symm_symm] at present
    exact List.mem_toFinset.mpr present
  have size := Finset.card_le_card cover
  have bounded := List.toFinset_card_le (leaves tree)
  simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using size.trans bounded

def truncate {number : Nat} : Nat → Tree number → Tree number
  | _, .leaf order => .leaf order
  | 0, .compare _ _ _ => .leaf (Equiv.refl _)
  | bound + 1, .compare question yes no =>
      .compare question (truncate bound yes) (truncate bound no)

theorem truncate_height {number : Nat} (bound : Nat) (tree : Tree number) :
    height (truncate bound tree) ≤ bound := by
  induction bound generalizing tree with
  | zero => cases tree <;> simp [truncate, height]
  | succ bound ih =>
      cases tree with
      | leaf order => simp [truncate, height]
      | compare question yes no =>
          have left := ih yes
          have right := ih no
          simp only [truncate, height]
          omega

theorem truncate_evaluation {number : Nat} (bound : Nat) (tree : Tree number)
    (input : Input number) (within : comparisons tree input ≤ bound) :
    evaluate (truncate bound tree) input = evaluate tree input := by
  induction bound generalizing tree with
  | zero =>
      cases tree with
      | leaf order => rfl
      | compare question yes no => simp [comparisons] at within
  | succ bound ih =>
      cases tree with
      | leaf order => rfl
      | compare question yes no =>
          simp only [comparisons] at within
          simp only [truncate, evaluate]
          split <;> simp_all

theorem actual_work_cap_bounds_factorial {number : Nat} (tree : Tree number)
    (correct : Correct tree) (cap : Nat) (bounded : ∀ input, comparisons tree input ≤ cap) :
    number.factorial ≤ 2 ^ cap := by
  have truncatedCorrect : Correct (truncate cap tree) := by
    intro input
    exact (truncate_evaluation cap tree input (bounded input)).trans (correct input)
  calc number.factorial ≤ (leaves (truncate cap tree)).length := factorial_le_leaves _ truncatedCorrect
    _ ≤ 2 ^ height (truncate cap tree) := leaf_count_le_power_height _
    _ ≤ 2 ^ cap := Nat.pow_le_pow_right (by decide : 0 < 2) (truncate_height cap tree)

theorem some_input_exceeds_too_small_cap {number : Nat} (tree : Tree number)
    (correct : Correct tree) (cap : Nat) (small : 2 ^ cap < number.factorial) :
    ∃ input, cap < comparisons tree input := by
  by_contra! bounded
  have impossible := actual_work_cap_bounds_factorial tree correct cap bounded
  omega

theorem comparison_matrix_separates {number : Nat} (first second : Input number)
    (same : ∀ question, ask first question = ask second question) : first = second := by
  let change := first.symm.trans second
  have ordered : Monotone change := by
    intro left right below
    have compared := same (first.symm left, first.symm right)
    simp only [ask, Equiv.apply_symm_apply, decide_eq_decide] at compared
    exact compared.mp below
  have identity := (Equiv.Perm.monotone_iff change).mp ordered
  apply Equiv.ext
  intro index
  have sameValue := congrArg (fun permutation : Input number => permutation (first index)) identity
  simpa [change] using sameValue.symm

def build {number : Nat} : List (Question number) → List (Input number) → Tree number
  | [], [] => .leaf (Equiv.refl _)
  | [], first :: _ => .leaf first.symm
  | question :: rest, candidates =>
      .compare question
        (build rest (candidates.filter fun candidate => ask candidate question))
        (build rest (candidates.filter fun candidate => !ask candidate question))

theorem build_correct_on {number : Nat} (questions : List (Question number))
    (candidates : List (Input number)) (input : Input number) (present : input ∈ candidates)
    (separates : ∀ candidate ∈ candidates,
      (∀ question ∈ questions, ask candidate question = ask input question) → candidate = input) :
    evaluate (build questions candidates) input = input.symm := by
  induction questions generalizing candidates with
  | nil =>
      cases candidates with
      | nil => contradiction
      | cons first rest =>
          have same := separates first List.mem_cons_self (by simp)
          simp [build, evaluate, same]
  | cons question rest ih =>
      simp only [build, evaluate]
      cases decision : ask input question with
      | true =>
          simp only [↓reduceIte]
          apply ih
          · exact List.mem_filter.mpr ⟨present, decision⟩
          · intro candidate member agrees
            obtain ⟨inside, tested⟩ := List.mem_filter.mp member
            apply separates candidate inside
            intro asked inQuestions
            rcases List.mem_cons.mp inQuestions with rfl | later
            · exact tested.trans decision.symm
            · exact agrees asked later
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply ih
          · exact List.mem_filter.mpr ⟨present, by simp [decision]⟩
          · intro candidate member agrees
            obtain ⟨inside, tested⟩ := List.mem_filter.mp member
            apply separates candidate inside
            intro asked inQuestions
            rcases List.mem_cons.mp inQuestions with rfl | later
            · simpa [decision] using tested
            · exact agrees asked later

noncomputable def sortingTree (number : Nat) : Tree number :=
  build (Finset.univ : Finset (Question number)).toList
    (Finset.univ : Finset (Input number)).toList

theorem sortingTree_correct (number : Nat) : Correct (sortingTree number) := by
  classical
  intro input
  apply build_correct_on
  · simp
  · intro candidate _ agrees
    exact comparison_matrix_separates candidate input (fun question => agrees question (by simp))

theorem correct_tree_exists (number : Nat) : ∃ tree : Tree number, Correct tree :=
  ⟨sortingTree number, sortingTree_correct number⟩

theorem factorial_has_logarithmic_block (number : Nat) :
    2 ^ ((number / 2) * Nat.log 2 (number / 2 + 1)) ≤ number.factorial := by
  let half := number / 2
  have power : 2 ^ Nat.log 2 (half + 1) ≤ half + 1 := Nat.pow_log_le_self 2 (by omega)
  have raised := Nat.pow_le_pow_left power half
  have block := Nat.factorial_mul_pow_le_factorial (m := half) (n := half)
  have positive := Nat.factorial_pos half
  have monotone := Nat.factorial_le (show half + half ≤ number by dsimp [half]; omega)
  rw [← pow_mul, Nat.mul_comm] at raised
  calc 2 ^ ((number / 2) * Nat.log 2 (number / 2 + 1)) ≤ (half + 1) ^ half := raised
    _ ≤ half.factorial * (half + 1) ^ half := Nat.le_mul_of_pos_left _ positive
    _ ≤ (half + half).factorial := block
    _ ≤ number.factorial := monotone

theorem logarithmic_work_lower_bound {number : Nat} (tree : Tree number)
    (correct : Correct tree) :
    ∃ input, (number / 2) * Nat.log 2 (number / 2 + 1) ≤ comparisons tree input := by
  let lower := (number / 2) * Nat.log 2 (number / 2 + 1)
  by_cases zero : lower = 0
  · exact ⟨Equiv.refl _, by change lower ≤ _; omega⟩
  · have strict : 2 ^ (lower - 1) < number.factorial := by
      have growing := Nat.pow_lt_pow_right (by decide : 1 < 2) (show lower - 1 < lower by omega)
      exact growing.trans_le (factorial_has_logarithmic_block number)
    obtain ⟨input, expensive⟩ := some_input_exceeds_too_small_cap tree correct (lower - 1) strict
    exact ⟨input, by change lower ≤ _; omega⟩

end Mettapedia.Machines.OrderedRead.ComparisonLowerBound
