import Mettapedia.Computability.ProbabilisticTM
import Mettapedia.Computability.ProbabilisticTMRefined

/-!
# Where the bounded experiments fail

For the packed encoding of `ProbabilisticTM.lean`: one tape can give two
outputs, the two binary output events can overlap, and the diagonal of bounded
probabilities need not converge to the probability of the output.

For the prefix-stable encoding of `ProbabilisticTMRefined.lean`: a run is lost
when the prefix grows and the budget does not, every diagonal stage is empty,
and the constant machine has output probability one although its diagonal is
empty. The prefix law that lets the budget grow is satisfied by the constant
machine and fails for the projection code.
-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

namespace ProbabilisticTMBoundaryControls

/-- Increasing the prefix changes the output, even on a fixed tape. -/
theorem packed_prefix_two_outputs :
    PTMHaltsWithOutput Nat.Partrec.Code.right 0 (fun _ => true) 0 ∧
    PTMHaltsWithOutput Nat.Partrec.Code.right 0 (fun _ => true) 1 := by
  constructor
  · exact ⟨1, 0, by simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, Nat.pair]⟩
  · exact ⟨3, 1, by simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, List.finRange, show Nat.pair 0 1 ≤ 2 by norm_num [Nat.pair]]⟩

/-- The two binary output events actually overlap in the arbitrary-prefix model. -/
theorem packed_output_sets_not_disjoint :
    ¬ Disjoint (outputZeroSet Nat.Partrec.Code.right 0)
      (outputOneSet Nat.Partrec.Code.right 0) := by
  intro disjoint
  exact Set.disjoint_left.mp disjoint packed_prefix_two_outputs.1
    packed_prefix_two_outputs.2

/-- Successful diagonal experiments can disappear at the next stage. -/
theorem packed_diagonal_not_monotone :
    ¬ Monotone (fun n => {r : CantorSpace |
      runPTMBounded Nat.Partrec.Code.right 0 r n n = some 1}) := by
  intro monotone
  have atThree : runPTMBounded Nat.Partrec.Code.right 0 (fun i => i == 2) 3 3 = some 1 := by
    simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, List.finRange,
      show Nat.pair 0 1 ≤ 2 by norm_num [Nat.pair]]
  have atFour : runPTMBounded Nat.Partrec.Code.right 0 (fun i => i == 2) 4 4 = none := by
    simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, List.finRange, Nat.pair]
  have persisted := monotone (by omega : 3 ≤ 4) atThree
  change runPTMBounded Nat.Partrec.Code.right 0 (fun i => i == 2) 4 4 = some 1 at persisted
  rw [atFour] at persisted
  contradiction

end ProbabilisticTMBoundaryControls

private theorem fold_bits_zero {α : Type*} (r : α → Bool) (l : List α) (acc : ℕ) :
    l.foldl (fun a i => a * 2 + if r i then 1 else 0) acc = 0 ↔
      acc = 0 ∧ ∀ i ∈ l, r i = false := by
  induction l generalizing acc with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, forall_eq_or_imp]
    cases r head <;> simp

theorem encodeRandomBits_eq_zero_iff (r : CantorSpace) (bits : ℕ) :
    encodeRandomBits r bits = 0 ↔ ∀ i : Fin bits, r i = false := by
  simp [encodeRandomBits, fold_bits_zero]

private theorem pair_zero_iff (a b : ℕ) : Nat.pair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro eq
    have ha := Nat.left_le_pair a b
    have hb := Nat.right_le_pair a b
    rw [eq] at ha hb
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    simp [Nat.pair]

/-- The original diagonal for successor succeeds exactly on all-zero prefixes. -/
theorem successor_output_one_iff (r : CantorSpace) (fuel bits : ℕ) :
    runPTMBounded Nat.Partrec.Code.succ 0 r fuel bits = some 1 ↔
      0 < fuel ∧ ∀ i : Fin bits, r i = false := by
  cases fuel with
  | zero => simp [runPTMBounded, Nat.Partrec.Code.evaln]
  | succ f =>
    simp [runPTMBounded, Nat.Partrec.Code.evaln, Option.bind_eq_some_iff,
      pair_zero_iff, encodeRandomBits_eq_zero_iff]
    intro zeroes
    have encoded := (encodeRandomBits_eq_zero_iff r bits).mpr zeroes
    simp [encoded, Nat.pair]

namespace ProbabilisticTMBoundaryControls

/-- Every tape is accepted at the empty prefix by the successor code. -/
theorem successor_outputProb_eq_one : outputProb Nat.Partrec.Code.succ 0 = 1 := by
  have all : outputOneSet Nat.Partrec.Code.succ 0 = Set.univ := by
    ext r
    simp only [outputOneSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨1, 0, by simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, Nat.pair]⟩
  simp [outputProb, all]

/-- Every positive diagonal stage has probability exactly two to the minus stage. -/
theorem successor_boundedOutputProb (n : ℕ) (positive : 0 < n) :
    boundedOutputProb Nat.Partrec.Code.succ 0 n n = (1 / 2 : ℝ≥0∞) ^ n := by
  have setEq : {r : CantorSpace | runPTMBounded Nat.Partrec.Code.succ 0 r n n = some 1} =
      cylinderSet n (fun _ => false) := by
    ext r
    simp only [Set.mem_ofPred_eq, successor_output_one_iff, positive, true_and, cylinderSet]
  unfold boundedOutputProb
  rw [setEq, coinMeasure_cylinderSet]

/-- The actual diagonal converges to zero, although the existing total event has measure one. -/
theorem successor_diagonal_tendsto_zero :
    Tendsto (fun n => boundedOutputProb Nat.Partrec.Code.succ 0 n n) atTop (nhds 0) := by
  apply (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1)).congr'
  filter_upwards [eventually_gt_atTop 0] with n positive
  exact (successor_boundedOutputProb n positive).symm

/-- The diagonal of bounded probabilities does not converge to the output
probability in general: for the successor code it tends to 0 while the output
probability is 1. -/
theorem diagonal_convergence_fails :
    ¬ Tendsto (fun n => boundedOutputProb Nat.Partrec.Code.succ 0 n n) atTop
      (nhds (outputProb Nat.Partrec.Code.succ 0)) := by
  intro claimed
  have one : Tendsto (fun n => boundedOutputProb Nat.Partrec.Code.succ 0 n n) atTop (nhds 1) := by
    simpa only [successor_outputProb_eq_one] using claimed
  exact zero_ne_one (tendsto_nhds_unique successor_diagonal_tendsto_zero one)

end ProbabilisticTMBoundaryControls

/-! ## The prefix-stable encoding -/

namespace RefinedBoundaryControls

/-- A halting run is lost when the prefix grows and the budget does not. -/
theorem run_lost_at_fixed_budget (M : PTMIndexR) (x : ℕ) (r : CantorSpace)
    (fuel numBits : ℕ) : runPTMR M x r fuel (max numBits fuel) = none :=
  runPTMR_eq_none_of_fuel_le M x r (le_max_right _ _)

/-- Every diagonal stage, budget `stage` and `stage` bits, is empty. -/
theorem diagonal_empty (M : PTMIndexR) (x stage output : ℕ) :
    {r : CantorSpace | runPTMR M x r stage stage = some output} = ∅ := by
  ext r
  simp [runPTMR_eq_none_of_fuel_le M x r (le_refl stage)]

/-- The constant machine halts with 1 on every tape and every prefix. -/
theorem constantOne_halts (x : ℕ) (r : CantorSpace) (numBits : ℕ) :
    ∃ fuel, runPTMR constantOne x r fuel numBits = some 1 :=
  constantOne_evaln_complete _

/-- A machine that halts satisfies the prefix law. -/
theorem constantOne_prefixMonotone : IsPrefixMonotone constantOne := by
  intro x r fuel numBits more output _ halted
  obtain rfl : output = 1 := constantOne_evaln_sound halted
  exact constantOne_halts x r more

theorem constantOne_outputProbR (x : ℕ) : outputProbR constantOne x = 1 := by
  have all : outputOneSetR constantOne x = Set.univ := by
    ext r
    simp only [outputOneSetR, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨fuel, halted⟩ := constantOne_halts x r 0
    exact ⟨fuel, 0, halted⟩
  simp [outputProbR, all]

/-- The stage probabilities of the constant machine converge to one, although
each of its diagonal stages is empty. -/
theorem constantOne_stage_tendsto_one (x : ℕ) :
    Tendsto (fun stage => stageOutputProbR constantOne x stage) atTop (nhds 1) := by
  simpa only [constantOne_outputProbR] using stageOutputProbR_tendsto constantOne x

/-- The projection code is not prefix-monotone: its output is the encoded
prefix, which changes with the prefix. -/
theorem right_not_prefixMonotone : ¬ IsPrefixMonotone Nat.Partrec.Code.right := by
  intro monotone
  have atZero : runPTMR Nat.Partrec.Code.right 0 (fun _ => false) 1 0 = some 0 := by
    simp [runPTMR, prefixEncode, Nat.Partrec.Code.evaln, Nat.pair]
  obtain ⟨budget, later⟩ := monotone 0 (fun _ => false) 1 0 1 0 (Nat.zero_le 1) atZero
  have value : 0 = Nat.pair (prefixEncode (fun _ => false) 1) 1 := by
    simpa [Nat.Partrec.Code.eval] using Nat.Partrec.Code.evaln_sound later
  have bound := Nat.right_le_pair (prefixEncode (fun _ => false) 1) 1
  omega

end RefinedBoundaryControls

end Mettapedia.Computability
