import Mettapedia.Computability.ProbabilisticTMBoundary
import Mettapedia.Computability.ProbabilisticPrefixExperiment

/-!
# Semantic prefix consistency

A halting prefix result persists under extension with a possibly larger evaluator
budget. This property permits genuine halting codes and establishes unique outputs
and the binary semimeasure bound. It does not represent a sequential random-tape
instruction set or prove reflective-oracle existence.

Halting at some budget is membership in the partial function computed by the code
(`exists_fuel_run_iff`), so the property is a condition on that partial function
(`prefixConsistent_iff_eval`). The positive controls are the constant-zero code and
a code that reads the tape: it outputs 1 once the prefix contains a one-bit and
diverges on the all-zero tape (`exists_tape_reading_prefixConsistent`).
-/

open MeasureTheory
open scoped ENNReal

namespace Mettapedia.Computability

/-- A result already obtained from a prefix persists under prefix extension,
    allowing the evaluator budget to increase with its encoded input: the
    runs of the code are prefix-monotone on every input. -/
def PrefixConsistent (M : PTMIndex) : Prop := ∀ x, (ptmRun M x).PrefixMonotone

/-- Halting at some budget is membership in the partial function of the code. -/
theorem exists_fuel_run_iff (M : PTMIndex) (x : ℕ) (r : CantorSpace) (bits output : ℕ) :
    (∃ fuel, runPTMBounded M x r fuel bits = some output) ↔
      output ∈ Nat.Partrec.Code.eval M (Nat.pair x (encodeRandomBits r bits)) :=
  Nat.Partrec.Code.evaln_complete.symm

/-- Prefix consistency is a condition on the partial function computed by the
code: a value obtained on a packed prefix is obtained on every longer one. -/
theorem prefixConsistent_iff_eval (M : PTMIndex) :
    PrefixConsistent M ↔ ∀ (x : ℕ) (r : CantorSpace) (bits more output : ℕ), bits ≤ more →
      output ∈ Nat.Partrec.Code.eval M (Nat.pair x (encodeRandomBits r bits)) →
      output ∈ Nat.Partrec.Code.eval M (Nat.pair x (encodeRandomBits r more)) := by
  constructor
  · intro consistent x r bits more output bound member
    obtain ⟨fuel, halted⟩ := (exists_fuel_run_iff M x r bits output).mpr member
    exact (exists_fuel_run_iff M x r more output).mp
      (consistent x r fuel bits more output bound halted)
  · intro stable x r fuel bits more output bound halted
    exact (exists_fuel_run_iff M x r more output).mpr
      (stable x r bits more output bound
        ((exists_fuel_run_iff M x r bits output).mp ⟨fuel, halted⟩))

/-- The evaluator is deterministic at a fixed encoded prefix. -/
theorem prefix_output_unique (M : PTMIndex) (x : ℕ) (r : CantorSpace)
    (bits first second : ℕ)
    (haltsFirst : ∃ fuel, runPTMBounded M x r fuel bits = some first)
    (haltsSecond : ∃ fuel, runPTMBounded M x r fuel bits = some second) :
    first = second := by
  obtain ⟨fuelFirst, hFirst⟩ := haltsFirst
  obtain ⟨fuelSecond, hSecond⟩ := haltsSecond
  have f : runPTMBounded M x r (max fuelFirst fuelSecond) bits = some first :=
    Nat.Partrec.Code.evaln_mono (le_max_left _ _) hFirst
  have s : runPTMBounded M x r (max fuelFirst fuelSecond) bits = some second :=
    Nat.Partrec.Code.evaln_mono (le_max_right _ _) hSecond
  exact Option.some.inj (f.symm.trans s)

/-- Semantic prefix consistency gives one output per tape, even when the
    two witnesses use different prefixes and budgets. -/
theorem PrefixConsistent.output_unique {M : PTMIndex} (consistent : PrefixConsistent M)
    (x : ℕ) (r : CantorSpace) (first second : ℕ)
    (haltsFirst : PTMHaltsWithOutput M x r first)
    (haltsSecond : PTMHaltsWithOutput M x r second) : first = second :=
  BoundedRun.output_unique (ptmRun_fuelMonotone M x) (consistent x) haltsFirst haltsSecond

/-- Distinct output events are disjoint under the actual nonvacuous consistency law. -/
theorem PrefixConsistent.output_events_disjoint {M : PTMIndex}
    (consistent : PrefixConsistent M) (x first second : ℕ) (different : first ≠ second) :
    Disjoint {r | PTMHaltsWithOutput M x r first}
      {r | PTMHaltsWithOutput M x r second} :=
  BoundedRun.disjoint_outputSet (ptmRun_fuelMonotone M x) (consistent x) different

/-- Constant zero actually halts at every input and prefix. -/
theorem zeroCode_halts_prefix (x : ℕ) (r : CantorSpace) (bits : ℕ) :
    ∃ fuel, runPTMBounded Nat.Partrec.Code.zero x r fuel bits = some 0 := by
  refine ⟨Nat.pair x (encodeRandomBits r bits) + 1, ?_⟩
  simp [runPTMBounded, Nat.Partrec.Code.evaln]

/-- A genuine halting code satisfies semantic prefix consistency. -/
theorem zeroCode_prefixConsistent : PrefixConsistent Nat.Partrec.Code.zero := by
  intro x r fuel bits more output _ halted
  have outputEq : output = 0 :=
    prefix_output_unique Nat.Partrec.Code.zero x r bits output 0 ⟨fuel, halted⟩
      (zeroCode_halts_prefix x r bits)
  subst output
  exact zeroCode_halts_prefix x r more

/-- The positive control is nonvacuous on every tape and input. -/
theorem zeroCode_halts (x : ℕ) (r : CantorSpace) :
    PTMHaltsWithOutput Nat.Partrec.Code.zero x r 0 := by
  obtain ⟨fuel, halted⟩ := zeroCode_halts_prefix x r 0
  exact ⟨fuel, 0, halted⟩

/-- The arbitrary packed-prefix projection does not satisfy consistency. -/
theorem rightCode_not_prefixConsistent : ¬ PrefixConsistent Nat.Partrec.Code.right := by
  intro consistent
  obtain ⟨zeroRun, oneRun⟩ := ProbabilisticTMBoundaryControls.packed_prefix_two_outputs
  have contradiction := consistent.output_unique 0 (fun _ => true) 0 1 zeroRun oneRun
  simp at contradiction

/-- Consistency restores the binary semimeasure bound, allowing divergence. -/
theorem PrefixConsistent.binary_probability_le_one {M : PTMIndex}
    (consistent : PrefixConsistent M) (x : ℕ) :
    outputProb M x + outputProbZero M x ≤ 1 :=
  BoundedRun.coinMeasure_outputSet_add_le_one (ptmRun_readsPrefix M x)
    (ptmRun_fuelMonotone M x) (consistent x) (by decide)

/-- Without prefix consistency the binary bound fails: for the projection code
the one-output and zero-output events together have measure above one. -/
theorem rightCode_binary_probability_gt_one :
    1 < outputProb Nat.Partrec.Code.right 0 + outputProbZero Nat.Partrec.Code.right 0 := by
  have zeroAll : outputZeroSet Nat.Partrec.Code.right 0 = Set.univ := by
    ext r
    simp only [outputZeroSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨1, 0, by simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, Nat.pair]⟩
  have zeroOne : outputProbZero Nat.Partrec.Code.right 0 = 1 := by
    simp [outputProbZero, zeroAll]
  have subset : cylinderSet 1 (fun _ => true) ⊆ outputOneSet Nat.Partrec.Code.right 0 := by
    intro r member
    have first : r 0 = true := member ⟨0, Nat.zero_lt_one⟩
    exact ⟨3, 1, by
      simp [runPTMBounded, encodeRandomBits, Nat.Partrec.Code.evaln, List.finRange, first,
        show Nat.pair 0 1 ≤ 2 by norm_num [Nat.pair]]⟩
  have oneHalf : (1 / 2 : ℝ≥0∞) ≤ outputProb Nat.Partrec.Code.right 0 := by
    have measured := measure_mono (μ := coinMeasure) subset
    rwa [coinMeasure_cylinderSet, pow_one] at measured
  rw [zeroOne]
  calc (1 : ℝ≥0∞) < 1 / 2 + 1 := by
        rw [add_comm]
        exact ENNReal.lt_add_right ENNReal.one_ne_top (by norm_num)
    _ ≤ outputProb Nat.Partrec.Code.right 0 + 1 := by gcongr

/-- The constant-zero positive control has full zero-output probability. -/
theorem zeroCode_outputProbZero_eq_one (x : ℕ) :
    outputProbZero Nat.Partrec.Code.zero x = 1 := by
  have all : outputZeroSet Nat.Partrec.Code.zero x = Set.univ := by
    ext r
    simp only [outputZeroSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact zeroCode_halts x r
  simp [outputProbZero, all]

/-- It has no one-output probability, by actual output uniqueness. -/
theorem zeroCode_outputProb_eq_zero (x : ℕ) : outputProb Nat.Partrec.Code.zero x = 0 := by
  have empty : outputOneSet Nat.Partrec.Code.zero x = ∅ := by
    ext r
    simp only [outputOneSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro one
    have impossible := zeroCode_prefixConsistent.output_unique x r 1 0 one (zeroCode_halts x r)
    contradiction
  simp [outputProb, empty]

/-! ## A prefix-consistent code that reads the tape -/

/-- Return 1 once the packed prefix is nonzero; diverge on a zero prefix. -/
def sawOne : ℕ →. ℕ := fun n => Nat.rfindOpt fun _ => if n.unpair.2 = 0 then none else some 1

theorem mem_sawOne {n output : ℕ} : output ∈ sawOne n ↔ n.unpair.2 ≠ 0 ∧ output = 1 := by
  unfold sawOne
  rw [Nat.rfindOpt_mono (fun _ h => h)]
  by_cases zero : n.unpair.2 = 0 <;> simp [zero, eq_comm]

theorem sawOne_partrec : Nat.Partrec sawOne := by
  apply Partrec.nat_iff.1
  apply Partrec.rfindOpt
  exact (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.const 0)) (Primrec.const none) (Primrec.const (some 1))).to_comp

/-- A packed prefix is nonzero exactly when it contains a one-bit. -/
theorem encodeRandomBits_ne_zero_iff (r : CantorSpace) (bits : ℕ) :
    encodeRandomBits r bits ≠ 0 ↔ ∃ i, i < bits ∧ r i = true := by
  rw [Ne, encodeRandomBits_eq_zero_iff]
  constructor
  · intro notAll
    by_contra none
    exact notAll fun i => by
      cases value : r i with
      | false => rfl
      | true => exact (none ⟨i, i.isLt, value⟩).elim
  · rintro ⟨i, bound, one⟩ all
    have zero := all ⟨i, bound⟩
    rw [one] at zero
    cases zero

/-- **Prefix consistency admits a code that reads the tape.** Some
prefix-consistent code outputs 1 exactly on the tapes containing a one-bit and
has no output on the all-zero tape. -/
theorem exists_tape_reading_prefixConsistent :
    ∃ M : PTMIndex, PrefixConsistent M ∧
      (∀ (x : ℕ) (r : CantorSpace), PTMHaltsWithOutput M x r 1 ↔ ∃ i, r i = true) ∧
      ∀ x output : ℕ, ¬PTMHaltsWithOutput M x (fun _ => false) output := by
  obtain ⟨M, evalM⟩ := Nat.Partrec.Code.exists_code.1 sawOne_partrec
  have halts : ∀ (x : ℕ) (r : CantorSpace) (bits output : ℕ),
      (∃ fuel, runPTMBounded M x r fuel bits = some output) ↔
        (∃ i, i < bits ∧ r i = true) ∧ output = 1 := by
    intro x r bits output
    rw [exists_fuel_run_iff, evalM, mem_sawOne, Nat.unpair_pair, encodeRandomBits_ne_zero_iff]
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x r fuel bits more output bound halted
    obtain ⟨⟨i, small, one⟩, value⟩ := (halts x r bits output).1 ⟨fuel, halted⟩
    exact (halts x r more output).2 ⟨⟨i, small.trans_le bound, one⟩, value⟩
  · intro x r
    constructor
    · rintro ⟨fuel, bits, halted⟩
      obtain ⟨⟨i, _, one⟩, _⟩ := (halts x r bits 1).1 ⟨fuel, halted⟩
      exact ⟨i, one⟩
    · rintro ⟨i, one⟩
      obtain ⟨fuel, halted⟩ := (halts x r (i + 1) 1).2 ⟨⟨i, Nat.lt_succ_self i, one⟩, rfl⟩
      exact ⟨fuel, i + 1, halted⟩
  · rintro x output ⟨fuel, bits, halted⟩
    obtain ⟨⟨_, _, one⟩, _⟩ := (halts x (fun _ => false) bits output).1 ⟨fuel, halted⟩
    cases one

end Mettapedia.Computability
