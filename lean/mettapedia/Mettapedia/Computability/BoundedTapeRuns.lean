import Mettapedia.Computability.CantorSpace

/-!
# Runs bounded by a budget and by the tape prefix offered

A probabilistic machine is run with a budget of steps and with a finite prefix
of its random tape. The event that it gives an output is the set of tapes on
which some budget and some prefix give that output.

This module is about any such family of runs.

* The event is the increasing union of its stages: the tapes on which some
  budget and some prefix, both at most the stage, give the output. This needs
  no stability of the machine (`tendsto_measure_stageSet`).
* When a run reads only the prefix it is offered, a stage is a finite union of
  cylinders. Its probability is an explicit rational number, the count of
  accepted prefixes over a power of two, and these numbers increase to the
  probability of the event (`approximated_from_below`).
* A family of runs is prefix-monotone when an output obtained from a prefix is
  obtained from every longer prefix, given enough budget. Then one tape never
  gives two outputs (`output_unique`), the events of different outputs are
  disjoint and their probabilities sum to at most one
  (`coinMeasure_outputSet_add_le_one`), and the event is also the increasing
  union over the prefix length alone (`tendsto_measure_prefixSet`).

In the prefix law the budget is allowed to grow with the prefix. An encoded
prefix grows with its length and a bounded evaluator needs a budget above its
input, so a law that fixes the budget is satisfied by no halting run; the
modules of the machines prove this for their encodings.
-/

set_option autoImplicit false

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-- A family of runs of a machine on a random tape, indexed by a budget of
steps and by the number of tape bits offered. -/
abbrev BoundedRun := CantorSpace → ℕ → ℕ → Option ℕ

/-- Complete a finite prefix with zeros. -/
def completeTape {length : ℕ} (bits : Fin length → Bool) : CantorSpace :=
  fun index => if within : index < length then bits ⟨index, within⟩ else false

namespace BoundedRun

variable (run : BoundedRun)

/-- Some budget and some prefix give the output. -/
def HaltsWith (r : CantorSpace) (output : ℕ) : Prop :=
  ∃ fuel numBits, run r fuel numBits = some output

/-- The tapes on which the output is obtained. -/
def outputSet (output : ℕ) : Set CantorSpace := {r | run.HaltsWith r output}

/-- The tapes on which the output is obtained with budget and prefix at most
the stage. -/
def stageSet (output stage : ℕ) : Set CantorSpace :=
  {r | ∃ fuel ≤ stage, ∃ numBits ≤ stage, run r fuel numBits = some output}

/-! ## Stages -/

theorem stageSet_monotone (output : ℕ) : Monotone (run.stageSet output) := by
  rintro lower upper bound r ⟨fuel, fuelBound, numBits, bitsBound, halted⟩
  exact ⟨fuel, fuelBound.trans bound, numBits, bitsBound.trans bound, halted⟩

theorem stageSet_subset_outputSet (output stage : ℕ) :
    run.stageSet output stage ⊆ run.outputSet output := by
  rintro r ⟨fuel, -, numBits, -, halted⟩
  exact ⟨fuel, numBits, halted⟩

/-- The stages exhaust the event. -/
theorem iUnion_stageSet (output : ℕ) :
    (⋃ stage, run.stageSet output stage) = run.outputSet output := by
  ext r
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨stage, member⟩
    exact run.stageSet_subset_outputSet output stage member
  · rintro ⟨fuel, numBits, halted⟩
    exact ⟨max fuel numBits, fuel, le_max_left _ _, numBits, le_max_right _ _, halted⟩

/-- **The probabilities of the stages converge to the probability of the
event**, for every family of runs and every measure. -/
theorem tendsto_measure_stageSet (μ : Measure CantorSpace) (output : ℕ) :
    Tendsto (fun stage => μ (run.stageSet output stage)) atTop
      (nhds (μ (run.outputSet output))) := by
  rw [← run.iUnion_stageSet output]
  exact tendsto_measure_iUnion_atTop (run.stageSet_monotone output)

/-! ## Runs that read only the prefix offered -/

/-- A run reads only the prefix it is offered. -/
def ReadsPrefix : Prop :=
  ∀ (first second : CantorSpace) (fuel numBits : ℕ),
    (∀ index, index < numBits → first index = second index) →
      run first fuel numBits = run second fuel numBits

/-- A finite, executable test of a stage on one prefix. -/
def accepts (output stage : ℕ) (bits : Fin stage → Bool) : Bool :=
  (List.range (stage + 1)).any fun fuel =>
    (List.range (stage + 1)).any fun numBits =>
      run (completeTape bits) fuel numBits == some output

theorem accepts_iff (output stage : ℕ) (bits : Fin stage → Bool) :
    run.accepts output stage bits = true ↔ completeTape bits ∈ run.stageSet output stage := by
  simp [accepts, stageSet, List.any_eq_true, List.mem_range]

variable {run}

/-- A run with a prefix within the stage is a run on the completed prefix of
the stage. -/
theorem ReadsPrefix.run_completeTape (reads : run.ReadsPrefix) (r : CantorSpace)
    (fuel numBits stage : ℕ) (bounded : numBits ≤ stage) :
    run (completeTape (prefixProj stage r)) fuel numBits = run r fuel numBits := by
  apply reads
  intro index within
  simp [completeTape, prefixProj, lt_of_lt_of_le within bounded]

/-- A stage is an event of the prefix of its length. -/
theorem ReadsPrefix.stageSet_eq_preimage (reads : run.ReadsPrefix) (output stage : ℕ) :
    run.stageSet output stage =
      prefixProj stage ⁻¹' {bits | run.accepts output stage bits = true} := by
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, accepts_iff, stageSet]
  constructor
  · rintro ⟨fuel, fuelBound, numBits, bitsBound, halted⟩
    exact ⟨fuel, fuelBound, numBits, bitsBound,
      (reads.run_completeTape r fuel numBits stage bitsBound).trans halted⟩
  · rintro ⟨fuel, fuelBound, numBits, bitsBound, halted⟩
    exact ⟨fuel, fuelBound, numBits, bitsBound,
      (reads.run_completeTape r fuel numBits stage bitsBound).symm.trans halted⟩

theorem ReadsPrefix.measurableSet_stageSet (reads : run.ReadsPrefix) (output stage : ℕ) :
    MeasurableSet (run.stageSet output stage) := by
  rw [reads.stageSet_eq_preimage]
  exact prefixProj_measurable stage (MeasurableSet.of_discrete)

theorem ReadsPrefix.measurableSet_outputSet (reads : run.ReadsPrefix) (output : ℕ) :
    MeasurableSet (run.outputSet output) := by
  rw [← run.iUnion_stageSet output]
  exact MeasurableSet.iUnion fun stage => reads.measurableSet_stageSet output stage

variable (run)

/-- The prefixes of the stage's length that the stage accepts. -/
def acceptedPrefixes (output stage : ℕ) : Finset (Fin stage → Bool) :=
  Finset.univ.filter fun bits => run.accepts output stage bits = true

/-- How many prefixes the stage accepts. -/
def numerator (output stage : ℕ) : ℕ := (run.acceptedPrefixes output stage).card

/-- The probability of the stage as an executable rational number. -/
def fraction (output stage : ℕ) : ℚ := run.numerator output stage / (2 : ℚ) ^ stage

theorem fraction_nonneg (output stage : ℕ) : 0 ≤ run.fraction output stage :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

variable {run}

/-- A stage is the finite union of the cylinders of its accepted prefixes. -/
theorem ReadsPrefix.stageSet_eq_cylinders (reads : run.ReadsPrefix) (output stage : ℕ) :
    run.stageSet output stage =
      ⋃ bits ∈ run.acceptedPrefixes output stage, cylinderSet stage bits := by
  rw [reads.stageSet_eq_preimage]
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion,
    acceptedPrefixes, Finset.mem_filter, Finset.mem_univ, true_and, cylinderSet]
  constructor
  · intro accepted
    exact ⟨prefixProj stage r, accepted, fun _ => rfl⟩
  · rintro ⟨bits, accepted, same⟩
    have equal : prefixProj stage r = bits := funext same
    exact equal ▸ accepted

/-- The count of accepted prefixes gives the probability of the stage. -/
theorem ReadsPrefix.coinMeasure_stageSet_eq_count (reads : run.ReadsPrefix)
    (output stage : ℕ) :
    coinMeasure (run.stageSet output stage) =
      (run.numerator output stage : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ stage := by
  rw [reads.stageSet_eq_cylinders]
  have disjoint : Set.PairwiseDisjoint (↑(run.acceptedPrefixes output stage))
      (cylinderSet stage) := by
    intro first _ second _ different
    apply Set.disjoint_left.mpr
    intro r inFirst inSecond
    apply different
    exact funext fun index => (inFirst index).symm.trans (inSecond index)
  rw [measure_biUnion_finset disjoint (fun bits _ => cylinderSet_measurable stage bits)]
  simp [coinMeasure_cylinderSet, Finset.sum_const, numerator, nsmul_eq_mul]

/-- The executable rational number is the probability of the stage. -/
theorem ReadsPrefix.coinMeasure_stageSet_eq_fraction (reads : run.ReadsPrefix)
    (output stage : ℕ) :
    coinMeasure (run.stageSet output stage) =
      ENNReal.ofReal (run.fraction output stage : ℝ) := by
  rw [reads.coinMeasure_stageSet_eq_count]
  simp only [fraction, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  rw [ENNReal.ofReal_div_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat]
  simp only [div_eq_mul_inv, one_mul, ENNReal.inv_pow]

theorem ReadsPrefix.fraction_tendsto (reads : run.ReadsPrefix) (output : ℕ) :
    Tendsto (fun stage => ENNReal.ofReal (run.fraction output stage : ℝ)) atTop
      (nhds (coinMeasure (run.outputSet output))) := by
  simpa only [reads.coinMeasure_stageSet_eq_fraction] using
    run.tendsto_measure_stageSet coinMeasure output

theorem ReadsPrefix.fraction_monotone (reads : run.ReadsPrefix) (output : ℕ) :
    Monotone (run.fraction output) := by
  intro lower upper bound
  have upperNonneg : (0 : ℝ) ≤ (run.fraction output upper : ℝ) :=
    Rat.cast_nonneg.mpr (run.fraction_nonneg output upper)
  have interpreted : ENNReal.ofReal (run.fraction output lower : ℝ) ≤
      ENNReal.ofReal (run.fraction output upper : ℝ) := by
    rw [← reads.coinMeasure_stageSet_eq_fraction, ← reads.coinMeasure_stageSet_eq_fraction]
    exact measure_mono (run.stageSet_monotone output bound)
  have ordered := (ENNReal.ofReal_le_ofReal_iff upperNonneg).mp interpreted
  exact_mod_cast ordered

/-- **Approximation of the probability of an output from below.** The rational
counts of accepted prefixes increase with the stage, never exceed the
probability of the event, and converge to it. -/
theorem ReadsPrefix.approximated_from_below (reads : run.ReadsPrefix) (output : ℕ) :
    Monotone (run.fraction output) ∧
      (∀ stage, ENNReal.ofReal (run.fraction output stage : ℝ) ≤
        coinMeasure (run.outputSet output)) ∧
      Tendsto (fun stage => ENNReal.ofReal (run.fraction output stage : ℝ)) atTop
        (nhds (coinMeasure (run.outputSet output))) :=
  ⟨reads.fraction_monotone output,
    fun stage => (reads.coinMeasure_stageSet_eq_fraction output stage) ▸
      measure_mono (run.stageSet_subset_outputSet output stage),
    reads.fraction_tendsto output⟩

/-! ## The prefix law -/

variable (run)

/-- More budget never loses an output. -/
def FuelMonotone : Prop :=
  ∀ (r : CantorSpace) (numBits fuel more output : ℕ), fuel ≤ more →
    run r fuel numBits = some output → run r more numBits = some output

/-- An output obtained from a prefix is obtained from every longer prefix,
given enough budget. -/
def PrefixMonotone : Prop :=
  ∀ (r : CantorSpace) (fuel numBits more output : ℕ), numBits ≤ more →
    run r fuel numBits = some output → ∃ budget, run r budget more = some output

/-- The tapes on which some budget gives the output from the prefix of the
given length. -/
def prefixSet (output numBits : ℕ) : Set CantorSpace :=
  {r | ∃ fuel, run r fuel numBits = some output}

theorem iUnion_prefixSet (output : ℕ) :
    (⋃ numBits, run.prefixSet output numBits) = run.outputSet output := by
  ext r
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨numBits, fuel, halted⟩
    exact ⟨fuel, numBits, halted⟩
  · rintro ⟨fuel, numBits, halted⟩
    exact ⟨numBits, fuel, halted⟩

variable {run}

/-- **Under the two laws a tape gives at most one output.** -/
theorem output_unique (fuelMonotone : run.FuelMonotone) (prefixMonotone : run.PrefixMonotone)
    {r : CantorSpace} {first second : ℕ}
    (haltsFirst : run.HaltsWith r first) (haltsSecond : run.HaltsWith r second) :
    first = second := by
  obtain ⟨fuelFirst, bitsFirst, runFirst⟩ := haltsFirst
  obtain ⟨fuelSecond, bitsSecond, runSecond⟩ := haltsSecond
  obtain ⟨budgetFirst, laterFirst⟩ := prefixMonotone r fuelFirst bitsFirst
    (max bitsFirst bitsSecond) first (le_max_left _ _) runFirst
  obtain ⟨budgetSecond, laterSecond⟩ := prefixMonotone r fuelSecond bitsSecond
    (max bitsFirst bitsSecond) second (le_max_right _ _) runSecond
  have one := fuelMonotone r _ budgetFirst (max budgetFirst budgetSecond) first
    (le_max_left _ _) laterFirst
  have other := fuelMonotone r _ budgetSecond (max budgetFirst budgetSecond) second
    (le_max_right _ _) laterSecond
  exact Option.some.inj (one.symm.trans other)

theorem disjoint_outputSet (fuelMonotone : run.FuelMonotone)
    (prefixMonotone : run.PrefixMonotone) {first second : ℕ} (different : first ≠ second) :
    Disjoint (run.outputSet first) (run.outputSet second) :=
  Set.disjoint_left.mpr fun _ haltsFirst haltsSecond =>
    different (output_unique fuelMonotone prefixMonotone haltsFirst haltsSecond)

/-- **Under the two laws the probabilities of two different outputs sum to at
most one.** -/
theorem coinMeasure_outputSet_add_le_one (reads : run.ReadsPrefix)
    (fuelMonotone : run.FuelMonotone) (prefixMonotone : run.PrefixMonotone)
    {first second : ℕ} (different : first ≠ second) :
    coinMeasure (run.outputSet first) + coinMeasure (run.outputSet second) ≤ 1 := by
  rw [← measure_union (disjoint_outputSet fuelMonotone prefixMonotone different)
    (reads.measurableSet_outputSet second)]
  exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ

theorem PrefixMonotone.prefixSet_monotone (prefixMonotone : run.PrefixMonotone) (output : ℕ) :
    Monotone (run.prefixSet output) := by
  rintro lower upper bound r ⟨fuel, halted⟩
  exact prefixMonotone r fuel lower upper output bound halted

/-- Under the prefix law the event is approached through the prefix length
alone. -/
theorem PrefixMonotone.tendsto_measure_prefixSet (prefixMonotone : run.PrefixMonotone)
    (μ : Measure CantorSpace) (output : ℕ) :
    Tendsto (fun numBits => μ (run.prefixSet output numBits)) atTop
      (nhds (μ (run.outputSet output))) := by
  rw [← run.iUnion_prefixSet output]
  exact tendsto_measure_iUnion_atTop (prefixMonotone.prefixSet_monotone output)

end BoundedRun

end Mettapedia.Computability
