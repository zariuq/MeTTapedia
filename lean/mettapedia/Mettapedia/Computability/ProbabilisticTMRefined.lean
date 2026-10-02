import Mettapedia.Computability.BoundedTapeRuns
import Mathlib.Computability.PartrecCode

/-!
# Probabilistic machines on a prefix-stable encoding of the tape

In `ProbabilisticTM.lean` the first bits of the tape are packed into one
binary number, so offering one more bit changes the whole encoded input:

```
encodeRandomBits [1,0,1,...] 2 = 2
encodeRandomBits [1,0,1,...] 3 = 5
```

Here a prefix is encoded by nested pairs with the newest bit outermost, so
the encoding of a shorter prefix can be read off the encoding of a longer
one. The machine receives its input, the encoded prefix and the length of the
prefix.

The runs of a machine form a family bounded by a budget and by the prefix
offered (`BoundedTapeRuns`), and a run reads only the prefix it is offered.
So, for every machine, the probability of the output is the limit of the
probabilities of its stages, which are explicit rational numbers
(`stageOutputProbR_tendsto`, `outputProbR_approximated_from_below`).

A machine is prefix-monotone when an output obtained from a prefix is
obtained from every longer prefix, given enough budget. Then a tape gives at
most one output and the probabilities of the outputs 1 and 0 sum to at most
one.

The budget has to grow with the prefix. The bounded evaluator needs a budget
above its input, and the encoded input is at least the number of bits
offered, so no run halts with a budget of at most the number of bits
(`runPTMR_eq_none_of_fuel_le`). The stages therefore bound the budget and the
prefix separately, and the prefix law lets the budget grow.
-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Prefix-Stable Random Bit Encoding -/

/-- Encode a single bit as 0 or 1. -/
def bitToNat (b : Bool) : ℕ := if b then 1 else 0

/-- Encode random bits 0..(n-1) using nested pairs, with the newest bit outermost.

Structure: `prefixEncode r (n+1) = pair (prefixEncode r n) (bit n)`

This ensures that `prefixEncode r n` can be recovered from `prefixEncode r (n+k)`. -/
def prefixEncode (r : CantorSpace) : ℕ → ℕ
  | 0 => 0  -- Empty encoding (sentinel)
  | n + 1 => Nat.pair (prefixEncode r n) (bitToNat (r n))

/-- Extract bit i from a prefix encoding of length n (returns 0 if i ≥ n).
We navigate from the outermost pair (position length-1) down to position i. -/
def extractBit (encoded : ℕ) (length i : ℕ) : ℕ :=
  if i < length then
    -- Navigate: strip (length - 1 - i) outer layers, then take .2
    let stepsToStrip := length - 1 - i
    let innerEnc := Nat.iterate (fun n => n.unpair.1) stepsToStrip encoded
    innerEnc.unpair.2
  else 0

/-- Key property: prefixEncode is monotone in the sense that we can extract the shorter prefix. -/
theorem prefixEncode_prefix (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.1 = prefixEncode r n := by
  simp [prefixEncode]

/-- The newest bit is correctly encoded. -/
theorem prefixEncode_newest_bit (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.2 = bitToNat (r n) := by
  simp [prefixEncode]

/-! ## Refined PTM Definition -/

/-- A refined probabilistic Turing machine index.

The machine takes:
- Input x : ℕ
- Encoded random prefix : ℕ (using prefixEncode)
- Length of the prefix : ℕ (so it knows how many bits are available)

The machine can extract individual bits using extractBit.
-/
abbrev PTMIndexR := Nat.Partrec.Code

/-- Run a refined PTM with fuel steps and numBits random bits available.

The input encoding is:
  triple (x, prefixEncode r numBits, numBits)

This way the machine knows both the encoded bits and how many are available. -/
def runPTMR (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  let encoded := prefixEncode r numBits
  let input := Nat.pair x (Nat.pair encoded numBits)
  Nat.Partrec.Code.evaln fuel M input

/-- A refined PTM halts with output k if there exist sufficient fuel and random bits. -/
def PTMRHaltsWithOutput (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (k : ℕ) : Prop :=
  ∃ fuel numBits, runPTMR M x r fuel numBits = some k

/-! ## Monotonicity Properties -/

/-- Key monotonicity: more fuel with same bits gives same or better result. -/
theorem runPTMR_mono_fuel (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (numBits : ℕ)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) {k : ℕ}
    (hr : runPTMR M x r fuel₁ numBits = some k) :
    runPTMR M x r fuel₂ numBits = some k := by
  unfold runPTMR at hr ⊢
  have h_mem : k ∈ Nat.Partrec.Code.evaln fuel₁ M _ := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-- Helper: extract prefix from longer encoding by stripping outer layers.
Uses `Nat.iterate` to avoid termination issues. -/
def truncateEncoding (encoded length targetLength : ℕ) : ℕ :=
  if targetLength ≥ length then encoded
  else Nat.iterate (fun n => n.unpair.1) (length - targetLength) encoded

/-- Key lemma: stripping one layer from prefixEncode (n+1) gives prefixEncode n. -/
theorem prefixEncode_unpair_fst (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.1 = prefixEncode r n := by
  simp [prefixEncode]

/-- Truncating to the same length is identity. -/
theorem truncateEncoding_self (encoded length : ℕ) :
    truncateEncoding encoded length length = encoded := by
  simp [truncateEncoding]

/-- Stripping k layers from prefixEncode (n + k) gives prefixEncode n.
Proved by induction on k, stripping one layer at a time from the outside. -/
theorem iterate_unpair_prefixEncode (r : CantorSpace) (n k : ℕ) :
    (fun m => m.unpair.1)^[k] (prefixEncode r (n + k)) = prefixEncode r n := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- f^[k+1] x = f^[k] (f x), so apply f first then iterate k times
    rw [Function.iterate_succ_apply]
    -- Goal: (fun m => m.unpair.1)^[k] ((prefixEncode r (n + (k + 1))).unpair.1) = prefixEncode r n
    -- Use that n + (k + 1) = (n + k) + 1 and prefixEncode_unpair_fst
    have h_add : n + (k + 1) = (n + k) + 1 := by omega
    rw [h_add, prefixEncode_unpair_fst]
    exact ih

theorem truncateEncoding_correct (r : CantorSpace) (n m : ℕ) (h : n ≤ m) :
    truncateEncoding (prefixEncode r m) m n = prefixEncode r n := by
  unfold truncateEncoding
  by_cases h_eq : n ≥ m
  · -- n = m case
    have : n = m := Nat.le_antisymm h h_eq
    simp [this]
  · -- n < m case
    have h_eq : n < m := Nat.lt_of_not_ge h_eq
    simp only [h_eq.not_ge, ↓reduceIte]
    -- m = n + (m - n), so we strip (m - n) layers
    have h_split : m = n + (m - n) := (Nat.add_sub_cancel' (Nat.le_of_lt h_eq)).symm
    conv_lhs =>
      rw [h_split]
      arg 2; rw [Nat.add_sub_cancel_left]
    exact iterate_unpair_prefixEncode r n (m - n)

/-! ## The bounded evaluator -/

/-- The bounded evaluator gives nothing when the budget does not exceed its
input. -/
theorem evaln_eq_none_of_le {fuel input : ℕ} (code : Nat.Partrec.Code) (small : fuel ≤ input) :
    Nat.Partrec.Code.evaln fuel code input = none := by
  cases result : Nat.Partrec.Code.evaln fuel code input with
  | none => rfl
  | some output =>
      exact absurd (Nat.Partrec.Code.evaln_bound result) (Nat.not_lt_of_ge small)

/-- With a budget of at most the number of bits offered, no run halts. -/
theorem runPTMR_eq_none_of_fuel_le (M : PTMIndexR) (x : ℕ) (r : CantorSpace) {fuel numBits : ℕ}
    (small : fuel ≤ numBits) : runPTMR M x r fuel numBits = none :=
  evaln_eq_none_of_le M
    (small.trans ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)))

/-! ## The runs as a bounded family -/

/-- The runs of a machine on an input. -/
def ptmRunR (M : PTMIndexR) (x : ℕ) : BoundedRun :=
  fun r fuel numBits => runPTMR M x r fuel numBits

/-- The encoding of a prefix depends on the bits of the prefix only. -/
theorem prefixEncode_congr {first second : CantorSpace} {numBits : ℕ}
    (same : ∀ index, index < numBits → first index = second index) :
    prefixEncode first numBits = prefixEncode second numBits := by
  induction numBits with
  | zero => rfl
  | succ numBits ih =>
      simp only [prefixEncode]
      rw [ih fun index within => same index (Nat.lt_succ_of_lt within),
        same numBits (Nat.lt_succ_self _)]

theorem ptmRunR_readsPrefix (M : PTMIndexR) (x : ℕ) : (ptmRunR M x).ReadsPrefix := by
  intro first second fuel numBits same
  simp only [ptmRunR, runPTMR, prefixEncode_congr same]

theorem ptmRunR_fuelMonotone (M : PTMIndexR) (x : ℕ) : (ptmRunR M x).FuelMonotone :=
  fun r numBits _ _ _ bound halted => runPTMR_mono_fuel M x r numBits bound halted

/-- A machine is prefix-monotone when an output obtained from a prefix of the
tape is obtained from every longer prefix, given enough budget. -/
def IsPrefixMonotone (M : PTMIndexR) : Prop := ∀ x, (ptmRunR M x).PrefixMonotone

/-! ## Output probability -/

/-- The set of random tapes for which the machine outputs 1. -/
def outputOneSetR (M : PTMIndexR) (x : ℕ) : Set CantorSpace :=
  {r : CantorSpace | PTMRHaltsWithOutput M x r 1}

theorem outputOneSetR_eq (M : PTMIndexR) (x : ℕ) :
    outputOneSetR M x = (ptmRunR M x).outputSet 1 := rfl

/-- The probability that the machine outputs 1. -/
noncomputable def outputProbR (M : PTMIndexR) (x : ℕ) : ℝ≥0∞ :=
  coinMeasure (outputOneSetR M x)

/-- The probability that the machine outputs 1 with budget and prefix at most
the stage. -/
noncomputable def stageOutputProbR (M : PTMIndexR) (x stage : ℕ) : ℝ≥0∞ :=
  coinMeasure ((ptmRunR M x).stageSet 1 stage)

/-- **Convergence.** For every machine the probabilities of the stages
converge to the output probability. -/
theorem stageOutputProbR_tendsto (M : PTMIndexR) (x : ℕ) :
    Filter.Tendsto (fun stage => stageOutputProbR M x stage) Filter.atTop
      (nhds (outputProbR M x)) :=
  (ptmRunR M x).tendsto_measure_stageSet coinMeasure 1

/-- **Approximation from below.** The rational counts of accepted prefixes
increase with the stage, never exceed the output probability and converge to
it. -/
theorem outputProbR_approximated_from_below (M : PTMIndexR) (x : ℕ) :
    Monotone ((ptmRunR M x).fraction 1) ∧
      (∀ stage, ENNReal.ofReal ((ptmRunR M x).fraction 1 stage : ℝ) ≤ outputProbR M x) ∧
      Filter.Tendsto (fun stage => ENNReal.ofReal ((ptmRunR M x).fraction 1 stage : ℝ))
        Filter.atTop (nhds (outputProbR M x)) :=
  (ptmRunR_readsPrefix M x).approximated_from_below 1

/-! ## Prefix-monotone machines -/

/-- For a prefix-monotone machine a tape gives at most one output. -/
theorem IsPrefixMonotone.output_unique {M : PTMIndexR} (monotone : IsPrefixMonotone M)
    {x : ℕ} {r : CantorSpace} {first second : ℕ}
    (haltsFirst : PTMRHaltsWithOutput M x r first)
    (haltsSecond : PTMRHaltsWithOutput M x r second) : first = second :=
  BoundedRun.output_unique (ptmRunR_fuelMonotone M x) (monotone x) haltsFirst haltsSecond

/-- For a prefix-monotone machine the probabilities of the outputs 1 and 0 sum
to at most one. -/
theorem IsPrefixMonotone.binary_probability_le_one {M : PTMIndexR}
    (monotone : IsPrefixMonotone M) (x : ℕ) :
    outputProbR M x + coinMeasure {r : CantorSpace | PTMRHaltsWithOutput M x r 0} ≤ 1 :=
  BoundedRun.coinMeasure_outputSet_add_le_one (ptmRunR_readsPrefix M x)
    (ptmRunR_fuelMonotone M x) (monotone x) (by decide)

/-- For a prefix-monotone machine the output probability is approached
through the prefix length alone, with the budget unbounded. -/
theorem IsPrefixMonotone.prefix_tendsto {M : PTMIndexR} (monotone : IsPrefixMonotone M)
    (x : ℕ) :
    Filter.Tendsto (fun numBits => coinMeasure ((ptmRunR M x).prefixSet 1 numBits))
      Filter.atTop (nhds (outputProbR M x)) :=
  (monotone x).tendsto_measure_prefixSet coinMeasure 1

/-! ## A machine that always outputs 1 -/

/-- The code of the constant function 1. -/
def constantOne : Nat.Partrec.Code := Nat.Partrec.Code.const 1

theorem constantOne_eval (input : ℕ) : 1 ∈ Nat.Partrec.Code.eval constantOne input := by
  rw [constantOne, Nat.Partrec.Code.eval_const]
  exact Part.mem_some 1

/-- Given enough budget the bounded evaluator gives 1. -/
theorem constantOne_evaln_complete (input : ℕ) :
    ∃ fuel, Nat.Partrec.Code.evaln fuel constantOne input = some 1 :=
  Nat.Partrec.Code.evaln_complete.mp (constantOne_eval input)

/-- The bounded evaluator gives nothing but 1. -/
theorem constantOne_evaln_sound {fuel input output : ℕ}
    (halted : Nat.Partrec.Code.evaln fuel constantOne input = some output) : output = 1 :=
  Part.mem_unique (Nat.Partrec.Code.evaln_sound halted) (constantOne_eval input)

end Mettapedia.Computability
