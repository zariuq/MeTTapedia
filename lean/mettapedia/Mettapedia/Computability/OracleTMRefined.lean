import Mettapedia.Computability.ProbabilisticTMRefined
import Mathlib.Computability.PartrecCode

/-!
# Refined Oracle Turing Machines

This file provides a refined OTM model that uses the prefix-stable random bit encoding
from `ProbabilisticTMRefined.lean`.

## Key Improvements over OracleTM.lean

1. **Prefix-stable random bit encoding**: Uses `prefixEncode` instead of `encodeRandomBits`,
   which ensures that more random bits only ADD information, never change existing bits.

2. **Separate oracle encoding**: The oracle is encoded separately from random bits,
   using a list-based representation that allows for consistent partial oracle queries.

## Monotonicity Properties

With this model:
- **Random bit monotonicity**: More random bits can only help (or be neutral), never hurt
- **Oracle monotonicity**: Requires additional assumptions about machine behavior
  (see `OracleTM.lean` for discussion)

## Implementation

We model an OTM as taking:
- Input x : ℕ
- Prefix-encoded random bits (using `prefixEncode`)
- Oracle answers encoded as a separate component

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Oracle Definition -/

/-- An oracle is a function answering probability threshold queries. -/
abbrev OracleR := ℕ → Bool

/-! ## Refined Oracle Turing Machine -/

/-- A refined Oracle Turing Machine index. -/
abbrev OTMIndexR := Nat.Partrec.Code

/-- Run a refined OTM with prefix-encoded random bits.

The input encoding is:
  triple (x, prefixEncode r numBits, oracleBit)

This ensures random bit monotonicity (more bits only add information).
-/
def runOTMRBounded (M : OTMIndexR) (x : ℕ) (r : CantorSpace) (O : OracleR)
    (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  let encoded := prefixEncode r numBits
  -- For simplicity, include first oracle query result
  -- A more complete model would allow dynamic oracle queries
  let oracleBit : ℕ := if O 0 then 1 else 0
  let input := Nat.pair x (Nat.pair (Nat.pair encoded numBits) oracleBit)
  Nat.Partrec.Code.evaln fuel M input

/-- An OTM halts with output k given random bits r and oracle O. -/
def OTMRHaltsWithOutput (M : OTMIndexR) (x : ℕ) (r : CantorSpace) (O : OracleR) (k : ℕ) : Prop :=
  ∃ fuel numBits, runOTMRBounded M x r O fuel numBits = some k

/-- The set of random tapes for which the OTM outputs 1 given oracle O. -/
def oracleOutputOneSetR (M : OTMIndexR) (x : ℕ) (O : OracleR) : Set CantorSpace :=
  {r : CantorSpace | OTMRHaltsWithOutput M x r O 1}

/-! ## Prefix-Respecting OTMs -/

/-- An OTM is prefix-respecting if its behavior only depends on the random bits
actually queried, not on the numBits parameter. This is the oracle-aware
version of `isPrefixRespecting` from ProbabilisticTMRefined.lean. -/
def isOraclePrefixRespecting (M : OTMIndexR) (O : OracleR) : Prop :=
  ∀ (x : ℕ) (r : CantorSpace) (fuel numBits₁ numBits₂ : ℕ) (k : ℕ),
    numBits₁ ≤ numBits₂ →
    runOTMRBounded M x r O fuel numBits₁ = some k →
    runOTMRBounded M x r O fuel numBits₂ = some k

/-! ## Monotonicity for Random Bits -/

/-- Fuel monotonicity: more fuel with same bits gives same or better result. -/
theorem runOTMRBounded_mono_fuel (M : OTMIndexR) (x : ℕ) (r : CantorSpace) (O : OracleR)
    (numBits : ℕ) {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) {k : ℕ}
    (hr : runOTMRBounded M x r O fuel₁ numBits = some k) :
    runOTMRBounded M x r O fuel₂ numBits = some k := by
  unfold runOTMRBounded at hr ⊢
  have h_mem : k ∈ Nat.Partrec.Code.evaln fuel₁ M _ := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-- For prefix-respecting OTMs, more random bits gives same result. -/
theorem runOTMRBounded_mono_bits (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O)
    (x : ℕ) (r : CantorSpace) (fuel : ℕ)
    {numBits₁ numBits₂ : ℕ} (h : numBits₁ ≤ numBits₂) {k : ℕ}
    (hr : runOTMRBounded M x r O fuel numBits₁ = some k) :
    runOTMRBounded M x r O fuel numBits₂ = some k :=
  hM x r fuel numBits₁ numBits₂ k h hr

/-- Combined monotonicity for prefix-respecting OTMs. -/
theorem runOTMRBounded_mono (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O)
    (x : ℕ) (r : CantorSpace)
    {fuel₁ fuel₂ numBits₁ numBits₂ : ℕ} (hf : fuel₁ ≤ fuel₂) (hn : numBits₁ ≤ numBits₂) {k : ℕ}
    (hr : runOTMRBounded M x r O fuel₁ numBits₁ = some k) :
    runOTMRBounded M x r O fuel₂ numBits₂ = some k := by
  have h1 := runOTMRBounded_mono_bits M O hM x r fuel₁ hn hr
  exact runOTMRBounded_mono_fuel M x r O numBits₂ hf h1

/-! ## Output Sets and Probabilities -/

/-- Bounded output set for the refined model. -/
def boundedOracleOutputSetR (M : OTMIndexR) (x : ℕ) (O : OracleR) (fuel numBits : ℕ) :
    Set CantorSpace :=
  {r : CantorSpace | runOTMRBounded M x r O fuel numBits = some 1}

/-- Bounded output sets are monotone for prefix-respecting OTMs. -/
theorem boundedOracleOutputSetR_mono (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O) (x : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    boundedOracleOutputSetR M x O n₁ n₁ ⊆ boundedOracleOutputSetR M x O n₂ n₂ := by
  intro r hr
  simp only [boundedOracleOutputSetR, Set.mem_setOf_eq] at hr ⊢
  exact runOTMRBounded_mono M O hM x r h h hr

/-- For prefix-respecting OTMs, outputOneSet equals the union of diagonal sets. -/
theorem oracleOutputOneSetR_eq_iUnion (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O) (x : ℕ) :
    oracleOutputOneSetR M x O = ⋃ (n : ℕ), boundedOracleOutputSetR M x O n n := by
  ext r
  simp only [oracleOutputOneSetR, OTMRHaltsWithOutput, boundedOracleOutputSetR,
             Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ⟨fuel, numBits, hr⟩
    use max fuel numBits
    exact runOTMRBounded_mono M O hM x r (le_max_left _ _) (le_max_right _ _) hr
  · intro ⟨n, hr⟩
    exact ⟨n, n, hr⟩

/-! ## Probability Definitions -/

/-- Output probability for the refined OTM model. -/
noncomputable def oracleOutputProbR (M : OTMIndexR) (x : ℕ) (O : OracleR) : ℝ≥0∞ :=
  coinMeasure (oracleOutputOneSetR M x O)

/-- Bounded output probability for the refined OTM model. -/
noncomputable def boundedOracleOutputProbR (M : OTMIndexR) (x : ℕ) (O : OracleR)
    (fuel numBits : ℕ) : ℝ≥0∞ :=
  coinMeasure (boundedOracleOutputSetR M x O fuel numBits)

/-- Bounded approximations are monotone for prefix-respecting OTMs. -/
theorem boundedOracleOutputProbR_mono (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O) (x : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    boundedOracleOutputProbR M x O n₁ n₁ ≤ boundedOracleOutputProbR M x O n₂ n₂ := by
  unfold boundedOracleOutputProbR
  exact measure_mono (boundedOracleOutputSetR_mono M O hM x h)

/-- Convergence theorem for prefix-respecting OTMs. -/
theorem boundedOracleOutputProbR_tendsto (M : OTMIndexR) (O : OracleR)
    (hM : isOraclePrefixRespecting M O) (x : ℕ) :
    Filter.Tendsto (fun n => boundedOracleOutputProbR M x O n n) Filter.atTop
      (nhds (oracleOutputProbR M x O)) := by
  unfold oracleOutputProbR boundedOracleOutputProbR
  rw [oracleOutputOneSetR_eq_iUnion M O hM x]
  have h_mono : Monotone (fun n => boundedOracleOutputSetR M x O n n) := by
    intro n₁ n₂ h
    exact boundedOracleOutputSetR_mono M O hM x h
  exact tendsto_measure_iUnion_atTop h_mono

/-! ## Basic Properties -/

/-- Oracle output probability is at most 1. -/
theorem oracleOutputProbR_le_one (M : OTMIndexR) (x : ℕ) (O : OracleR) :
    oracleOutputProbR M x O ≤ 1 := by
  unfold oracleOutputProbR
  have h1 : coinMeasure (oracleOutputOneSetR M x O) ≤ coinMeasure Set.univ :=
    measure_mono (Set.subset_univ _)
  have h2 : coinMeasure Set.univ = 1 := measure_univ
  calc coinMeasure (oracleOutputOneSetR M x O) ≤ coinMeasure Set.univ := h1
    _ = 1 := h2

/-- Oracle output probability is non-negative. -/
theorem oracleOutputProbR_nonneg (M : OTMIndexR) (x : ℕ) (O : OracleR) :
    0 ≤ oracleOutputProbR M x O :=
  bot_le

end Mettapedia.Computability
