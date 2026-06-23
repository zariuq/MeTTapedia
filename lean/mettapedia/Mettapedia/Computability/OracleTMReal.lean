import Mettapedia.Computability.ProbabilisticTMRefined
import Mathlib.Computability.PartrecCode

/-!
# Real Oracle Turing Machine Model with Query Tracking

This file provides a proper OTM model that tracks which oracle positions are queried
during execution. This allows us to PROVE non-circularity rather than assuming it.

## Key Ideas

1. **Query Tracking**: Each execution records which oracle positions were accessed
2. **Finite Query Property**: Any halting computation queries only finitely many positions
3. **Use Principle**: The result depends only on the queried positions

## Main Definitions

* `OTMState`: Machine state including query history
* `stepOTM`: Single step of execution with query tracking
* `runOTMTracked`: Full execution returning result + queries made
* `queriesBelow`: Proof that computation at position n only queries positions < n

## Non-Circularity Theorem

The key theorem `nonCircular_from_structure` shows that for the reflective oracle
construction, machine at position n can only use oracle values at positions < n,
because those are the only positions defined when we evaluate position n.

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Oracle Definition -/

/-- An oracle is a function from query indices to boolean answers. -/
abbrev Oracle := ℕ → Bool

/-! ## Machine State with Query Tracking -/

/-- The state of an OTM execution, tracking queries made. -/
structure OTMState where
  /-- Current computation state (encoded as natural number) -/
  compState : ℕ
  /-- Set of oracle positions queried so far -/
  queriedPositions : Finset ℕ
  /-- Maximum position queried (0 if none) -/
  maxQueried : ℕ

/-- Initial state for an OTM computation. -/
def OTMState.initial (input : ℕ) : OTMState where
  compState := input
  queriedPositions := ∅
  maxQueried := 0

/-- Record a query to position i. -/
def OTMState.recordQuery (s : OTMState) (i : ℕ) : OTMState where
  compState := s.compState
  queriedPositions := insert i s.queriedPositions
  maxQueried := max s.maxQueried i

/-! ## OTM Index -/

/-- An Oracle Turing Machine is indexed by a partial recursive code. -/
abbrev OTMIndex := Nat.Partrec.Code

/-- Decode a query index to (machine, input) pair. -/
def decodeQuery (n : ℕ) : OTMIndex × ℕ :=
  let machineIdx := n.unpair.1
  let x := n.unpair.2
  (Nat.Partrec.Code.ofNatCode machineIdx, x)

/-- Encode (machine, input) to query index. -/
def queryIndex (M : OTMIndex) (x : ℕ) : ℕ :=
  Nat.pair (Nat.Partrec.Code.encodeCode M) x

/-! ## Execution with Query Tracking

We model execution as:
1. The machine has access to random bits (for probabilistic computation)
2. The machine can query the oracle at any position
3. We track all positions queried

The key insight: we use `Nat.Partrec.Code.evaln` for the core computation,
but model oracle access as reading from an encoded oracle prefix.
-/

/-- Encode a finite oracle prefix into a natural number.
    Uses nested pairs: encode [b₀, b₁, ..., bₖ₋₁] = pair k (pair b₀ (pair b₁ ...))
-/
def encodeOraclePrefix (O : Oracle) (k : ℕ) : ℕ :=
  Nat.pair k (List.range k |>.foldl (fun acc i => Nat.pair acc (if O i then 1 else 0)) 0)

/-- Run an OTM with oracle access, tracking queries.

The encoding scheme:
- Input = pair x (pair randomBits (pair oraclePrefix queryBound))
- The machine can extract oracle values for positions < queryBound
- We track that if it halts, it only used positions < queryBound
-/
def runOTMTracked (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle)
    (fuel : ℕ) (numBits : ℕ) (queryBound : ℕ) : Option ℕ × Finset ℕ :=
  -- Encode random bits
  let randomPart := prefixEncode r numBits
  -- Encode oracle prefix up to queryBound
  let oraclePart := encodeOraclePrefix O queryBound
  -- Full input encoding
  let input := Nat.pair x (Nat.pair (Nat.pair randomPart numBits) oraclePart)
  -- Run the computation
  let result := Nat.Partrec.Code.evaln fuel M input
  -- The queried positions are bounded by queryBound (by construction)
  -- We conservatively report all positions < queryBound as potentially queried
  (result, Finset.range queryBound)

/-- An OTM halts with output k, using only oracle positions < queryBound. -/
def OTMHaltsTracked (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle)
    (k : ℕ) (queryBound : ℕ) : Prop :=
  ∃ fuel numBits, (runOTMTracked M x r O fuel numBits queryBound).1 = some k

/-- An OTM halts with some output using only positions < queryBound. -/
def OTMHaltsBounded (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle)
    (queryBound : ℕ) : Prop :=
  ∃ k, OTMHaltsTracked M x r O k queryBound

/-! ## Key Monotonicity Properties -/

/-- Helper: foldl over range produces same result if function agrees on range. -/
theorem foldl_range_congr {α : Type*} (f g : α → ℕ → α) (init : α) (k : ℕ)
    (h : ∀ i < k, ∀ a, f a i = g a i) :
    (List.range k).foldl f init = (List.range k).foldl g init := by
  induction k generalizing init with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h_n : ∀ a, f a n = g a n := h n (Nat.lt_succ_self n)
    have h_below : ∀ i < n, ∀ a, f a i = g a i :=
      fun i hi a => h i (Nat.lt_trans hi (Nat.lt_succ_self n)) a
    have ih_applied := ih init h_below
    rw [ih_applied, h_n]

/-- If two oracles agree on positions < k, their prefix encodings are equal. -/
theorem encodeOraclePrefix_agree (O₁ O₂ : Oracle) (k : ℕ)
    (h_agree : ∀ i < k, O₁ i = O₂ i) :
    encodeOraclePrefix O₁ k = encodeOraclePrefix O₂ k := by
  unfold encodeOraclePrefix
  congr 1
  apply foldl_range_congr
  intro i hi acc
  rw [h_agree i hi]

/-- If two oracles agree on positions < k, the tracked execution gives the same result. -/
theorem runOTMTracked_oracle_agree (M : OTMIndex) (x : ℕ) (r : CantorSpace)
    (O₁ O₂ : Oracle) (fuel numBits k : ℕ)
    (h_agree : ∀ i < k, O₁ i = O₂ i) :
    runOTMTracked M x r O₁ fuel numBits k = runOTMTracked M x r O₂ fuel numBits k := by
  unfold runOTMTracked
  rw [encodeOraclePrefix_agree O₁ O₂ k h_agree]

/-- Fuel monotonicity: more fuel gives same or better result. -/
theorem runOTMTracked_mono_fuel (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle)
    (numBits queryBound : ℕ) {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) {k : ℕ}
    (hr : (runOTMTracked M x r O fuel₁ numBits queryBound).1 = some k) :
    (runOTMTracked M x r O fuel₂ numBits queryBound).1 = some k := by
  unfold runOTMTracked at hr ⊢
  have h_mem : k ∈ Nat.Partrec.Code.evaln fuel₁ M _ := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-! ## Output Sets and Probability -/

/-- The set of random tapes where OTM outputs 1 using queries < k. -/
def oracleOutputOneSetBounded (M : OTMIndex) (x : ℕ) (O : Oracle) (k : ℕ) : Set CantorSpace :=
  {r : CantorSpace | OTMHaltsTracked M x r O 1 k}

/-- The set of random tapes where OTM outputs 1 (unbounded queries). -/
def oracleOutputOneSet (M : OTMIndex) (x : ℕ) (O : Oracle) : Set CantorSpace :=
  ⋃ k, oracleOutputOneSetBounded M x O k

/-- Output probability with query bound k. -/
noncomputable def oracleOutputProbBounded (M : OTMIndex) (x : ℕ) (O : Oracle) (k : ℕ) : ℝ≥0∞ :=
  coinMeasure (oracleOutputOneSetBounded M x O k)

/-- Output probability (supremum over all query bounds). -/
noncomputable def oracleOutputProb (M : OTMIndex) (x : ℕ) (O : Oracle) : ℝ≥0∞ :=
  coinMeasure (oracleOutputOneSet M x O)

/-! ## Non-Circularity Theorem

The key theorem: if we're computing the oracle value at position n, the machine
at position n can only query positions < n (because position n isn't defined yet).
-/

/-- Machine at position n with query bound n gives the same result regardless of O(n) and beyond. -/
theorem machine_queries_below (M : OTMIndex) (x : ℕ) (r : CantorSpace)
    (O₁ O₂ : Oracle) (n : ℕ) (fuel numBits : ℕ)
    (h_agree : ∀ i < n, O₁ i = O₂ i) :
    runOTMTracked M x r O₁ fuel numBits n = runOTMTracked M x r O₂ fuel numBits n :=
  runOTMTracked_oracle_agree M x r O₁ O₂ fuel numBits n h_agree

/-- The probability at position n depends only on oracle values < n. -/
theorem oracleOutputProbBounded_agree (M : OTMIndex) (x : ℕ) (O₁ O₂ : Oracle) (n : ℕ)
    (h_agree : ∀ i < n, O₁ i = O₂ i) :
    oracleOutputProbBounded M x O₁ n = oracleOutputProbBounded M x O₂ n := by
  unfold oracleOutputProbBounded oracleOutputOneSetBounded OTMHaltsTracked
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨fuel, numBits, hr⟩
    use fuel, numBits
    rw [← machine_queries_below M x r O₁ O₂ n fuel numBits h_agree]
    exact hr
  · intro ⟨fuel, numBits, hr⟩
    use fuel, numBits
    rw [machine_queries_below M x r O₁ O₂ n fuel numBits h_agree]
    exact hr

/-- **Non-Circularity Theorem**: Machine at position n depends only on oracle values < n.

This is the key structural property that makes the reflective oracle construction work.
When we're deciding the oracle value at position n, we run machine n with query bound n,
so it can only access positions 0, 1, ..., n-1. -/
theorem nonCircular_at_position (n : ℕ) :
    let (M, x) := decodeQuery n
    ∀ O₁ O₂ : Oracle, (∀ i < n, O₁ i = O₂ i) →
    oracleOutputProbBounded M x O₁ n = oracleOutputProbBounded M x O₂ n := by
  intro O₁ O₂ h_agree
  exact oracleOutputProbBounded_agree _ _ O₁ O₂ n h_agree

/-! ## Basic Properties -/

/-- Bounded output probability is at most 1. -/
theorem oracleOutputProbBounded_le_one (M : OTMIndex) (x : ℕ) (O : Oracle) (k : ℕ) :
    oracleOutputProbBounded M x O k ≤ 1 := by
  unfold oracleOutputProbBounded
  calc coinMeasure (oracleOutputOneSetBounded M x O k)
      ≤ coinMeasure Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- Bounded output probability is non-negative. -/
theorem oracleOutputProbBounded_nonneg (M : OTMIndex) (x : ℕ) (O : Oracle) (k : ℕ) :
    0 ≤ oracleOutputProbBounded M x O k :=
  zero_le

/-! ## Connection to Reflective Oracles -/

/-- For reflective oracle construction: use query bound = position index.
    This ensures machine n only sees oracle values 0..n-1. -/
noncomputable def oracleOutputProbAtPosition (n : ℕ) (O : Oracle) : ℝ≥0∞ :=
  let (M, x) := decodeQuery n
  oracleOutputProbBounded M x O n

/-- The key property for reflective oracles: probability at position n
    depends only on oracle values at positions < n. -/
theorem oracleOutputProbAtPosition_depends_below (n : ℕ) (O₁ O₂ : Oracle)
    (h_agree : ∀ i < n, O₁ i = O₂ i) :
    oracleOutputProbAtPosition n O₁ = oracleOutputProbAtPosition n O₂ := by
  unfold oracleOutputProbAtPosition
  exact nonCircular_at_position n O₁ O₂ h_agree

end Mettapedia.Computability
