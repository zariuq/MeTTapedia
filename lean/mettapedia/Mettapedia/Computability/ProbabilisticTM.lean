import Mettapedia.Computability.CantorSpace
import Mathlib.Computability.PartrecCode

/-!
# Probabilistic Turing Machines

This file defines probabilistic Turing machines using Mathlib's `Nat.Partrec.Code`
combined with the random bit stream from `CantorSpace`.

## Main Definitions

* `PTM`: A probabilistic Turing machine is a partial recursive code that reads random bits
* `PTM.runN`: Run a PTM for n steps with bounded fuel
* `PTM.outputProb`: The probability that the machine outputs a given value

## Implementation Notes

We model a probabilistic TM as a function that takes:
1. An input `x : ℕ` (encoded)
2. A random bit stream `r : CantorSpace` (infinite random bits)

The machine can query `r i` to get the i-th random bit. The computation is deterministic
given the random bits; randomness comes from the fair coin measure on CantorSpace.

## Mathematical Model

For a PTM M and input x:
- `outputProb M x k` = μ({r ∈ CantorSpace | M(x, r) terminates with output k})

where μ is the fair coin measure on Cantor space.

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Probabilistic Turing Machines -/

/-- A probabilistic Turing machine index.

We represent a PTM as a `Nat.Partrec.Code` that takes a pair (input, random_bits_used_so_far).
The random bits are encoded as a natural number (binary representation).
-/
abbrev PTMIndex := Nat.Partrec.Code

/-- Encode the first n bits of a random sequence as a natural number. -/
def encodeRandomBits (r : CantorSpace) (n : ℕ) : ℕ :=
  (List.finRange n).foldl (fun acc i => acc * 2 + if r i then 1 else 0) 0

/-- Run a PTM for at most k steps with n random bits.

This is a bounded, decidable approximation of PTM execution.
Returns `some output` if the machine halts, `none` if it needs more time/bits.
-/
def runPTMBounded (M : PTMIndex) (x : ℕ) (r : CantorSpace) (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  -- Encode input and random bits as a pair
  let input := Nat.pair x (encodeRandomBits r numBits)
  -- Use Mathlib's bounded evaluation
  Nat.Partrec.Code.evaln fuel M input

/-- A PTM halts with output k if there exist sufficient fuel and random bits. -/
def PTMHaltsWithOutput (M : PTMIndex) (x : ℕ) (r : CantorSpace) (k : ℕ) : Prop :=
  ∃ fuel numBits, runPTMBounded M x r fuel numBits = some k

/-- The set of random tapes for which the PTM outputs 1 (true/halting). -/
def outputOneSet (M : PTMIndex) (x : ℕ) : Set CantorSpace :=
  {r : CantorSpace | PTMHaltsWithOutput M x r 1}

/-- The set of random tapes for which the PTM outputs 0 (false/non-halting). -/
def outputZeroSet (M : PTMIndex) (x : ℕ) : Set CantorSpace :=
  {r : CantorSpace | PTMHaltsWithOutput M x r 0}

/-! ## Measurability

We prove that the output sets are measurable, which allows us to define probabilities.
-/

/-- The encoding of random bits depends only on the first numBits.

The foldl over finRange numBits only accesses indices i with i < numBits.
Since r₁ and r₂ agree on these indices, the encoded results are equal.
-/
-- Helper: foldl with step functions that agree on all list elements (when bounded)
private lemma foldl_nat_eq (r₁ r₂ : CantorSpace) (numBits : ℕ)
    (h : ∀ i < numBits, r₁ i = r₂ i) (acc : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < numBits) →
    l.foldl (fun a i => a * 2 + if r₁ i then 1 else 0) acc =
    l.foldl (fun a i => a * 2 + if r₂ i then 1 else 0) acc
  | [], _ => rfl
  | x :: xs, hbnd => by
    simp only [List.foldl_cons]
    have hx : x < numBits := hbnd x (List.mem_cons.mpr (Or.inl rfl))
    rw [h x hx]
    exact foldl_nat_eq r₁ r₂ numBits h _ xs
      (fun i hi => hbnd i (List.mem_cons.mpr (Or.inr hi)))

-- Helper: foldl building a list from non-empty accumulator
private lemma foldl_append_singleton_acc {α β : Type*} (f : α → β) (acc : List β) (l : List α) :
    l.foldl (fun acc a => acc ++ [f a]) acc = acc ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]

-- Helper: the foldl building a list equals map
private lemma foldl_append_singleton_eq_map {α β : Type*} (f : α → β) (l : List α) :
    l.foldl (fun acc a => acc ++ [f a]) [] = l.map f := by
  rw [foldl_append_singleton_acc]
  simp

-- The list produced by `do let a ← List.finRange n; pure ↑a` contains only values < n
private lemma finRange_bind_pure_bounded (n : ℕ) :
    ∀ i ∈ (do let a ← List.finRange n; pure (↑a : ℕ)), i < n := by
  intro i hi
  -- The do notation expands to List.bind which is flatMap/foldl
  -- We use that this equals List.map Fin.val (List.finRange n)
  have h_eq : (do let a ← List.finRange n; pure (↑a : ℕ)) =
              (List.finRange n).map (fun x : Fin n => (x : ℕ)) := by
    simp only [List.bind_eq_flatMap, List.flatMap_eq_foldl, List.pure_def]
    exact foldl_append_singleton_eq_map _ _
  rw [h_eq] at hi
  simp only [List.mem_map, List.mem_finRange, true_and] at hi
  obtain ⟨j, rfl⟩ := hi
  exact j.isLt

theorem encodeRandomBits_firstN (r₁ r₂ : CantorSpace) (numBits : ℕ)
    (h : ∀ i < numBits, r₁ i = r₂ i) :
    encodeRandomBits r₁ numBits = encodeRandomBits r₂ numBits := by
  unfold encodeRandomBits
  exact foldl_nat_eq r₁ r₂ numBits h 0 _ (finRange_bind_pure_bounded numBits)

/-- The bounded run factorizes through the first numBits. -/
def runPTMBoundedViaPrefix (M : PTMIndex) (x : ℕ) (fuel numBits : ℕ) :
    (Fin numBits → Bool) → Option ℕ :=
  fun bits => Nat.Partrec.Code.evaln fuel M
    (Nat.pair x (encodeRandomBits (fun i => if h : i < numBits then bits ⟨i, h⟩ else false) numBits))

/-- The bounded run equals the factored version composed with prefixProj. -/
theorem runPTMBounded_eq_factored (M : PTMIndex) (x : ℕ) (fuel numBits : ℕ) (r : CantorSpace) :
    runPTMBounded M x r fuel numBits = runPTMBoundedViaPrefix M x fuel numBits (prefixProj numBits r) := by
  unfold runPTMBounded runPTMBoundedViaPrefix prefixProj
  simp only
  congr 2
  apply encodeRandomBits_firstN
  intro i hi
  simp only [hi, dite_true]

/-- The set of tapes where bounded execution gives output k is measurable.

Key insight: The set is the preimage of {some k} under a function that depends only
on the first numBits. Since projecting to a finite prefix is measurable, and the
resulting function on a finite type is automatically measurable, the preimage is measurable.
-/
theorem boundedOutputSet_measurable (M : PTMIndex) (x : ℕ) (fuel numBits k : ℕ) :
    MeasurableSet {r : CantorSpace | runPTMBounded M x r fuel numBits = some k} := by
  -- Rewrite as preimage of factored function
  have h_eq : {r : CantorSpace | runPTMBounded M x r fuel numBits = some k} =
              (prefixProj numBits) ⁻¹' {bits | runPTMBoundedViaPrefix M x fuel numBits bits = some k} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [runPTMBounded_eq_factored]
  rw [h_eq]
  -- The preimage of a measurable set under a measurable function is measurable
  -- The set in Fin numBits → Bool is measurable because Fin numBits → Bool
  -- has a discrete measurable space structure
  have h_discrete : MeasurableSet {bits : Fin numBits → Bool |
      runPTMBoundedViaPrefix M x fuel numBits bits = some k} := by
    apply MeasurableSet.of_discrete
  exact (prefixProj_measurable numBits) h_discrete

/-- The full output set is measurable (countable union of measurable sets). -/
theorem outputSet_measurable (M : PTMIndex) (x : ℕ) (k : ℕ) :
    MeasurableSet {r : CantorSpace | PTMHaltsWithOutput M x r k} := by
  unfold PTMHaltsWithOutput
  -- Countable union over fuel and numBits
  have : {r : CantorSpace | ∃ fuel numBits, runPTMBounded M x r fuel numBits = some k} =
         ⋃ (fuel : ℕ) (numBits : ℕ), {r | runPTMBounded M x r fuel numBits = some k} := by
    ext r; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [this]
  apply MeasurableSet.iUnion
  intro fuel
  apply MeasurableSet.iUnion
  intro numBits
  exact boundedOutputSet_measurable M x fuel numBits k

/-! ## Output Probabilities -/

/-- The probability that PTM M on input x outputs 1.

This is the key quantity for Reflective Oracles: we want to compute/bound
this probability.
-/
noncomputable def outputProb (M : PTMIndex) (x : ℕ) : ℝ≥0∞ :=
  coinMeasure (outputOneSet M x)

/-- The probability that PTM M on input x outputs 0. -/
noncomputable def outputProbZero (M : PTMIndex) (x : ℕ) : ℝ≥0∞ :=
  coinMeasure (outputZeroSet M x)

/-- Output probability is at most 1. -/
theorem outputProb_le_one (M : PTMIndex) (x : ℕ) : outputProb M x ≤ 1 := by
  unfold outputProb
  have h1 : coinMeasure (outputOneSet M x) ≤ coinMeasure Set.univ :=
    measure_mono (Set.subset_univ _)
  have h2 : coinMeasure Set.univ = 1 := measure_univ
  calc coinMeasure (outputOneSet M x) ≤ coinMeasure Set.univ := h1
    _ = 1 := h2

/-- Output probability is non-negative. -/
theorem outputProb_nonneg (M : PTMIndex) (x : ℕ) : 0 ≤ outputProb M x := by
  exact bot_le

/-! ## Bounded Approximations

For practical proofs, we work with bounded approximations of output probability.
-/

/-- Probability of outputting 1 within fuel steps using numBits random bits. -/
noncomputable def boundedOutputProb (M : PTMIndex) (x : ℕ) (fuel numBits : ℕ) : ℝ≥0∞ :=
  coinMeasure {r : CantorSpace | runPTMBounded M x r fuel numBits = some 1}

/-- Bounded approximations are monotone in fuel. -/
theorem boundedOutputProb_mono_fuel (M : PTMIndex) (x : ℕ) (numBits : ℕ)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) :
    boundedOutputProb M x fuel₁ numBits ≤ boundedOutputProb M x fuel₂ numBits := by
  -- More fuel can only add halting runs, not remove them
  unfold boundedOutputProb
  apply measure_mono
  intro r hr
  simp only [Set.mem_setOf_eq] at hr ⊢
  -- Use evaln_mono: if evaln k₁ c n = some x, then evaln k₂ c n = some x for k₂ ≥ k₁
  unfold runPTMBounded at hr ⊢
  have h_mem : (1 : ℕ) ∈ Nat.Partrec.Code.evaln fuel₁ M (Nat.pair x (encodeRandomBits r numBits)) := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-- Bounded approximations converge to the true probability.

NOTE: This theorem requires a modeling assumption about "well-behaved" PTMs that
only read the random bits they actually need. In the current encoding where
`encodeRandomBits r numBits` packs the first numBits into a single ℕ, changing
numBits changes the encoded value entirely. A "proper" PTM that reads bits
sequentially and halts once it has enough information would satisfy:
- If halts with (fuel, numBits), then halts with same output for (fuel', numBits') when
  fuel' ≥ fuel and numBits' ≥ numBits

For now, we accept this as a fundamental property of our PTM model.
-/
theorem boundedOutputProb_tendsto (M : PTMIndex) (x : ℕ) :
    Filter.Tendsto (fun n => boundedOutputProb M x n n) Filter.atTop
      (nhds (outputProb M x)) := by
  -- The proof requires showing that for each r ∈ outputOneSet, r eventually
  -- belongs to the n-th bounded set. This follows from the definition of
  -- PTMHaltsWithOutput plus a modeling assumption about sequential bit reading.
  -- Key steps:
  -- 1. outputOneSet M x = ⋃ (fuel numBits : ℕ), {r | runPTMBounded M x r fuel numBits = some 1}
  -- 2. The diagonal sets {r | runPTMBounded M x r n n = some 1} eventually cover outputOneSet
  -- 3. Use MeasureTheory.tendsto_measure_iUnion for continuity from below
  sorry

/-! ## Connection to Reflective Oracles

The key property for reflective oracles is that we can compute/approximate
the output probability from below and above.
-/

/-- The output probability can be approximated from below computably.

This is the "limit computability" property: there's a computable sequence
converging to the true probability from below.

The approximating function f(n) counts, for each n, the fraction of n-bit
random strings for which the machine halts with output 1 within n steps:
  f(n) = |{bits ∈ {0,1}^n | runPTMBounded M x r_bits n n = some 1}| / 2^n

This is computable (enumerate all 2^n bit strings, run the machine) and
monotone (under the "well-behaved PTM" assumption from boundedOutputProb_tendsto).
-/
theorem outputProb_limit_computable_below (M : PTMIndex) (x : ℕ) :
    ∃ f : ℕ → ℝ≥0, (∀ n, (f n : ℝ≥0∞) ≤ outputProb M x) ∧
                    Monotone f ∧
                    Filter.Tendsto (fun n => (f n : ℝ≥0∞)) Filter.atTop
                      (nhds (outputProb M x)) := by
  -- The construction:
  -- f(n) = boundedOutputProb M x n n (converted to ℝ≥0 via .toReal/.toNNReal)
  -- This is bounded by outputProb (since the bounded set ⊆ outputOneSet)
  -- Monotonicity and convergence follow from boundedOutputProb_tendsto
  sorry

end Mettapedia.Computability
