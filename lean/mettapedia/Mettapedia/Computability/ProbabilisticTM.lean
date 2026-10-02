import Mettapedia.Computability.CantorSpace
import Mathlib.Computability.PartrecCode

/-!
# Partial-recursive finite-prefix experiments

Each experiment runs a `Nat.Partrec.Code` on a pair containing the input and a
packed finite random prefix. Changing the prefix changes the code's entire input.
The existential output event therefore need not assign one output per tape; this
is not yet a sequential probabilistic Turing-machine representation.

The legacy `PTMIndex`, `runPTMBounded`, and output-event names remain the interfaces
used by the oracle-experiment modules. `evaln`'s budget bounds numbers encountered
during evaluation, not just a number of machine steps.

`ProbabilisticPrefixExperiment` accumulates all bounded prefix experiments and
proves convergence of explicit finite-count rational approximations.
`ProbabilisticPrefixConsistency` gives a nonvacuous semantic condition for unique
outputs. `ProbabilisticTMBoundary` proves the failure of the unrestricted raw
diagonal and the vacuity of the refined same-budget prefix condition.
-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Finite-prefix execution -/

/-- A partial-recursive code evaluated on packed-prefix inputs.
    The name is shared with existing oracle-experiment interfaces. -/
abbrev PTMIndex := Nat.Partrec.Code

/-- Encode the first n bits of a random sequence as a natural number. -/
def encodeRandomBits (r : CantorSpace) (n : ℕ) : ℕ :=
  (List.finRange n).foldl (fun acc i => acc * 2 + if r i then 1 else 0) 0

/-- Run one experiment with the evaluator budget and packed prefix specified.
    This bounds the evaluator's encountered numbers; the prefix is ordinary input. -/
def runPTMBounded (M : PTMIndex) (x : ℕ) (r : CantorSpace) (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  -- Encode input and random bits as a pair
  let input := Nat.pair x (encodeRandomBits r numBits)
  -- Use Mathlib's bounded evaluation
  Nat.Partrec.Code.evaln fuel M input

/-- Some finite-prefix experiment produces the given output. -/
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
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
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
    ext r; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [this]
  apply MeasurableSet.iUnion
  intro fuel
  apply MeasurableSet.iUnion
  intro numBits
  exact boundedOutputSet_measurable M x fuel numBits k

/-! ## Output Probabilities -/

/-- Measure of the existential one-output experiment event. -/
noncomputable def outputProb (M : PTMIndex) (x : ℕ) : ℝ≥0∞ :=
  coinMeasure (outputOneSet M x)

/-- Measure of the existential zero-output experiment event. -/
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

/-- Measure of one experiment with its budget and prefix length fixed. -/
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
  simp only [Set.mem_ofPred_eq] at hr ⊢
  -- Use evaln_mono: if evaln k₁ c n = some x, then evaln k₂ c n = some x for k₂ ≥ k₁
  unfold runPTMBounded at hr ⊢
  have h_mem : (1 : ℕ) ∈ Nat.Partrec.Code.evaln fuel₁ M (Nat.pair x (encodeRandomBits r numBits)) := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-!
The raw diagonal changes the code's input at every stage and does not generally
converge to the existential output event. Accumulated finite events and their exact
rational counts are developed in `ProbabilisticPrefixExperiment`.
-/

end Mettapedia.Computability
