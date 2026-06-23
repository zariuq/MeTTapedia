import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.NNReal.Defs

/-!
# Cantor Space and Fair Coin Measure

This file defines the Cantor space (infinite binary sequences) and the fair coin
measure (product of Bernoulli(1/2) distributions). This is the foundation for
formalizing probabilistic computation.

## Main Definitions

* `CantorSpace`: The type `ℕ → Bool` of infinite binary sequences
* `CantorSpace.coinMeasure`: The fair coin measure (product Bernoulli(1/2))

## Implementation Notes

We use Mathlib's projective limit infrastructure (`IsProjectiveLimit`) to define
the infinite product measure. The fair coin measure is the unique probability
measure such that:
- Each coordinate is independent
- Each coordinate is Bernoulli(1/2)

## References

* Mathlib's `MeasureTheory.Constructions.Projective`
* Mathlib's `Probability.ProbabilityMassFunction.Constructions` for Bernoulli

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Cantor Space -/

/-- Cantor space: infinite binary sequences. -/
abbrev CantorSpace := ℕ → Bool

-- The product σ-algebra instance is automatically inferred via MeasurableSpace.pi

/-! ## Finite Approximations

For the projective limit construction, we define measures on finite prefixes.
-/

/-- The probability 1/2 as an NNReal. -/
noncomputable def half : ℝ≥0 := (2 : ℝ≥0)⁻¹

theorem half_le_one : half ≤ 1 := by
  unfold half
  rw [NNReal.inv_le (by norm_num : (2 : ℝ≥0) ≠ 0)]
  norm_num

/-- Bernoulli(1/2) probability mass function. -/
noncomputable def bernoulliHalf : PMF Bool :=
  PMF.bernoulli half half_le_one

/-- The measure on Bool from Bernoulli(1/2). -/
noncomputable def bernoulliHalfMeasure : Measure Bool :=
  bernoulliHalf.toMeasure

/-- Bernoulli(1/2) measure is a probability measure.
This comes from `PMF.toMeasure.isProbabilityMeasure`. -/
instance : IsProbabilityMeasure bernoulliHalfMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Bernoulli(1/2) measure is SigmaFinite (follows from being a probability measure). -/
instance : SigmaFinite bernoulliHalfMeasure := inferInstance

/-- The product measure on finite prefixes `Fin n → Bool`. -/
noncomputable def finPrefixMeasure (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => bernoulliHalfMeasure)

/-- Each finite prefix measure is a probability measure.
Uses `Measure.pi.instIsProbabilityMeasure`. -/
instance finPrefixMeasure_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (finPrefixMeasure n) := by
  unfold finPrefixMeasure
  infer_instance

/-! ## Projective Family

The measures on finite prefixes form a projective family: restricting
from a longer prefix to a shorter one gives the correct marginal.
-/

/-- Projection from `Fin m → Bool` to `Fin n → Bool` for `n ≤ m`. -/
def finPrefixProj {n m : ℕ} (h : n ≤ m) : (Fin m → Bool) → (Fin n → Bool) :=
  fun f i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- The projection is measurable. -/
theorem finPrefixProj_measurable {n m : ℕ} (h : n ≤ m) :
    Measurable (finPrefixProj h) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The finite prefix measures form a projective family.

This is the key property: projecting from level m to level n (n ≤ m)
gives the correct marginal distribution.

The proof strategy:
1. Use Measure.pi_eq to reduce to showing equality on product sets
2. Show preimage of pi set under projection extends with Set.univ
3. Use Measure.pi_pi to get products
4. Show product over Fin m equals product over Fin n (coords ≥ n contribute 1)
-/
theorem finPrefixMeasure_projective :
    ∀ n m : ℕ, ∀ h : n ≤ m,
      (finPrefixMeasure m).map (finPrefixProj h) = finPrefixMeasure n := by
  intro n m h
  -- Use Measure.pi_eq: two product measures are equal if they agree on all product sets
  symm
  apply Measure.pi_eq
  intro s hs
  simp only [finPrefixMeasure]
  rw [Measure.map_apply (finPrefixProj_measurable h) (.univ_pi hs)]
  -- The preimage of Set.pi univ s under finPrefixProj extends s with Set.univ for extra coords
  have h_preimage : finPrefixProj h ⁻¹' (Set.pi Set.univ s) =
      Set.pi Set.univ (fun i : Fin m =>
        if hi : i.val < n then s ⟨i.val, hi⟩ else Set.univ) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, finPrefixProj]
    constructor
    · intro hf i
      by_cases hi : i.val < n
      · simp only [hi, ↓reduceDIte]; convert hf ⟨i.val, hi⟩
      · simp only [hi, ↓reduceDIte, Set.mem_univ]
    · intro hf i
      have := hf ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
      simp only [i.isLt, ↓reduceDIte] at this
      exact this
  rw [h_preimage, Measure.pi_pi]
  -- Product over Fin m with extended s equals product over Fin n with s
  -- Split the product: coords < n give s values, coords ≥ n give Set.univ (measure 1)
  have h_univ_one : bernoulliHalfMeasure Set.univ = 1 := measure_univ
  -- Split product using filter
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin m => i.val < n)]
  -- The "not" part is all 1s
  have h_tail : ∏ i ∈ Finset.univ.filter (fun i : Fin m => ¬i.val < n),
      bernoulliHalfMeasure (if hi : i.val < n then s ⟨i.val, hi⟩ else Set.univ) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    simp only [Nat.not_lt.mpr hi, dite_false, h_univ_one]
  rw [h_tail, mul_one]
  -- Now show filtered product over Fin m equals product over Fin n
  -- Use bijection: Fin n → Fin m via val embedding
  symm
  let embed : Fin n → Fin m := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
  apply Finset.prod_nbij embed
  · intro i _
    simp only [embed, Finset.mem_filter, Finset.mem_univ, true_and, Fin.isLt]
  · intro i₁ _ i₂ _ heq
    simp only [embed, Fin.mk.injEq] at heq
    exact Fin.ext heq
  · -- Surjectivity: for j in filter, find i in Fin n with embed i = j
    intro j hj
    -- hj : j ∈ ↑{x : Fin m | x.val < n}
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.val, hj⟩, ?_, ?_⟩
    · simp only [Finset.coe_univ, Set.mem_univ]
    · simp only [embed, Fin.eta]
  · intro i _
    simp only [embed, Fin.isLt, dite_true, Fin.eta]

/-! ## Fair Coin Measure

The fair coin measure on Cantor space is defined as the projective limit
of the finite prefix measures.
-/

/-- Projection from Cantor space to finite prefix. -/
def prefixProj (n : ℕ) : CantorSpace → (Fin n → Bool) :=
  fun f i => f i.val

/-- The prefix projection is measurable. -/
theorem prefixProj_measurable (n : ℕ) : Measurable (prefixProj n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The fair coin measure on Cantor space.

This is the unique probability measure such that:
1. Each bit is independent
2. Each bit is Bernoulli(1/2) (fair coin flip)

Mathematically, this is the product measure ∏_{i ∈ ℕ} Bernoulli(1/2),
constructed via Mathlib's `Measure.infinitePi`.
-/
noncomputable def coinMeasure : Measure CantorSpace :=
  Measure.infinitePi (fun _ : ℕ => bernoulliHalfMeasure)

/-- The fair coin measure is a probability measure. -/
instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

/-- The projection to the first n bits has the correct distribution.

Uses `Measure.infinitePi_map_restrict` and the connection to Finset.restrict.
-/
theorem coinMeasure_proj (n : ℕ) :
    coinMeasure.map (prefixProj n) = finPrefixMeasure n := by
  unfold coinMeasure finPrefixMeasure
  -- Use Measure.pi_eq to show equality
  symm
  apply Measure.pi_eq
  intro s hs
  -- Need to show: (Measure.infinitePi _).map (prefixProj n) (pi univ s) = ∏ i, bernoulliHalfMeasure (s i)
  rw [Measure.map_apply (prefixProj_measurable n) (.univ_pi hs)]
  -- Rewrite preimage using Set.pi over Finset.range n
  have h_preimage : prefixProj n ⁻¹' (Set.pi Set.univ s) =
      Set.pi (Finset.range n) (fun i => if h : i < n then s ⟨i, h⟩ else Set.univ) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, prefixProj, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro hf i hi
      simp only [hi, dite_true]
      exact hf ⟨i, hi⟩
    · intro hf ⟨i, hi⟩
      have := hf i hi
      simp only [hi, dite_true] at this
      exact this
  rw [h_preimage]
  -- Use infinitePi_pi to compute the LHS
  have h_meas : ∀ i ∈ Finset.range n, MeasurableSet ((fun i => if h : i < n then s ⟨i, h⟩ else Set.univ) i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [hi, dite_true]
    exact hs _
  have h_pi := Measure.infinitePi_pi (μ := fun _ : ℕ => bernoulliHalfMeasure)
    (s := Finset.range n) (t := fun i => if h : i < n then s ⟨i, h⟩ else Set.univ) h_meas
  rw [h_pi]
  -- Goal: ∏ i ∈ range n, bernoulliHalfMeasure (dite ...) = ∏ i : Fin n, bernoulliHalfMeasure (s i)
  rw [Finset.prod_range (fun i => bernoulliHalfMeasure (if h : i < n then s ⟨i, h⟩ else Set.univ))]
  congr 1
  ext i : 1
  simp only [Fin.isLt, dite_true, Fin.eta]

/-! ## Cylinder Sets

Cylinder sets are the basic measurable sets in Cantor space.
A cylinder set is determined by fixing finitely many coordinates.
-/

/-- A cylinder set fixing the first n coordinates to match given bits. -/
def cylinderSet (n : ℕ) (bits : Fin n → Bool) : Set CantorSpace :=
  {f : CantorSpace | ∀ i : Fin n, f i.val = bits i}

/-- Cylinder sets are measurable. -/
theorem cylinderSet_measurable (n : ℕ) (bits : Fin n → Bool) :
    MeasurableSet (cylinderSet n bits) := by
  unfold cylinderSet
  -- The set {f | ∀ i, f i = bits i} = ⋂ i, {f | f i = bits i}
  have : {f : CantorSpace | ∀ i : Fin n, f i.val = bits i} =
         ⋂ i : Fin n, {f : CantorSpace | f i.val = bits i} := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  apply MeasurableSet.iInter
  intro i
  have h : Measurable (fun f : CantorSpace => f i.val) := measurable_pi_apply i.val
  exact h (measurableSet_singleton _)

/-- The measure of a cylinder set is 2^{-n}.

This is a key property: fixing n fair coin flips has probability 2^{-n}.
-/
theorem coinMeasure_cylinderSet (n : ℕ) (bits : Fin n → Bool) :
    coinMeasure (cylinderSet n bits) = (1/2 : ℝ≥0∞)^n := by
  unfold coinMeasure cylinderSet
  -- Express the cylinder set as Set.pi over Finset.range n
  have h_eq : {f : CantorSpace | ∀ i : Fin n, f i.val = bits i} =
      Set.pi (Finset.range n) (fun i => if h : i < n then {bits ⟨i, h⟩} else Set.univ) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro hf i hi
      simp only [hi, dite_true, Set.mem_singleton_iff]
      exact hf ⟨i, hi⟩
    · intro hf ⟨i, hi⟩
      have := hf i hi
      simp only [hi, dite_true, Set.mem_singleton_iff] at this
      exact this
  rw [h_eq]
  -- Use infinitePi_pi to compute the measure
  have h_meas : ∀ i ∈ Finset.range n, MeasurableSet ((fun i => if h : i < n then {bits ⟨i, h⟩} else Set.univ) i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [hi, dite_true]
    exact measurableSet_singleton _
  have h_pi := Measure.infinitePi_pi (μ := fun _ : ℕ => bernoulliHalfMeasure)
    (s := Finset.range n) (t := fun i => if h : i < n then {bits ⟨i, h⟩} else Set.univ) h_meas
  rw [h_pi]
  -- Now compute ∏ i ∈ Finset.range n, bernoulliHalfMeasure {bits ⟨i, _⟩}
  -- Each factor is bernoulliHalf({b}) = 1/2 for any b : Bool
  have h_half : ∀ i ∈ Finset.range n, bernoulliHalfMeasure
      ((fun i => if h : i < n then {bits ⟨i, h⟩} else Set.univ) i) = (1/2 : ℝ≥0∞) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [hi, dite_true]
    unfold bernoulliHalfMeasure bernoulliHalf half
    rw [(PMF.bernoulli 2⁻¹ half_le_one).toMeasure_apply_singleton
        (bits ⟨i, hi⟩) (measurableSet_singleton _)]
    rw [PMF.bernoulli_apply]
    cases bits ⟨i, hi⟩ <;> simp
  rw [Finset.prod_congr rfl h_half]
  rw [Finset.prod_const, Finset.card_range]

/-! ## Measurable Functions on Cantor Space -/

/-- Reading the n-th bit is measurable. -/
@[fun_prop]
theorem measurable_bit (n : ℕ) : Measurable (fun f : CantorSpace => f n) :=
  measurable_pi_apply n

/-- The first n bits as a function. -/
def firstNBits (n : ℕ) : CantorSpace → Fin n → Bool :=
  prefixProj n

/-- Taking the first n bits is measurable. -/
theorem measurable_firstNBits (n : ℕ) : Measurable (firstNBits n) :=
  prefixProj_measurable n

end Mettapedia.Computability
