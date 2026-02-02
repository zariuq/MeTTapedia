/-
LLM Context:
- PLN Fuzzy-OR = Noisy-OR semantics for independent causes
- Multi-cause: 1 - Π(1 - s_i) = iterated fuzzy-OR
- Connects PLN disjunction to causal Bayesian networks
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# PLN Noisy-OR Semantics

This file proves that **PLN Fuzzy-OR equals Noisy-OR semantics** for combining
independent uncertain causes.

## Noisy-OR Model

In causal Bayesian networks, the Noisy-OR model assumes:
- Multiple causes C₁, ..., Cₙ can independently trigger an effect E
- Each cause Cᵢ has probability pᵢ of triggering E when active
- Causes act independently (no interaction effects)

The Noisy-OR formula:
```
P(E = 1 | active causes) = 1 - Π(1 - pᵢ) for active Cᵢ
```

## PLN Fuzzy-OR

PLN's inclusion-exclusion formula under independence:
```
s_{A∨B} = s_A + s_B - s_A × s_B
```

## Main Theorem

**PLN Fuzzy-OR = Noisy-OR**: The formulas are algebraically identical.

```
s_A + s_B - s_A × s_B = 1 - (1 - s_A)(1 - s_B)
```

This proves that PLN disjunction correctly implements Noisy-OR causal reasoning.

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988), Ch. 4
- Goertzel et al., "Probabilistic Logic Networks" (2009), Ch. 10.6.2
- Díez & Druzdzel, "Canonical Probabilistic Models for Knowledge Engineering" (2007)
-/

namespace Mettapedia.Logic.PLNNoisyOr

/-! ## Basic Noisy-OR Formulas -/

section NoisyOrBasics

/-- Noisy-OR formula for two causes.

    P(effect | cause₁ active, cause₂ active) = 1 - (1 - p₁)(1 - p₂)

    where pᵢ is the probability that cause i triggers the effect. -/
noncomputable def noisyOr2 (p₁ p₂ : ℝ) : ℝ :=
  1 - (1 - p₁) * (1 - p₂)

/-- PLN Fuzzy-OR (inclusion-exclusion under independence).

    s_{A∨B} = s_A + s_B - s_A × s_B -/
noncomputable def fuzzyOr2 (s₁ s₂ : ℝ) : ℝ :=
  s₁ + s₂ - s₁ * s₂

/-- **KEY THEOREM**: PLN Fuzzy-OR equals Noisy-OR.

    s₁ + s₂ - s₁ × s₂ = 1 - (1 - s₁)(1 - s₂)

    This is the fundamental identity connecting PLN to causal reasoning. -/
theorem fuzzyOr_eq_noisyOr (s₁ s₂ : ℝ) :
    fuzzyOr2 s₁ s₂ = noisyOr2 s₁ s₂ := by
  unfold fuzzyOr2 noisyOr2
  ring

/-- Fuzzy-OR is commutative. -/
theorem fuzzyOr2_comm (s₁ s₂ : ℝ) : fuzzyOr2 s₁ s₂ = fuzzyOr2 s₂ s₁ := by
  unfold fuzzyOr2; ring

/-- Fuzzy-OR is associative. -/
theorem fuzzyOr2_assoc (s₁ s₂ s₃ : ℝ) :
    fuzzyOr2 (fuzzyOr2 s₁ s₂) s₃ = fuzzyOr2 s₁ (fuzzyOr2 s₂ s₃) := by
  unfold fuzzyOr2; ring

/-- Fuzzy-OR with 0 is identity. -/
theorem fuzzyOr2_zero_left (s : ℝ) : fuzzyOr2 0 s = s := by
  unfold fuzzyOr2; ring

theorem fuzzyOr2_zero_right (s : ℝ) : fuzzyOr2 s 0 = s := by
  unfold fuzzyOr2; ring

/-- Fuzzy-OR with 1 is 1 (certain cause triggers effect). -/
theorem fuzzyOr2_one_left (s : ℝ) : fuzzyOr2 1 s = 1 := by
  unfold fuzzyOr2; ring

theorem fuzzyOr2_one_right (s : ℝ) : fuzzyOr2 s 1 = 1 := by
  unfold fuzzyOr2; ring

/-- Noisy-OR output is in [0,1] when inputs are in [0,1]. -/
theorem noisyOr2_mem_unit (s₁ s₂ : ℝ) (h₁ : 0 ≤ s₁) (h₁' : s₁ ≤ 1)
    (h₂ : 0 ≤ s₂) (h₂' : s₂ ≤ 1) :
    0 ≤ noisyOr2 s₁ s₂ ∧ noisyOr2 s₁ s₂ ≤ 1 := by
  unfold noisyOr2
  constructor
  · -- 0 ≤ 1 - (1-s₁)(1-s₂)
    have h1 : 0 ≤ 1 - s₁ := by linarith
    have h2 : 0 ≤ 1 - s₂ := by linarith
    have h3 : (1 - s₁) * (1 - s₂) ≤ 1 := by
      have ha : 1 - s₁ ≤ 1 := by linarith
      have hb : 1 - s₂ ≤ 1 := by linarith
      calc (1 - s₁) * (1 - s₂) ≤ 1 * 1 := by apply mul_le_mul ha hb h2 (by linarith)
        _ = 1 := by ring
    linarith
  · -- 1 - (1-s₁)(1-s₂) ≤ 1
    have h1 : 0 ≤ 1 - s₁ := by linarith
    have h2 : 0 ≤ 1 - s₂ := by linarith
    have h3 : 0 ≤ (1 - s₁) * (1 - s₂) := mul_nonneg h1 h2
    linarith

/-- Fuzzy-OR output is in [0,1] when inputs are in [0,1]. -/
theorem fuzzyOr2_mem_unit (s₁ s₂ : ℝ) (h₁ : 0 ≤ s₁) (h₁' : s₁ ≤ 1)
    (h₂ : 0 ≤ s₂) (h₂' : s₂ ≤ 1) :
    0 ≤ fuzzyOr2 s₁ s₂ ∧ fuzzyOr2 s₁ s₂ ≤ 1 := by
  rw [fuzzyOr_eq_noisyOr]
  exact noisyOr2_mem_unit s₁ s₂ h₁ h₁' h₂ h₂'

end NoisyOrBasics

/-! ## Multi-Cause Noisy-OR -/

section MultiCause

/-- Noisy-OR for multiple causes using product form.

    P(effect | causes) = 1 - Π(1 - pᵢ) -/
noncomputable def noisyOrMulti (strengths : List ℝ) : ℝ :=
  1 - strengths.foldl (fun acc s => acc * (1 - s)) 1

/-- Iterated Fuzzy-OR for multiple causes. -/
noncomputable def fuzzyOrMulti (strengths : List ℝ) : ℝ :=
  strengths.foldl fuzzyOr2 0

/-- Empty list gives 0 (no causes = no effect). -/
theorem noisyOrMulti_nil : noisyOrMulti [] = 0 := by
  unfold noisyOrMulti
  simp [List.foldl]

theorem fuzzyOrMulti_nil : fuzzyOrMulti [] = 0 := by
  unfold fuzzyOrMulti
  simp [List.foldl]

/-- Single cause: just that probability. -/
theorem noisyOrMulti_singleton (s : ℝ) : noisyOrMulti [s] = s := by
  unfold noisyOrMulti
  simp [List.foldl]

theorem fuzzyOrMulti_singleton (s : ℝ) : fuzzyOrMulti [s] = s := by
  unfold fuzzyOrMulti
  simp [List.foldl, fuzzyOr2_zero_left]

/-- Two causes: reduces to binary case. -/
theorem noisyOrMulti_two (s₁ s₂ : ℝ) : noisyOrMulti [s₁, s₂] = noisyOr2 s₁ s₂ := by
  unfold noisyOrMulti noisyOr2
  simp [List.foldl]

theorem fuzzyOrMulti_two (s₁ s₂ : ℝ) : fuzzyOrMulti [s₁, s₂] = fuzzyOr2 s₁ s₂ := by
  unfold fuzzyOrMulti
  simp [List.foldl, fuzzyOr2_zero_left]

/-- Helper: foldl with multiplicative accumulator. -/
theorem foldl_mul_one_sub_init (init : ℝ) (xs : List ℝ) :
    xs.foldl (fun acc s => acc * (1 - s)) init =
    init * xs.foldl (fun acc s => acc * (1 - s)) 1 := by
  induction xs generalizing init with
  | nil => simp [List.foldl]
  | cons x tail ih =>
    simp only [List.foldl_cons]
    rw [ih (init * (1 - x)), ih (1 * (1 - x))]
    ring

/-- Key invariant: fuzzyOr2 accumulator relates to product via complementation.

    foldl fuzzyOr2 a rest = 1 - (1-a) × Π(1-sᵢ) -/
theorem foldl_fuzzyOr2_eq_one_sub_prod (a : ℝ) (rest : List ℝ) :
    rest.foldl fuzzyOr2 a = 1 - (1 - a) * rest.foldl (fun acc s => acc * (1 - s)) 1 := by
  induction rest generalizing a with
  | nil =>
    simp only [List.foldl_nil, mul_one]
    ring
  | cons s tail ih =>
    simp only [List.foldl_cons]
    rw [ih (fuzzyOr2 a s)]
    -- Need: 1 - fuzzyOr2 a s = (1-a)(1-s)
    have h1 : 1 - fuzzyOr2 a s = (1 - a) * (1 - s) := by
      unfold fuzzyOr2; ring
    rw [h1]
    -- RHS has foldl with init (1*(1-s)); simplify to (1-s)
    simp only [one_mul]
    -- Use the fold init helper
    rw [foldl_mul_one_sub_init (1 - s) tail]
    ring

/-- **Multi-Cause Equivalence**: Iterated fuzzy-OR equals Noisy-OR product form.

    This is proven by showing both compute 1 - Π(1 - sᵢ). -/
theorem fuzzyOrMulti_eq_noisyOrMulti (strengths : List ℝ) :
    fuzzyOrMulti strengths = noisyOrMulti strengths := by
  unfold fuzzyOrMulti noisyOrMulti
  rw [foldl_fuzzyOr2_eq_one_sub_prod 0 strengths]
  simp

end MultiCause

/-! ## Noisy-OR Weight Conversion -/

section WeightConversion

/-- Convert Noisy-OR edge weight to PLN strength.

    In Noisy-OR networks: P(effect | single active parent) = 1 - exp(-w)
    This IS the PLN strength for that causal link. -/
noncomputable def weightToStrength (w : ℝ) : ℝ :=
  1 - Real.exp (-w)

/-- Weight 0 gives strength 0 (no causal influence). -/
theorem weightToStrength_zero : weightToStrength 0 = 0 := by
  unfold weightToStrength
  simp [Real.exp_zero]

/-- Positive weight gives positive strength. -/
theorem weightToStrength_pos (w : ℝ) (hw : 0 < w) : 0 < weightToStrength w := by
  unfold weightToStrength
  have h : Real.exp (-w) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- Strength is always < 1 for finite weight. -/
theorem weightToStrength_lt_one (w : ℝ) : weightToStrength w < 1 := by
  unfold weightToStrength
  have h : 0 < Real.exp (-w) := Real.exp_pos _
  linarith

/-- Strength is in [0, 1) for non-negative weight. -/
theorem weightToStrength_mem_unit (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ weightToStrength w ∧ weightToStrength w < 1 := by
  constructor
  · unfold weightToStrength
    have h : Real.exp (-w) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith
  · exact weightToStrength_lt_one w

/-- As weight → ∞, strength → 1. -/
theorem weightToStrength_tendsto_one :
    Filter.Tendsto weightToStrength Filter.atTop (nhds 1) := by
  unfold weightToStrength
  have h : Filter.Tendsto (fun w => Real.exp (-w)) Filter.atTop (nhds 0) := by
    have key : Filter.Tendsto (fun w : ℝ => -w) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot
    exact Real.tendsto_exp_atBot.comp key
  have h2 : Filter.Tendsto (fun w => 1 - Real.exp (-w)) Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.const_sub 1 h
  simp only [sub_zero] at h2
  exact h2

end WeightConversion

/-! ## Consistency Theorem for Topic Inference -/

section TopicInference

/-- Evidence for a topic based on word observation.

    If word w is connected to topic t with strength s:
    - w=1 (observed): positive evidence for t being active
    - w=0 (not observed): weak negative evidence

    This mirrors the PLN evidence aggregation in the Python implementation. -/
structure TopicEvidence where
  pos : ℝ
  neg : ℝ
  pos_nonneg : 0 ≤ pos
  neg_nonneg : 0 ≤ neg

/-- Aggregate evidence using PLN hplus (addition). -/
def hplus (e₁ e₂ : TopicEvidence) : TopicEvidence where
  pos := e₁.pos + e₂.pos
  neg := e₁.neg + e₂.neg
  pos_nonneg := add_nonneg e₁.pos_nonneg e₂.pos_nonneg
  neg_nonneg := add_nonneg e₁.neg_nonneg e₂.neg_nonneg

/-- PLN strength from topic evidence. -/
noncomputable def toStrength (e : TopicEvidence) : ℝ :=
  if e.pos + e.neg = 0 then 0.5  -- No evidence → uniform
  else e.pos / (e.pos + e.neg)

/-- Strength is in [0, 1]. -/
theorem toStrength_mem_unit (e : TopicEvidence) :
    0 ≤ toStrength e ∧ toStrength e ≤ 1 := by
  unfold toStrength
  split_ifs with h
  · constructor <;> norm_num
  · constructor
    · apply div_nonneg e.pos_nonneg
      linarith [e.pos_nonneg, e.neg_nonneg]
    · have hsum_nonneg : 0 ≤ e.pos + e.neg := add_nonneg e.pos_nonneg e.neg_nonneg
      have hsum_pos : 0 < e.pos + e.neg := lt_of_le_of_ne hsum_nonneg (Ne.symm h)
      rw [div_le_one hsum_pos]
      linarith [e.neg_nonneg]

/-- hplus is commutative. -/
theorem hplus_comm (e₁ e₂ : TopicEvidence) :
    hplus e₁ e₂ = hplus e₂ e₁ := by
  simp only [hplus, add_comm]

/-- hplus is associative. -/
theorem hplus_assoc (e₁ e₂ e₃ : TopicEvidence) :
    hplus (hplus e₁ e₂) e₃ = hplus e₁ (hplus e₂ e₃) := by
  simp only [hplus, add_assoc]

/-- **Convergence**: As evidence grows, strength converges to true ratio.

    If true proportion of positive evidence is p, then toStrength(aggregate evidence) → p
    at rate O(1/n). Specifically, |k/n - p| ≤ 1/n for k = ⌊p × n⌋.

    This is a discretization bound: floor(p*n)/n is within 1/n of p. -/
theorem topic_strength_converges (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    let k := ⌊p * n⌋₊
    let m := n - k
    let e : TopicEvidence := ⟨k, m, by exact Nat.cast_nonneg k, by exact Nat.cast_nonneg m⟩
    |toStrength e - p| ≤ 1 / n := by
  intro k m e
  -- k = floor(p * n), so k ≤ p * n ≤ n (since p ≤ 1)
  have hk_le_n : k ≤ n := by
    apply Nat.floor_le_of_le
    calc p * ↑n ≤ 1 * ↑n := by nlinarith [hp']
      _ = ↑n := by ring
  -- k + m = n in ℕ (since m = n - k and k ≤ n)
  have hkm_nat : k + m = n := by
    simp only [m]
    exact Nat.add_sub_cancel' hk_le_n
  -- k + m = n in ℝ
  have hkm : (k : ℝ) + m = n := by
    have := hkm_nat
    exact_mod_cast this
  -- toStrength e = k / n (since k + m = n > 0)
  have hne : ¬ ((k : ℝ) + m = 0) := by
    rw [hkm]
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  unfold toStrength
  rw [if_neg hne, hkm]
  -- Now prove |k/n - p| ≤ 1/n
  -- We have: p * n - 1 < floor(p * n) ≤ p * n
  -- So: (p * n - 1)/n < k/n ≤ p
  -- i.e.: p - 1/n < k/n ≤ p
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpn_nonneg : 0 ≤ p * n := mul_nonneg hp (Nat.cast_nonneg n)
  have hk_le : (k : ℝ) ≤ p * n := Nat.floor_le hpn_nonneg
  have hk_gt : p * n - 1 < k := Nat.sub_one_lt_floor (p * n)
  -- Upper bound: k/n ≤ p
  have hub : k / n ≤ p := by
    rw [div_le_iff₀ hn_pos]
    exact hk_le
  -- Lower bound: p - 1/n < k/n
  have hlb : p - 1 / n < k / n := by
    have h1 : (k : ℝ) / n + 1 / n = (k + 1) / n := by field_simp
    rw [sub_lt_iff_lt_add, h1, lt_div_iff₀ hn_pos]
    -- Goal: p * n < k + 1
    have h2 : p * n - 1 < k := hk_gt
    linarith
  -- Combine: |k/n - p| = p - k/n ≤ 1/n
  have hdiff : k / n - p ≤ 0 := by linarith [hub]
  have hdiff' : -(1 / n) < k / n - p := by linarith [hlb]
  rw [abs_le]
  constructor
  · linarith [hdiff']
  · linarith [hdiff]

end TopicInference

/-! ## Summary

**Main Results:**

1. `fuzzyOr_eq_noisyOr`: PLN Fuzzy-OR = Noisy-OR semantics
   ```
   s₁ + s₂ - s₁ × s₂ = 1 - (1 - s₁)(1 - s₂)
   ```

2. `fuzzyOr2_mem_unit`: Fuzzy-OR preserves [0,1] bounds

3. `weightToStrength`: Noisy-OR edge weights convert to PLN strengths
   ```
   strength = 1 - exp(-weight)
   ```

4. `topic_strength_converges`: Evidence aggregation converges at O(1/n) rate

**Conclusion:**

PLN's disjunction rule correctly implements Noisy-OR causal reasoning.
This provides formal justification for using PLN in Bayesian network inference,
particularly for topic models and other multi-cause scenarios.

The "Gödel machine" aspect: PLN can now provably reason about its own
correctness for Noisy-OR inference, not just Beta-Bernoulli estimation.
-/

end Mettapedia.Logic.PLNNoisyOr
