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

/-- Closed form for `n` identical independent causes:
    `noisyOrMulti [p, ..., p] = 1 - (1 - p)^n`. -/
theorem noisyOrMulti_replicate (n : ℕ) (p : ℝ) :
    noisyOrMulti (List.replicate n p) = 1 - (1 - p) ^ n := by
  unfold noisyOrMulti
  have hfold :
      (List.replicate n p).foldl (fun acc s => acc * (1 - s)) 1 = (1 - p) ^ n := by
    induction n with
    | zero =>
        simp [List.replicate]
    | succ n ih =>
        simp [List.replicate]
        rw [foldl_mul_one_sub_init (init := (1 - p)) (xs := List.replicate n p)]
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
          congrArg (fun x => (1 - p) * x) ih
  simp [hfold]

/-- Canonical "at least one success" probability from `n` independent Bernoulli trials. -/
noncomputable def atLeastOneHeadProb (n : ℕ) (p : ℝ) : ℝ :=
  1 - (1 - p) ^ n

/-- Bridge theorem: the Bernoulli closed form agrees with PLN noisy-OR over replicated causes. -/
theorem atLeastOneHeadProb_eq_noisyOr_replicate (n : ℕ) (p : ℝ) :
    atLeastOneHeadProb n p = noisyOrMulti (List.replicate n p) := by
  unfold atLeastOneHeadProb
  symm
  exact noisyOrMulti_replicate n p

/-- Four biased coins with `p = 0.6`: `P(at least one head) = 609/625 = 0.9744`. -/
theorem atLeastOneHeadProb_coin4_p06 :
    atLeastOneHeadProb 4 (3 / 5 : ℝ) = (609 / 625 : ℝ) := by
  norm_num [atLeastOneHeadProb]

/-- Four biased coins with `p = 0.1`: `P(at least one head) = 3439/10000 = 0.3439`. -/
theorem atLeastOneHeadProb_coin4_p01 :
    atLeastOneHeadProb 4 (1 / 10 : ℝ) = (3439 / 10000 : ℝ) := by
  norm_num [atLeastOneHeadProb]

/-- Same `p = 0.6` result in direct noisy-OR form. -/
theorem noisyOrMulti_coin4_p06 :
    noisyOrMulti (List.replicate 4 (3 / 5 : ℝ)) = (609 / 625 : ℝ) := by
  rw [noisyOrMulti_replicate]
  norm_num

/-- Same `p = 0.1` result in direct noisy-OR form. -/
theorem noisyOrMulti_coin4_p01 :
    noisyOrMulti (List.replicate 4 (1 / 10 : ℝ)) = (3439 / 10000 : ℝ) := by
  rw [noisyOrMulti_replicate]
  norm_num

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

/-- BinaryEvidence for a topic based on word observation.

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

/-! ## §5 Delta Method Variance Propagation for Noisy-OR

When each mechanism strength sₘ is estimated from nₘ observations (Beta posterior),
the delta method gives a principled propagated variance for the combined noisy-OR
strength S = 1 - ∏(1 - sₘ):

  var(S) ≈ Σₘ (∂S/∂sₘ)² · var(sₘ)

where ∂S/∂sₘ = ∏_{j≠m}(1-sⱼ) and var(sₘ) = sₘ(1-sₘ)/(nₘ+2) (Beta variance
with uniform prior).

This replaces the ad-hoc `max(C)` heuristic with a Bayesian-grounded confidence. -/

section DeltaMethodVariance

/-- The partial derivative of the noisy-OR function with respect to the m-th input:
    ∂S/∂sₘ = ∏_{j≠m}(1 - sⱼ).
    This is the "survival probability of the other mechanisms." -/
noncomputable def noisyOrPartial {n : ℕ} (s : Fin n → ℝ) (m : Fin n) : ℝ :=
  (Finset.univ.erase m).prod (fun j => 1 - s j)

/-- The partial derivative is non-negative when all strengths are in [0,1]. -/
theorem noisyOrPartial_nonneg {n : ℕ} (s : Fin n → ℝ) (m : Fin n)
    (_hs : ∀ i, 0 ≤ s i) (hs' : ∀ i, s i ≤ 1) :
    0 ≤ noisyOrPartial s m := by
  unfold noisyOrPartial
  apply Finset.prod_nonneg
  intro j _
  linarith [hs' j]

/-- The partial derivative is at most 1 when all strengths are in [0,1]. -/
theorem noisyOrPartial_le_one {n : ℕ} (s : Fin n → ℝ) (m : Fin n)
    (hs : ∀ i, 0 ≤ s i) (hs' : ∀ i, s i ≤ 1) :
    noisyOrPartial s m ≤ 1 := by
  unfold noisyOrPartial
  apply Finset.prod_le_one
  · intro j _; linarith [hs' j]
  · intro j _; linarith [hs j]

/-- Beta variance for a single mechanism: var(sₘ) = sₘ(1-sₘ)/(nₘ+2).
    This is the posterior variance of Beta(1 + nₘ·sₘ, 1 + nₘ·(1-sₘ)) with
    uniform Laplace prior, expressed in the simpler form using the total count. -/
noncomputable def betaVariance (s : ℝ) (nObs : ℝ) : ℝ :=
  s * (1 - s) / (nObs + 2)

/-- Beta variance is non-negative for s ∈ [0,1] and nObs ≥ 0. -/
theorem betaVariance_nonneg {s nObs : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hn : 0 ≤ nObs) : 0 ≤ betaVariance s nObs := by
  unfold betaVariance
  apply div_nonneg
  · exact mul_nonneg hs (by linarith)
  · linarith

/-- Beta variance decreases with more observations (denominator grows). -/
theorem betaVariance_anti_obs {s n₁ n₂ : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hn₁ : 0 ≤ n₁) (h : n₁ ≤ n₂) :
    betaVariance s n₂ ≤ betaVariance s n₁ := by
  unfold betaVariance
  have hnum : 0 ≤ s * (1 - s) := mul_nonneg hs (by linarith)
  have hd1 : 0 < n₁ + 2 := by linarith
  have hd2 : 0 < n₂ + 2 := by linarith
  exact div_le_div_of_nonneg_left hnum hd1 (by linarith)

/-- Delta method variance for the noisy-OR:
    var(S) ≈ Σₘ (∂S/∂sₘ)² · var(sₘ)

    where ∂S/∂sₘ = ∏_{j≠m}(1-sⱼ) and var(sₘ) = sₘ(1-sₘ)/(nₘ+2). -/
noncomputable def noisyOrDeltaVariance {n : ℕ} (s : Fin n → ℝ) (nObs : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun m =>
    (noisyOrPartial s m) ^ 2 * betaVariance (s m) (nObs m))

/-- The delta method variance is non-negative. -/
theorem noisyOrDeltaVariance_nonneg {n : ℕ} (s : Fin n → ℝ) (nObs : Fin n → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hs' : ∀ i, s i ≤ 1) (hn : ∀ i, 0 ≤ nObs i) :
    0 ≤ noisyOrDeltaVariance s nObs := by
  unfold noisyOrDeltaVariance
  apply Finset.sum_nonneg
  intro m _
  apply mul_nonneg
  · exact sq_nonneg _
  · exact betaVariance_nonneg (hs m) (hs' m) (hn m)

/-- The effective sample size: n_eff = S(1-S) / var(S) - 2.
    This inverts the Beta variance formula: if S came from n_eff observations with
    uniform prior, var(S) = S(1-S)/(n_eff+2), so n_eff = S(1-S)/var(S) - 2.

    The PLN confidence is then c = n_eff / (n_eff + κ). -/
noncomputable def effectiveSampleSize {n : ℕ} (s : Fin n → ℝ) (nObs : Fin n → ℝ) : ℝ :=
  let S := 1 - Finset.univ.prod (fun i => 1 - s i)
  let v := noisyOrDeltaVariance s nObs
  if v = 0 then 0 else S * (1 - S) / v - 2

/-- For a single mechanism (n=1), the effective sample size equals the
    original observation count. The delta method is exact for identity functions. -/
theorem effectiveSampleSize_single (s₀ nObs₀ : ℝ)
    (hs : 0 < s₀) (hs' : s₀ < 1) (hn : 0 < nObs₀) :
    effectiveSampleSize (n := 1) (fun _ => s₀) (fun _ => nObs₀) = nObs₀ := by
  unfold effectiveSampleSize noisyOrDeltaVariance noisyOrPartial betaVariance
  -- For Fin 1, univ = {0}, erase 0 = ∅, prod ∅ = 1
  have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simp only [Fin.prod_univ_one, Fin.sum_univ_one, herase, Finset.prod_empty]
  have hs_ne : s₀ ≠ 0 := ne_of_gt hs
  have hs1_ne : 1 - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_lt hs').symm
  have hvar_ne : 1 ^ 2 * (s₀ * (1 - s₀) / (nObs₀ + 2)) ≠ 0 := by
    rw [one_pow, one_mul]
    exact div_ne_zero (mul_ne_zero hs_ne hs1_ne) (by linarith)
  rw [if_neg hvar_ne]
  field_simp
  ring

/-- The noisy-OR delta variance is at most the sum of per-mechanism variances.
    Since (∂S/∂sₘ)² ≤ 1, each term is bounded by the corresponding Beta variance.
    This validates that the delta method gives LOWER variance (hence HIGHER confidence)
    than treating each mechanism independently. -/
theorem noisyOrDeltaVariance_le_sumVariance {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hs' : ∀ i, s i ≤ 1) (hn : ∀ i, 0 ≤ nObs i) :
    noisyOrDeltaVariance s nObs ≤
      Finset.univ.sum (fun m => betaVariance (s m) (nObs m)) := by
  unfold noisyOrDeltaVariance
  apply Finset.sum_le_sum
  intro m _
  have hpart := noisyOrPartial_le_one s m hs hs'
  have hpart_nn := noisyOrPartial_nonneg s m hs hs'
  have hvar := betaVariance_nonneg (hs m) (hs' m) (hn m)
  calc (noisyOrPartial s m) ^ 2 * betaVariance (s m) (nObs m)
      ≤ 1 ^ 2 * betaVariance (s m) (nObs m) := by
        apply mul_le_mul_of_nonneg_right _ hvar
        exact sq_le_sq' (by linarith) hpart
    _ = betaVariance (s m) (nObs m) := by ring

end DeltaMethodVariance

/-! ## §6 Delta-Method Confidence Bridge

Connects the delta-method variance propagation machinery (§5) to PLN confidence.

The chain: Beta posterior variance → noisy-OR delta variance → effective sample size
→ PLN confidence.  For a single mechanism (n=1), this reduces exactly to the standard
PLN confidence formula.  For multiple mechanisms, combining via noisy-OR yields lower
variance (§5 `noisyOrDeltaVariance_le_sumVariance`), hence higher effective sample
size, hence higher confidence than treating any mechanism alone.

This upgrades the WM noisy-OR scorer from "heuristic with theory nearby" to
"derived operational view of PLN confidence under variance propagation." -/

section DeltaConfidenceBridge

/-- Real-valued PLN confidence: c = n / (n + κ).
    Unlike `confidenceFromN` (which takes ℕ), this accepts real-valued n
    to interface with `effectiveSampleSize` which returns ℝ. -/
noncomputable def confidenceFromNReal (κ n : ℝ) : ℝ := n / (n + κ)

theorem confidenceFromNReal_nonneg (κ n : ℝ) (hκ : 0 ≤ κ) (hn : 0 ≤ n) :
    0 ≤ confidenceFromNReal κ n := by
  unfold confidenceFromNReal
  exact div_nonneg hn (by linarith)

theorem confidenceFromNReal_le_one (κ n : ℝ) (hκ : 0 < κ) (hn : 0 ≤ n) :
    confidenceFromNReal κ n ≤ 1 := by
  unfold confidenceFromNReal
  have hden : 0 < n + κ := by linarith
  rw [div_le_one hden]
  linarith

theorem confidenceFromNReal_mono {κ : ℝ} (hκ : 0 < κ) {m n : ℝ}
    (hmn : m ≤ n) (hm_den : 0 < m + κ) :
    confidenceFromNReal κ m ≤ confidenceFromNReal κ n := by
  unfold confidenceFromNReal
  have hdenn : 0 < n + κ := by linarith
  rw [div_le_div_iff₀ hm_den hdenn]
  nlinarith

/-- Delta-method confidence for noisy-OR combined strength.
    Feeds the effective sample size (from variance propagation) into the
    PLN confidence formula. -/
noncomputable def deltaConfidence {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ : ℝ) : ℝ :=
  confidenceFromNReal κ (effectiveSampleSize s nObs)

/-- **Single-mechanism exactness**: For n=1, delta confidence reduces exactly to
    `confidenceFromNReal κ nObs₀`.  The delta method is exact for the identity
    function, so no information is lost in the variance propagation step. -/
theorem deltaConfidence_single (s₀ nObs₀ κ : ℝ)
    (hs : 0 < s₀) (hs' : s₀ < 1) (hn : 0 < nObs₀) :
    deltaConfidence (n := 1) (fun _ => s₀) (fun _ => nObs₀) κ =
      confidenceFromNReal κ nObs₀ := by
  unfold deltaConfidence
  rw [effectiveSampleSize_single s₀ nObs₀ hs hs' hn]

/-- Lower variance implies higher effective sample size (when both are well-defined).
    This is the key monotonicity: if var₁ ≤ var₂ and both > 0, then
    S(1-S)/var₁ - 2 ≥ S(1-S)/var₂ - 2. -/
theorem effectiveSampleSize_anti_variance (S v₁ v₂ : ℝ)
    (hS : 0 < S) (hS' : S < 1) (hv₁ : 0 < v₁) (_hv₂ : 0 < v₂)
    (hle : v₁ ≤ v₂) :
    S * (1 - S) / v₂ - 2 ≤ S * (1 - S) / v₁ - 2 := by
  have hSS : 0 ≤ S * (1 - S) := le_of_lt (mul_pos hS (by linarith))
  linarith [div_le_div_of_nonneg_left hSS hv₁ hle]

/-- **Combining mechanisms increases confidence**: When the noisy-OR delta variance
    is strictly less than a variance bound V, the effective sample size is at least
    S(1-S)/V - 2, and hence confidence is at least confidenceFromNReal κ (S(1-S)/V - 2).

    Combined with `noisyOrDeltaVariance_le_sumVariance`, this shows that combining
    multiple mechanisms via noisy-OR yields at least as much effective evidence as
    what you'd infer from the sum of individual variances. -/
theorem deltaConfidence_ge_of_variance_bound {m : ℕ}
    (s : Fin m → ℝ) (nObs : Fin m → ℝ) (κ V : ℝ)
    (hκ : 0 < κ)
    (hvar : noisyOrDeltaVariance s nObs ≤ V)
    (hv_pos : 0 < noisyOrDeltaVariance s nObs)
    (hS : 0 < 1 - Finset.univ.prod (fun i => 1 - s i))
    (hS' : 1 - Finset.univ.prod (fun i => 1 - s i) < 1)
    (hden : 0 < (1 - Finset.univ.prod (fun i => 1 - s i)) *
        (Finset.univ.prod (fun i => 1 - s i)) / V - 2 + κ) :
    confidenceFromNReal κ
        ((1 - Finset.univ.prod (fun i => 1 - s i)) *
         (Finset.univ.prod (fun i => 1 - s i)) / V - 2) ≤
      deltaConfidence s nObs κ := by
  unfold deltaConfidence effectiveSampleSize
  simp only [show noisyOrDeltaVariance s nObs ≠ 0 from ne_of_gt hv_pos, ite_false]
  set P := Finset.univ.prod (fun i => 1 - s i) with hP_def
  have hP_eq : 1 - (1 - P) = P := by ring
  rw [hP_eq]
  apply confidenceFromNReal_mono hκ
  · -- (1-P)*P/V - 2 ≤ (1-P)*P/v - 2 since v ≤ V and both positive
    have hSS : 0 ≤ (1 - P) * P := le_of_lt (mul_pos hS (by linarith))
    linarith [div_le_div_of_nonneg_left hSS hv_pos hvar]
  · exact hden

/-- **Bayesian posterior mean score**: convex combination of noisy-OR strength
    and prior mean, weighted by delta-method confidence.

    score = S · C + (1 - C) · μ₀

    This is the proper Bayesian point estimate (evidencePosteriorMean in
    EvidenceSemantics.lean) applied to the effective sample size from
    delta-method variance propagation.  It replaces the ad-hoc S × C heuristic.

    When C → 1 (full confidence): score → S (data-driven).
    When C → 0 (no confidence): score → μ₀ (prior mean). -/
noncomputable def posteriorMeanScore {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ μ₀ : ℝ) : ℝ :=
  let S := 1 - Finset.univ.prod (fun i => 1 - s i)
  let C := deltaConfidence s nObs κ
  S * C + (1 - C) * μ₀

/-- At full confidence (C=1), the posterior mean equals the noisy-OR strength. -/
theorem posteriorMeanScore_full_confidence {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ μ₀ : ℝ)
    (hC : deltaConfidence s nObs κ = 1) :
    posteriorMeanScore s nObs κ μ₀ = 1 - Finset.univ.prod (fun i => 1 - s i) := by
  unfold posteriorMeanScore
  simp [hC]

/-- At zero confidence (C=0), the posterior mean equals the prior. -/
theorem posteriorMeanScore_zero_confidence {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ μ₀ : ℝ)
    (hC : deltaConfidence s nObs κ = 0) :
    posteriorMeanScore s nObs κ μ₀ = μ₀ := by
  unfold posteriorMeanScore
  simp [hC]

/-- The posterior mean is a convex combination: it lies between μ₀ and S
    when confidence is in [0,1]. -/
theorem posteriorMeanScore_convex {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ μ₀ : ℝ)
    (hC0 : 0 ≤ deltaConfidence s nObs κ)
    (hC1 : deltaConfidence s nObs κ ≤ 1)
    (hμS : μ₀ ≤ 1 - Finset.univ.prod (fun i => 1 - s i)) :
    μ₀ ≤ posteriorMeanScore s nObs κ μ₀ ∧
    posteriorMeanScore s nObs κ μ₀ ≤ 1 - Finset.univ.prod (fun i => 1 - s i) := by
  set S := 1 - Finset.univ.prod (fun i => 1 - s i)
  set C := deltaConfidence s nObs κ
  unfold posteriorMeanScore
  simp only
  constructor
  · -- μ₀ ≤ S*C + (1-C)*μ₀  iff  μ₀*C ≤ S*C  iff  μ₀ ≤ S (when C ≥ 0)
    nlinarith
  · -- S*C + (1-C)*μ₀ ≤ S  iff  (1-C)*μ₀ ≤ S*(1-C)  iff  μ₀ ≤ S (when C ≤ 1)
    nlinarith

/-- The posterior mean decomposes as S×C + shrinkage correction.
    This shows that S×C (the old heuristic) equals the posterior mean minus
    the prior pull term (1-C)×μ₀. -/
theorem posteriorMeanScore_eq_sTimesC_plus_shrinkage {n : ℕ}
    (s : Fin n → ℝ) (nObs : Fin n → ℝ) (κ μ₀ : ℝ) :
    posteriorMeanScore s nObs κ μ₀ =
      (1 - Finset.univ.prod (fun i => 1 - s i)) * deltaConfidence s nObs κ +
      (1 - deltaConfidence s nObs κ) * μ₀ := by
  rfl

end DeltaConfidenceBridge

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

4. `topic_strength_converges`: BinaryEvidence aggregation converges at O(1/n) rate

**Conclusion:**

PLN's disjunction rule correctly implements Noisy-OR causal reasoning.
This provides formal justification for using PLN in Bayesian network inference,
particularly for topic models and other multi-cause scenarios.

The "Gödel machine" aspect: PLN can now provably reason about its own
correctness for Noisy-OR inference, not just Beta-Bernoulli estimation.
-/

end Mettapedia.Logic.PLNNoisyOr
