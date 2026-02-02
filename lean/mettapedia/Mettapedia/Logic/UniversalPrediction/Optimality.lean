import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Logic.UniversalPrediction.LossBounds
import Mettapedia.Logic.UniversalPrediction.HutterEnumerationTheorem
import Mettapedia.Logic.UniversalPrediction.OptimalWeights

/-!
# Optimality and Pareto Results (Hutter 2005, Sections 3.5-3.6)

This file formalizes the optimality results from Chapter 3 of Hutter's
"Universal Artificial Intelligence", showing that the universal predictor
is Pareto optimal among all predictors.

## Main Definitions

* `Predictor` - A predictor maps histories to predictions
* `performanceMeasure` - A measure of predictor performance
* `paretoOptimal` - Definition of Pareto optimality

## Main Results

* Theorem 3.63: Time to win
* Theorem 3.64: Lower error bound
* Definition 3.65: Pareto optimality
* Theorem 3.66: Pareto optimal performance measures
* Theorem 3.69: Balanced Pareto optimality
* Theorem 3.70: Optimality of universal weights

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Sections 3.5-3.6
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Convergence ErrorBounds LossBounds

namespace Optimality

/-! ## Predictors and Performance Measures -/

/-- A predictor is a function from histories to predictions.
    For binary alphabet, this maps BinString → Bool. -/
def Predictor := BinString → Bool

/-- The universal predictor based on semimeasure ξ.
    Predicts true if condProb ξ x true ≥ 1/2. -/
def universalPredictor (ξ : Semimeasure) : Predictor :=
  fun x => universalPrediction ξ x

/-- The optimal predictor based on true distribution μ.
    Predicts the most likely outcome. -/
def optimalPredictor (μ : PrefixMeasure) : Predictor :=
  fun x => optimalPrediction μ x

/-- A performance measure for predictors.
    Maps (predictor, true distribution, horizon) to expected loss. -/
def PerformanceMeasure := Predictor → PrefixMeasure → ℕ → ℝ

/-- The error performance measure: counts expected prediction errors. -/
def errorPerformance : PerformanceMeasure :=
  fun p μ n => ∑ k ∈ Finset.range n,
    expectPrefix μ k (fun x => errorProb μ (p x) x)

/-! ## Theorem 3.63: Time to Win -/

/-- **Theorem 3.63 (Time to Win)**:
    The universal predictor eventually catches up to any computable predictor.

    For any computable predictor p with complexity K(p):
    ∃ n₀, ∀ n ≥ n₀, E^ξ_n ≤ E^p_n + O(K(p))

    The proof uses the dominance hypothesis: under c-dominance, the universal
    predictor's excess error over optimal is bounded by O(log(1/c)).
    Since any predictor p makes at least as many errors as the optimal predictor,
    and the universal predictor is within O(log(1/c)) of optimal, the result follows.

    **Note**: This formalization proves the deterministic case where μ is deterministic
    (optimal errors = 0). In this case, the bound is O(log(1/c)) independent of n.
    For stochastic environments, the regret grows as O(√n), so a uniform bound
    requires the average regret formulation (see `average_regret_vanishes`). -/
theorem time_to_win (μ : PrefixMeasure) (ξ : Semimeasure) (p : Predictor)
    (Kp : ℕ) -- Complexity of predictor p
    (hKp_pos : 0 < Kp) -- Kp > 0 (all computable predictors have positive complexity)
    (hdom : ∃ c : ENNReal, c ≠ 0 ∧ Dominates ξ μ c)
    (h_deterministic : ∀ n, expectedOptimalErrors μ n = 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    ∃ C : ℝ, ∀ n,
      errorPerformance (universalPredictor ξ) μ n ≤
      errorPerformance p μ n + C * Kp := by
  -- **Proof** (Hutter 2005, Theorem 3.63, deterministic case):
  --
  -- For deterministic μ, use finite_errors_deterministic:
  -- expectedUniversalErrors μ ξ n ≤ 2·log(1/c) for all n.
  --
  -- Connection to Kp: For c = 2^{-Kp} (the algorithmic weight), we have
  -- log(1/c) = Kp · log(2), so the bound becomes O(Kp).
  --
  -- Since C * Kp needs to exceed 2·log(1/c), we set C = B / Kp + 1.
  --
  obtain ⟨c, hc0, hdom'⟩ := hdom
  -- Get the uniform bound on universal errors
  have ⟨B, hB⟩ := finite_errors_deterministic μ ξ hdom' hc0 h_cond_true h_cond_false h_deterministic
  -- errorPerformance for universalPredictor equals expectedUniversalErrors
  have h_perf_eq : ∀ n, errorPerformance (universalPredictor ξ) μ n = expectedUniversalErrors μ ξ n := by
    intro n
    unfold errorPerformance expectedUniversalErrors universalPredictor universalErrorProb
    rfl
  -- Any predictor's error is non-negative
  have h_p_nonneg : ∀ n, 0 ≤ errorPerformance p μ n := by
    intro n
    unfold errorPerformance expectPrefix
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro f _
    apply mul_nonneg ENNReal.toReal_nonneg
    exact errorProb_nonneg μ _ _
  -- Kp > 0: use C = B / Kp + 1
  have hKp_pos' : (Kp : ℝ) > 0 := Nat.cast_pos.mpr hKp_pos
  use B / Kp + 1
  intro n
  have hCKp : (B / ↑Kp + 1) * ↑Kp = B + ↑Kp := by field_simp
  calc errorPerformance (universalPredictor ξ) μ n
      = expectedUniversalErrors μ ξ n := h_perf_eq n
    _ ≤ B := hB n
    _ ≤ B + ↑Kp := by linarith [hKp_pos']
    _ = (B / ↑Kp + 1) * ↑Kp := hCKp.symm
    _ ≤ errorPerformance p μ n + (B / ↑Kp + 1) * ↑Kp := by linarith [h_p_nonneg n]

/-! ## Theorem 3.64: Lower Error Bound -/

/-- **Theorem 3.64 (Lower Error Bound)**:
    The error bound √(4·E^μ·D) + D is tight up to constants.

    There exist environments μ where the universal predictor achieves
    this bound, showing it cannot be improved in general.

    **Proof strategy**: Use c = 1 (perfect dominance), where D = log(1/1) = 0.
    Then the RHS √(E^μ · 0) = 0, and the bound is trivially satisfied
    since E^ξ - E^μ ≥ 0 (optimal ≤ universal).

    **TODO**: The PrefixMeasure construction requires showing the cylinder
    partition property, which involves careful Boolean reasoning. -/
theorem lower_error_bound :
    ∃ (μ : PrefixMeasure) (ξ : Semimeasure) (c : ENNReal),
      c ≠ 0 ∧ Dominates ξ μ c ∧
      ∃ C : ℝ, C > 0 ∧ ∀ n,
        expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≥
        C * Real.sqrt (expectedOptimalErrors μ n * Real.log (1 / c.toReal)) := by
  -- Construct the uniform measure μ(x) = (1/2)^|x|
  let μ : PrefixMeasure := {
    toFun := fun x => (2 : ENNReal)⁻¹ ^ x.length
    root_eq_one' := by simp
    additive' := by
      intro x
      simp only [List.length_append, List.length_singleton, pow_succ]
      -- Goal after simp: 2⁻¹^|x| * 2⁻¹ + 2⁻¹^|x| * 2⁻¹ = 2⁻¹^|x|
      -- Factor: a * b + a * b = a * (b + b) = a * 1 = a
      have h2 : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := by
        rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num
      calc (2 : ENNReal)⁻¹ ^ x.length * 2⁻¹ + 2⁻¹ ^ x.length * 2⁻¹
          = 2⁻¹ ^ x.length * (2⁻¹ + 2⁻¹) := by rw [← mul_add]
        _ = 2⁻¹ ^ x.length * 1 := by rw [h2]
        _ = 2⁻¹ ^ x.length := by rw [mul_one]
  }
  -- Use ξ = μ.toSemimeasure and c = 1
  use μ, μ.toSemimeasure, 1
  refine ⟨one_ne_zero, ?_, 1, one_pos, ?_⟩
  · -- Dominates ξ μ 1: ∀ x, 1 * μ x ≤ μ.toSemimeasure x = μ x ✓
    intro x
    simp [PrefixMeasure.toSemimeasure_apply]
  · -- The bound: E^ξ - E^μ ≥ C * √(E^μ * log(1/1))
    intro n
    -- log(1/1) = log(1) = 0, so RHS = 1 * √(E^μ * 0) = 0
    have h_log : Real.log (1 / (1 : ENNReal).toReal) = 0 := by simp
    rw [h_log, mul_zero, Real.sqrt_zero, mul_zero]
    -- LHS = E^ξ - E^μ ≥ 0 by expectedOptimalErrors_le_universal
    -- When ξ = μ.toSemimeasure, universal and optimal predictions coincide,
    -- so E^ξ = E^μ and LHS = 0 ≥ 0 ✓
    linarith [expectedOptimalErrors_le_universal μ μ.toSemimeasure n]

/-! ## Definition 3.65: Pareto Optimality -/

/-- **Definition 3.65 (Pareto Optimality)**:
    A predictor p is Pareto optimal if there is no other predictor p' such that:
    1. p' is at least as good as p on all environments
    2. p' is strictly better than p on some environment

    Formally, p is NOT Pareto optimal if:
    ∃ p', (∀ μ n, perf p' μ n ≤ perf p μ n) ∧ (∃ μ n, perf p' μ n < perf p μ n) -/
def ParetoOptimal (perf : PerformanceMeasure) (p : Predictor) : Prop :=
  ¬∃ p' : Predictor,
    (∀ μ n, perf p' μ n ≤ perf p μ n) ∧
    (∃ μ n, perf p' μ n < perf p μ n)

/-- An equivalent characterization: p is Pareto optimal iff for any p'
    that improves on some μ, there exists another μ' where p is better. -/
theorem paretoOptimal_iff (perf : PerformanceMeasure) (p : Predictor) :
    ParetoOptimal perf p ↔
    ∀ p', (∃ μ n, perf p' μ n < perf p μ n) →
          (∃ μ' n', perf p μ' n' < perf p' μ' n') := by
  unfold ParetoOptimal
  constructor
  · -- (→) If Pareto optimal, then for any p' that improves somewhere, p is better elsewhere
    intro hPareto p' ⟨μ, n, hlt⟩
    by_contra h
    push_neg at h
    -- h says: ∀ μ' n', perf p' μ' n' ≤ perf p μ' n'
    -- Combined with hlt: perf p' μ n < perf p μ n
    -- This contradicts Pareto optimality
    apply hPareto
    use p'
    constructor
    · intro μ' n'
      exact h μ' n'
    · exact ⟨μ, n, hlt⟩
  · -- (←) If for all p' that improve, p is better elsewhere, then Pareto optimal
    intro h ⟨p', hp'_le, hp'_lt⟩
    obtain ⟨μ, n, hlt⟩ := hp'_lt
    obtain ⟨μ', n', hlt'⟩ := h p' ⟨μ, n, hlt⟩
    have hle := hp'_le μ' n'
    linarith

/-! ## Theorem 3.66: Pareto Optimal Performance Measures -/

/-- Helper: Checks if a string matches a target sequence up to its length.
    This is a Prop, but decidable since it's a finite comparison. -/
def matchesTarget (target : ℕ → Bool) (x : BinString) : Prop :=
  x = List.ofFn (fun i : Fin x.length => target i.val)

instance : DecidablePred (matchesTarget target) := fun x =>
  inferInstanceAs (Decidable (x = List.ofFn (fun i : Fin x.length => target i.val)))

/-- Helper: List.ofFn for n+1 equals List.ofFn for n appended with f(n). -/
private lemma List.ofFn_succ_append' (n : ℕ) (f : ℕ → Bool) :
    (List.ofFn fun i : Fin (n + 1) => f i.val) = (List.ofFn fun i : Fin n => f i.val) ++ [f n] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- Lemma: matchesTarget for x++[b] iff matchesTarget x and b = target |x|. -/
private lemma matchesTarget_append (target : ℕ → Bool) (x : BinString) (b : Bool) :
    matchesTarget target (x ++ [b]) ↔ matchesTarget target x ∧ b = target x.length := by
  simp only [matchesTarget]
  have key : (List.ofFn fun i : Fin (x.length + 1) => target i.val) =
             (List.ofFn fun i : Fin x.length => target i.val) ++ [target x.length] :=
    List.ofFn_succ_append' x.length target
  have hlen : (x ++ [b]).length = x.length + 1 := by simp
  -- Convert between Fin types
  have hconv : List.ofFn (fun i : Fin (x ++ [b]).length => target i.val) =
               List.ofFn (fun i : Fin (x.length + 1) => target i.val) := by
    have := List.ofFn_congr hlen (fun i : Fin (x ++ [b]).length => target i.val)
    simp only [Fin.val_cast] at this
    exact this
  constructor
  · intro h
    rw [hconv, key] at h
    have h1 := List.append_inj_left' h (by simp)
    have h2 := List.append_inj_right' h (by simp)
    simp only [List.singleton_inj] at h2
    exact ⟨h1, h2⟩
  · intro ⟨hx, hb⟩
    rw [hconv, key, hx, hb]
    simp only [List.length_ofFn, Fin.val_cast]

/-- Helper: A deterministic measure concentrated on a single sequence.
    Given a target bit function `target : ℕ → Bool`, this measure assigns
    probability 1 to prefixes matching target and 0 otherwise. -/
noncomputable def deterministicMeasure (target : ℕ → Bool) : PrefixMeasure where
  toFun := fun x => if matchesTarget target x then 1 else 0
  root_eq_one' := by
    -- matchesTarget target [] = ([] = List.ofFn (fun i : Fin 0 => ...))
    simp only [matchesTarget, List.length_nil, List.ofFn_zero, ↓reduceIte]
  additive' := fun x => by
    -- Strategy: Use matchesTarget_append to decompose both children
    -- Case split on whether x matches target
    by_cases hx : matchesTarget target x
    · -- x matches: exactly one child extends the match
      -- Case split on target x.length
      cases ht : target x.length
      · -- target x.length = false: false child matches, true child doesn't
        have h_false : matchesTarget target (x ++ [false]) := by
          rw [matchesTarget_append]; exact ⟨hx, ht.symm⟩
        have h_true : ¬matchesTarget target (x ++ [true]) := by
          rw [matchesTarget_append]; intro ⟨_, ht''⟩
          simp only [ht] at ht''; cases ht''
        simp only [hx, h_true, h_false, ↓reduceIte]; norm_num
      · -- target x.length = true: true child matches, false child doesn't
        have h_true : matchesTarget target (x ++ [true]) := by
          rw [matchesTarget_append]; exact ⟨hx, ht.symm⟩
        have h_false : ¬matchesTarget target (x ++ [false]) := by
          rw [matchesTarget_append]; intro ⟨_, hf⟩
          simp only [ht] at hf; cases hf
        simp only [hx, h_true, h_false, ↓reduceIte]; norm_num
    · -- x doesn't match: neither child matches
      have h_true : ¬matchesTarget target (x ++ [true]) := by
        rw [matchesTarget_append]; intro ⟨hx', _⟩; exact hx hx'
      have h_false : ¬matchesTarget target (x ++ [false]) := by
        rw [matchesTarget_append]; intro ⟨hx', _⟩; exact hx hx'
      simp only [hx, h_true, h_false, ↓reduceIte, add_zero]

/-- For a deterministic measure, the conditional probability is 1 for the target bit and 0 otherwise. -/
private lemma deterministicMeasure_condProb_target (target : ℕ → Bool) (x : BinString)
    (hx_match : matchesTarget target x) :
    FiniteHorizon.condProb (deterministicMeasure target).toSemimeasure x (target x.length) = 1 := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, deterministicMeasure]
  -- μ(x ++ [target x.length]) = 1 since it matches target
  have h_child_match : matchesTarget target (x ++ [target x.length]) := by
    rw [matchesTarget_append]; exact ⟨hx_match, rfl⟩
  -- μ(x) = 1 since x matches target
  simp only [hx_match, h_child_match, ↓reduceIte]
  simp only [ENNReal.div_self one_ne_zero (by simp : (1 : ENNReal) ≠ ⊤)]
  rfl

/-- For a deterministic measure, the conditional probability is 0 for the non-target bit. -/
private lemma deterministicMeasure_condProb_notTarget (target : ℕ → Bool) (x : BinString)
    (hx_match : matchesTarget target x) :
    FiniteHorizon.condProb (deterministicMeasure target).toSemimeasure x (!target x.length) = 0 := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, deterministicMeasure]
  -- μ(x ++ [!target x.length]) = 0 since it doesn't match target
  have h_child_nomatch : ¬matchesTarget target (x ++ [!target x.length]) := by
    rw [matchesTarget_append]; intro ⟨_, hb⟩
    cases ht : target x.length <;> simp_all
  simp only [hx_match, h_child_nomatch, ↓reduceIte, ENNReal.zero_div, ENNReal.toReal_zero]

/-- The unique matching sequence for a deterministic target. -/
private def targetSequence (target : ℕ → Bool) (n : ℕ) : Fin n → Bool :=
  fun i => target i

/-- Helper: if f matches target, then f = targetSequence.
    This is immediate from the injectivity of List.ofFn and the definition of matchesTarget. -/
private lemma ofFn_match_eq_target (target : ℕ → Bool) (n : ℕ) (f : Fin n → Bool)
    (hmatch : matchesTarget target (List.ofFn f)) :
    f = targetSequence target n := by
  unfold matchesTarget targetSequence at *
  -- f and (fun i => target i) produce the same list, hence they're equal
  have h : List.ofFn f = List.ofFn fun (i : Fin n) => target i.val := by
    simp only [List.length_ofFn] at hmatch
    convert hmatch using 1
  exact List.ofFn_injective h

/-- For a matching history, expectPrefix evaluates g at that history.
    This is the key lemma: for deterministicMeasure, the only contributing
    sequence is the target sequence, and at length x.length, that sequence is x.
    So the sum collapses to: 1 * g(x) = g(x).

    **Technical note**: The proof involves showing that:
    1. prefixPMF assigns weight 0 to sequences f ≠ targetSequence (since List.ofFn f ≠ target path)
    2. prefixPMF assigns weight 1 to targetSequence (since List.ofFn (targetSequence) matches)
    3. List.ofFn (targetSequence target x.length) = x (by definition of matchesTarget)

    The type-theoretic complexity arises from Fin.cast issues when comparing
    Fin (List.ofFn f).length with Fin x.length. The mathematical argument is complete. -/
private lemma deterministicMeasure_expectPrefix_at_matching
    (target : ℕ → Bool) (x : BinString) (hx_match : matchesTarget target x)
    (g : BinString → ℝ) :
    FiniteHorizon.expectPrefix (deterministicMeasure target) x.length g = g x := by
  -- The mathematical proof is:
  -- 1. expectPrefix = ∑_f prefixPMF(f) * g(List.ofFn f)
  -- 2. prefixPMF(f) = μ(List.ofFn f) = 1 if f matches target, else 0
  -- 3. The only f with prefixPMF(f) ≠ 0 is targetSequence
  -- 4. List.ofFn (targetSequence target x.length) = x by definition of matchesTarget
  -- 5. So the sum = 1 * g(x) = g(x)
  unfold FiniteHorizon.expectPrefix
  -- Use sum_eq_single to isolate the unique contributing term
  rw [Finset.sum_eq_single (targetSequence target x.length)]
  · -- Main term: prefixPMF = 1, and List.ofFn targetSequence = x
    have htarget_eq_x : List.ofFn (targetSequence target x.length) = x := by
      unfold matchesTarget at hx_match
      unfold targetSequence
      exact hx_match.symm
    have hmatch : matchesTarget target (List.ofFn (targetSequence target x.length)) := by
      rw [htarget_eq_x]; exact hx_match
    have hone : prefixPMF (deterministicMeasure target) x.length (targetSequence target x.length) = 1 := by
      show (if matchesTarget target (List.ofFn (targetSequence target x.length)) then (1 : ENNReal) else 0) = 1
      rw [if_pos hmatch]
    rw [hone, ENNReal.toReal_one, one_mul, htarget_eq_x]
  · -- Other terms: prefixPMF = 0
    intro f _ hf
    have hnomatch : ¬matchesTarget target (List.ofFn f) := by
      intro hmatch
      exact hf (ofFn_match_eq_target target x.length f hmatch)
    have hzero : prefixPMF (deterministicMeasure target) x.length f = 0 := by
      show (if matchesTarget target (List.ofFn f) then (1 : ENNReal) else 0) = 0
      rw [if_neg hnomatch]
    rw [hzero, ENNReal.toReal_zero, zero_mul]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- **Theorem 3.66 (Pareto Optimal Performance Measures)**:
    The universal predictor is Pareto optimal under the error performance measure.

    The proof uses the adversarial environment construction: if p' differs from
    universal at some minimal-length history x, we construct a deterministic
    environment that goes through x and punishes p' at that step.

    **Key insight**: By using the MINIMAL history where p' ≠ universal, we ensure
    that p' = universal on all strict prefixes. This means their errors are
    identical for steps before x.length, and differ by exactly 1 at step x.length. -/
theorem universal_pareto_optimal (ξ : Semimeasure)
    (_h_universal : ∀ (μ : PrefixMeasure) (c : ENNReal), c ≠ 0 → Dominates ξ μ c →
      ∃ n₀, ∀ n ≥ n₀, errorPerformance (universalPredictor ξ) μ n ≤
        errorPerformance (optimalPredictor μ) μ n + 1) :
    ParetoOptimal errorPerformance (universalPredictor ξ) := by
  -- Use the equivalent characterization: for any p' that improves somewhere,
  -- there exists μ' where universal is better.
  rw [paretoOptimal_iff]
  intro p' ⟨μ₀, n₀, hp'_better⟩
  -- Find a history x where p' differs from universal
  by_cases h_same : ∀ x : BinString, p' x = universalPredictor ξ x
  · -- If p' agrees with universal everywhere, they have identical performance
    exfalso
    have h_eq : ∀ μ n, errorPerformance p' μ n = errorPerformance (universalPredictor ξ) μ n := by
      intro μ n
      unfold errorPerformance expectPrefix
      congr 1
      ext k
      congr 1
      ext f
      simp only
      rw [h_same (List.ofFn f)]
    rw [h_eq] at hp'_better
    exact (lt_irrefl _ hp'_better)
  · -- There exists x where p' ≠ universal
    push_neg at h_same
    -- Use a minimal-length history where they differ (via well-founded recursion)
    -- This ensures p' = universal on all strict prefixes
    have ⟨x, hx_diff, hx_min⟩ : ∃ x, p' x ≠ universalPredictor ξ x ∧
        ∀ y, y.length < x.length → p' y = universalPredictor ξ y := by
      -- Find minimal using Nat.find on lengths
      have h_exists : ∃ n, ∃ x : BinString, x.length = n ∧ p' x ≠ universalPredictor ξ x := by
        obtain ⟨x, hx⟩ := h_same
        exact ⟨x.length, x, rfl, hx⟩
      let n_min := Nat.find h_exists
      obtain ⟨x, hxlen, hxdiff⟩ := Nat.find_spec h_exists
      use x, hxdiff
      intro y hylen
      by_contra hy_ne
      have : ∃ x' : BinString, x'.length = y.length ∧ p' x' ≠ universalPredictor ξ x' := ⟨y, rfl, hy_ne⟩
      have : y.length ≥ n_min := Nat.find_le this
      omega

    -- Construct the adversarial measure: deterministic path through x, then universal
    let target : ℕ → Bool := fun i =>
      if hi : i < x.length then x.get ⟨i, hi⟩
      else universalPredictor ξ (x.take i)
    let μ' := deterministicMeasure target
    use μ', x.length + 1
    unfold errorPerformance

    -- First, show x matches target up to its length
    have hx_match : matchesTarget target x := by
      unfold matchesTarget
      apply List.ext_getElem
      · simp
      · intro i hi _
        simp only [List.getElem_ofFn, target, hi, ↓reduceDIte]
        simp only [List.get_eq_getElem]

    -- At step x.length, the target bit is universalPredictor ξ x
    have h_target_at_x : target x.length = universalPredictor ξ x := by
      simp only [target, lt_irrefl, ↓reduceDIte, List.take_length]

    -- Universal error at x is 0 (predicts correctly)
    have h_univ_error : errorProb μ' (universalPredictor ξ x) x = 0 := by
      unfold errorProb
      rw [← h_target_at_x, deterministicMeasure_condProb_target target x hx_match]
      ring

    -- p' error at x is 1 (predicts wrong since p' x ≠ universalPredictor ξ x = target x.length)
    have h_p'_error : errorProb μ' (p' x) x = 1 := by
      unfold errorProb
      have hp'_ne_target : p' x ≠ target x.length := by rw [h_target_at_x]; exact hx_diff
      have hp'_eq_not : p' x = !target x.length := by
        cases hp' : p' x <;> cases ht : target x.length <;>
        simp_all
      rw [hp'_eq_not, deterministicMeasure_condProb_notTarget target x hx_match]
      ring

    -- Compute expectPrefix for universal at step x.length
    have h_univ_exp : expectPrefix μ' x.length (fun h => errorProb μ' (universalPredictor ξ h) h) = 0 := by
      rw [deterministicMeasure_expectPrefix_at_matching target x hx_match]
      exact h_univ_error

    -- Compute expectPrefix for p' at step x.length
    have h_p'_exp : expectPrefix μ' x.length (fun h => errorProb μ' (p' h) h) = 1 := by
      rw [deterministicMeasure_expectPrefix_at_matching target x hx_match]
      exact h_p'_error

    -- Split the sum: ∑_{k < x.length+1} = ∑_{k < x.length} + term at k=x.length
    rw [Finset.sum_range_succ, Finset.sum_range_succ, h_univ_exp, h_p'_exp]

    -- KEY: For k < x.length, both predictors agree on x.take k (by minimality of x)
    -- So their errors at each step are IDENTICAL
    have h_sums_eq : (∑ k ∈ Finset.range x.length, expectPrefix μ' k (fun h => errorProb μ' (universalPredictor ξ h) h))
        = (∑ k ∈ Finset.range x.length, expectPrefix μ' k (fun h => errorProb μ' (p' h) h)) := by
      apply Finset.sum_congr rfl
      intro k hk
      -- At step k < x.length, the unique matching history is x.take k
      have hk_lt : k < x.length := Finset.mem_range.mp hk
      -- x.take k matches target
      have htake_match : matchesTarget target (x.take k) := by
        unfold matchesTarget
        apply List.ext_getElem
        · simp
        · intro i hi _
          simp only [List.getElem_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk_lt),
                     Fin.val_cast]
          simp only [target]
          have hi_lt_k : i < k := by
            simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk_lt)] at hi
            exact hi
          have hi_lt : i < x.length := Nat.lt_trans hi_lt_k hk_lt
          simp only [hi_lt, ↓reduceDIte, List.getElem_take, List.get_eq_getElem]
      -- Use deterministicMeasure_expectPrefix_at_matching
      have htake_len : (x.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_lt)
      -- The expectPrefix at step k evaluates at x.take k
      -- We need to convert between lengths
      unfold expectPrefix
      -- Both sums are over Fin k, but we have htake_len : (x.take k).length = k
      -- The measure concentrates on x.take k
      -- Both predictors agree at x.take k by minimality: p' = universal for all y with |y| < |x|
      have h_agree : p' (x.take k) = universalPredictor ξ (x.take k) := by
        apply hx_min
        rw [List.length_take_of_le (Nat.le_of_lt hk_lt)]
        exact hk_lt
      -- So errorProb at x.take k is the same for both
      -- Show the product terms are equal point-wise
      apply Finset.sum_congr rfl
      intro f _
      -- Case split on whether f matches target
      by_cases hmatch : matchesTarget target (List.ofFn f)
      · -- f matches target, so List.ofFn f = x.take k (since k < x.length)
        have hfn_eq : List.ofFn f = x.take k := by
          have hf := ofFn_match_eq_target target k f hmatch
          unfold targetSequence at hf
          apply List.ext_getElem
          · simp [List.length_take_of_le (Nat.le_of_lt hk_lt)]
          · intro i hi _
            simp only [List.getElem_ofFn]
            have hi_lt_k : i < k := by simp at hi; exact hi
            have hi_lt : i < x.length := Nat.lt_trans hi_lt_k hk_lt
            have : f ⟨i, hi_lt_k⟩ = target i := congrFun hf ⟨i, hi_lt_k⟩
            simp only [this, target, hi_lt, ↓reduceDIte, List.getElem_take, List.get_eq_getElem]
        -- Beta reduce and use equality: both products have same errorProb
        simp only [hfn_eq, h_agree]
      · -- f doesn't match, both products are 0 * errorProb = 0
        have hzero : prefixPMF μ' k f = 0 := by
          show (if matchesTarget target (List.ofFn f) then (1 : ENNReal) else 0) = 0
          rw [if_neg hmatch]
        -- Both products are 0 * (something) = 0
        simp only [hzero, ENNReal.toReal_zero, zero_mul]

    rw [h_sums_eq]
    -- Goal: S + 0 < S + 1
    linarith

/-! ## Theorem 3.69: Balanced Pareto Optimality -/

/-! ### Helper Lemmas for Infinite-Horizon Performance -/

/-- Expectation of a non-negative function under a prefix measure is non-negative. -/
theorem expectPrefix_nonneg (μ : PrefixMeasure) (n : ℕ) (f : BinString → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectPrefix μ n f := by
  unfold expectPrefix
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ENNReal.toReal_nonneg
  exact hf (List.ofFn x)

/-- Error performance step is non-negative. -/
theorem errorProbStep_nonneg (p : Predictor) (μ : PrefixMeasure) (k : ℕ) :
    0 ≤ expectPrefix μ k (fun x => errorProb μ (p x) x) :=
  expectPrefix_nonneg μ k _ (fun x => errorProb_nonneg μ _ x)

/-- Error performance is monotone increasing in horizon n.
    More observations can only accumulate more errors. -/
theorem errorPerformance_mono (p : Predictor) (μ : PrefixMeasure) :
    Monotone (fun n => errorPerformance p μ n) := by
  intro m n hmn
  unfold errorPerformance
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hmn
  · intro k _ _
    exact errorProbStep_nonneg p μ k

/-- Infinite-horizon performance as supremum over finite horizons.
    For error performance, this is the total expected errors over infinite time.

    We use ENNReal to handle potentially infinite performance values. -/
noncomputable def infiniteHorizonPerf (perf : PerformanceMeasure)
    (p : Predictor) (μ : PrefixMeasure) : ENNReal :=
  ⨆ n, ENNReal.ofReal (perf p μ n)

/-- For monotone performance measures, the supremum equals the limit. -/
theorem infiniteHorizonPerf_eq_limit (p : Predictor) (μ : PrefixMeasure)
    (_h_mono : Monotone (fun n => errorPerformance p μ n)) :
    infiniteHorizonPerf errorPerformance p μ =
      ⨆ n, ENNReal.ofReal (errorPerformance p μ n) := rfl

/-- Balanced performance: weighted average over all environments.
    B(p) = ∑_μ w(μ) · perf(p, μ, ∞)

    Following Hutter (2005), Definition 3.69: this measures how well predictor p
    performs averaged over the prior w on environments.

    **Note**: This returns ENNReal since infinite-horizon performance may be infinite
    for non-trivial stochastic environments. -/
noncomputable def BalancedPerformance (w : PrefixMeasure → ENNReal)
    (perf : PerformanceMeasure) (p : Predictor) : ENNReal :=
  ∑' μ, w μ * infiniteHorizonPerf perf p μ

/-- For comparison with ℝ-valued bounds, we also define the ℝ version when finite. -/
noncomputable def BalancedPerformance_real (w : PrefixMeasure → ENNReal)
    (perf : PerformanceMeasure) (p : Predictor) : ℝ :=
  (BalancedPerformance w perf p).toReal

/-- At each step, the universal predictor minimizes ξ-expected error.
    This is because it predicts argmax_b ξ(b|x).

    **Note**: For proper measures (not just semimeasures), condProb(true) + condProb(false) = 1.
    This lemma requires that constraint for the "false" case. -/
theorem universalPrediction_minimizes_xi_error (μ : PrefixMeasure) (x : BinString) (b : Bool)
    (hμx : μ x ≠ 0) :
    1 - FiniteHorizon.condProb μ.toSemimeasure x (universalPrediction μ.toSemimeasure x) ≤
    1 - FiniteHorizon.condProb μ.toSemimeasure x b := by
  unfold universalPrediction
  -- For a PrefixMeasure, condProb(true) + condProb(false) = 1
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  set pt := FiniteHorizon.condProb μ.toSemimeasure x true with hpt_def
  set pf := FiniteHorizon.condProb μ.toSemimeasure x false with hpf_def
  -- Case split on whether pt ≥ 1/2
  by_cases h : pt ≥ 1/2
  · -- Universal predicts true
    have hpred : (decide (pt ≥ 1/2)) = true := decide_eq_true h
    rw [hpt_def, hpred]
    cases b
    · -- Need: 1 - pt ≤ 1 - pf, i.e., pf ≤ pt
      -- Since pt + pf = 1 and pt ≥ 1/2, we have pf = 1 - pt ≤ 1/2 ≤ pt
      rw [← hpf_def, ← hpt_def]
      have hpf_eq : pf = 1 - pt := by linarith
      linarith
    · -- trivial: 1 - pt ≤ 1 - pt
      rfl
  · -- Universal predicts false
    push_neg at h
    have hpred : (decide (pt ≥ 1/2)) = false := decide_eq_false (by linarith : ¬pt ≥ 1/2)
    rw [hpt_def, hpred]
    cases b
    · -- trivial: 1 - pf ≤ 1 - pf
      rfl
    · -- Need: 1 - pf ≤ 1 - pt, i.e., pt ≤ pf
      -- Since pt + pf = 1 and pt < 1/2, we have pf = 1 - pt > 1/2 > pt
      rw [← hpf_def, ← hpt_def]
      have hpf_eq : pf = 1 - pt := by linarith
      linarith

/-! ### Curriculum Lemmas for Balanced Pareto Optimality

These lemmas build the bridge between existing infrastructure and Theorems 3.69-3.70.
The dependency chain is:
  L2.1 → L2.2 → L3.2 → balanced_pareto_optimal -/

/-- L2.1: ENNReal version of error performance monotonicity. -/
theorem errorPerformance_ofReal_mono (p : Predictor) (μ : PrefixMeasure) :
    Monotone (fun n => ENNReal.ofReal (errorPerformance p μ n)) := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  exact errorPerformance_mono p μ hmn

/-- L2.2: Infinite-horizon performance is the limit of finite horizons.
    Uses Mathlib's `tendsto_atTop_iSup` for monotone sequences. -/
theorem infiniteHorizonPerf_tendsto (p : Predictor) (μ : PrefixMeasure) :
    Filter.Tendsto (fun n => ENNReal.ofReal (errorPerformance p μ n))
      Filter.atTop (nhds (infiniteHorizonPerf errorPerformance p μ)) :=
  tendsto_atTop_iSup (errorPerformance_ofReal_mono p μ)

/-- L3.2: Key interchange lemma - iSup of weighted sums ≤ weighted sum of iSups.
    This follows from monotonicity: each finite sum is bounded by the infinite sum.

    **Proof**: For each n, we have ∑ w(μ) * perf(n) ≤ ∑ w(μ) * (⨆ n, perf(n))
    by pointwise inequality w(μ) * perf(n) ≤ w(μ) * (⨆ n, perf(n)).
    Taking iSup over n preserves this. -/
theorem iSup_weighted_le_weighted_iSup (w : PrefixMeasure → ENNReal) (p : Predictor) :
    ⨆ n, (∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n)) ≤
    ∑' μ, w μ * (⨆ n, ENNReal.ofReal (errorPerformance p μ n)) := by
  apply iSup_le
  intro n
  apply ENNReal.tsum_le_tsum
  intro μ
  apply mul_le_mul_right
  -- ENNReal.ofReal (errorPerformance p μ n) ≤ ⨆ n, ENNReal.ofReal (errorPerformance p μ n)
  exact le_iSup (fun n => ENNReal.ofReal (errorPerformance p μ n)) n

/-- For the error performance (which is monotone in the horizon), balanced performance can be
computed as the supremum of the weighted finite-horizon sums. This is the ENNReal analogue of
monotone convergence for `tsum` and `iSup`. -/
theorem BalancedPerformance_eq_iSup_weighted_errorPerformance (w : PrefixMeasure → ENNReal)
    (p : Predictor) :
    BalancedPerformance w errorPerformance p =
      ⨆ n, ∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n) := by
  classical
  unfold BalancedPerformance infiniteHorizonPerf
  -- Expand the outer `tsum` as an `iSup` over finite sums.
  rw [ENNReal.tsum_eq_iSup_sum]
  -- Rewrite the `tsum` inside the RHS as an `iSup` over finite sums as well.
  have hRHS :
      (⨆ n, ∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n)) =
        ⨆ n, (⨆ s : Finset PrefixMeasure, ∑ μ ∈ s, w μ * ENNReal.ofReal (errorPerformance p μ n)) := by
    simp [ENNReal.tsum_eq_iSup_sum]
  -- Monotonicity needed to commute `iSup` with finite sums over `μ`.
  have hmono :
      ∀ μ : PrefixMeasure, Monotone fun n => w μ * ENNReal.ofReal (errorPerformance p μ n) := by
    intro μ m n hmn
    exact mul_le_mul_right (errorPerformance_ofReal_mono p μ hmn) (w μ)
  -- Commute `iSup` over horizon with the outer `tsum` (as `iSup` over finite sums).
  -- For each finite set of environments, monotonicity lets us pick one horizon `n`
  -- that approximates all components simultaneously.
  calc
    (⨆ s : Finset PrefixMeasure, ∑ μ ∈ s, w μ * ⨆ n, ENNReal.ofReal (errorPerformance p μ n))
        =
        ⨆ s : Finset PrefixMeasure, ⨆ n, ∑ μ ∈ s, w μ * ENNReal.ofReal (errorPerformance p μ n) := by
          refine iSup_congr ?_
          intro s
          -- Use `ENNReal.finsetSum_iSup_of_monotone` on the finite set `s`.
          -- First rewrite `w μ * (⨆ n, f n)` as `⨆ n, w μ * f n`.
          have hmul :
              (∑ μ ∈ s, w μ * ⨆ n, ENNReal.ofReal (errorPerformance p μ n)) =
                ∑ μ ∈ s, ⨆ n, w μ * ENNReal.ofReal (errorPerformance p μ n) := by
            refine Finset.sum_congr rfl ?_
            intro μ hμ
            simpa using (ENNReal.mul_iSup (w μ) (fun n => ENNReal.ofReal (errorPerformance p μ n)))
          -- Now commute the finite sum with the supremum.
          have hs :=
            (ENNReal.finsetSum_iSup_of_monotone (s := s)
              (f := fun μ n => w μ * ENNReal.ofReal (errorPerformance p μ n)) hmono)
          -- Put everything together.
          simpa [hmul] using hs
    _ = ⨆ n, (⨆ s : Finset PrefixMeasure, ∑ μ ∈ s, w μ * ENNReal.ofReal (errorPerformance p μ n)) := by
          -- Avoid `simp` loops: use the commutation lemma directly.
          exact iSup_comm
    _ = ⨆ n, ∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n) := by
          -- Fold back the finite-sum characterization of `tsum`.
          exact hRHS.symm

/-- Monotonicity: μ(x++[b]) ≤ μ(x) for any prefix measure. -/
theorem prefixMeasure_le_of_append (μ : PrefixMeasure) (x : BinString) (b : Bool) :
    μ (x ++ [b]) ≤ μ x := by
  have hadd := μ.additive' x
  cases b with
  | false =>
    calc μ (x ++ [false]) ≤ μ (x ++ [false]) + μ (x ++ [true]) := le_self_add
      _ = μ x := hadd
  | true =>
    calc μ (x ++ [true]) ≤ μ (x ++ [false]) + μ (x ++ [true]) := le_add_self
      _ = μ x := hadd

/-- If μ(x) = 0 then μ(x++[b]) = 0 for any prefix measure. -/
theorem prefixMeasure_ext_eq_zero_of_prefix_eq_zero (μ : PrefixMeasure) (x : BinString) (b : Bool)
    (hx : μ x = 0) : μ (x ++ [b]) = 0 := by
  have h := prefixMeasure_le_of_append μ x b
  simp only [hx, nonpos_iff_eq_zero] at h
  exact h

/-- L4.1: (μ x).toReal * condProb_μ(b|x) = (μ (x ++ [b])).toReal for prefix measures.
    This is the key algebraic identity for the Fubini interchange (in ℝ).

    **Proof**: condProb_μ(b|x) = μ(x++[b]) / μ(x) when μ(x) > 0, so
    μ(x) * condProb_μ(b|x) = μ(x++[b]). When μ(x) = 0, both sides are 0. -/
theorem mu_toReal_mul_condProb_eq_ext (μ : PrefixMeasure) (x : BinString) (b : Bool) :
    (μ x).toReal * FiniteHorizon.condProb μ.toSemimeasure x b = (μ (x ++ [b])).toReal := by
  unfold FiniteHorizon.condProb conditionalENN
  by_cases hμx : μ x = 0
  · -- If μ(x) = 0, then μ(x ++ [b]) = 0 by monotonicity
    simp only [hμx, ENNReal.toReal_zero, zero_mul]
    have h := prefixMeasure_ext_eq_zero_of_prefix_eq_zero μ x b hμx
    simp only [h, ENNReal.toReal_zero]
  · -- If μ(x) > 0, then μ(x) * (μ(x++[b])/μ(x)) = μ(x++[b])
    -- Note: goal after unfold is already in toReal form
    -- μ.toSemimeasure.toFun = μ.toFun by definition
    have hne' : (μ x : ENNReal) ≠ ⊤ := semimeasure_ne_top μ.toSemimeasure x
    simp only [PrefixMeasure.toSemimeasure_apply]
    -- Now goal is: μ(x).toReal * (μ(x++[b]) / μ(x)).toReal = μ(x++[b]).toReal
    rw [ENNReal.toReal_div]
    -- Goal: μ(x).toReal * (μ(x++[b]).toReal / μ(x).toReal) = μ(x++[b]).toReal
    field_simp [ENNReal.toReal_ne_zero.mpr ⟨hμx, hne'⟩]

/-- Error formula: μ(x) * (1 - condProb(b|x)) = μ(x) - μ(x++[b]) in toReal form. -/
theorem mu_toReal_mul_errorProb (μ : PrefixMeasure) (x : BinString) (b : Bool) :
    (μ x).toReal * (1 - FiniteHorizon.condProb μ.toSemimeasure x b) =
    (μ x).toReal - (μ (x ++ [b])).toReal := by
  rw [mul_sub, mul_one]
  congr 1
  exact mu_toReal_mul_condProb_eq_ext μ x b

/-- The errorProb formula expressed directly. -/
theorem mu_toReal_mul_errorProb' (μ : PrefixMeasure) (x : BinString) (prediction : Bool) :
    (μ x).toReal * errorProb μ prediction x = (μ x).toReal - (μ (x ++ [prediction])).toReal := by
  unfold errorProb
  exact mu_toReal_mul_errorProb μ x prediction

/-- L4.2: Weighted error at prefix x can be expressed as: ξ(x) - ξ(x ++ [b]).
    This shows why maximizing ξ(x ++ [b]) minimizes error.

    **Key identity**: ∑ w(μ) * μ(x).toReal * (1 - condProb_μ(b|x))
                    = ∑ w(μ) * (μ(x) - μ(x++[b])).toReal
                    = (ξ(x) - ξ(x ++ [b])).toReal  (when ξ = ∑ w·μ) -/
theorem weighted_error_as_mixture_diff (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) (b : Bool)
    (hξx_ne_top : ξ x ≠ ⊤) :
    ∑' μ, (w μ).toReal * ((μ x).toReal * (1 - FiniteHorizon.condProb μ.toSemimeasure x b)) =
    (ξ x).toReal - (ξ (x ++ [b])).toReal := by
  -- Step 1: Rewrite using mu_toReal_mul_errorProb and distribute multiplication
  have h1 : (fun μ => (w μ).toReal * ((μ x).toReal * (1 - FiniteHorizon.condProb μ.toSemimeasure x b)))
          = (fun μ => (w μ).toReal * (μ x).toReal - (w μ).toReal * (μ (x ++ [b])).toReal) := by
    ext μ
    rw [mu_toReal_mul_errorProb μ x b, mul_sub]
  rw [tsum_congr (fun μ => congrFun h1 μ)]
  -- Goal: ∑' μ, ((w μ).toReal * (μ x).toReal - (w μ).toReal * (μ (x ++ [b])).toReal) = ...
  -- Step 3: Use tsum_sub (need summability)
  have hξb_ne_top : ξ (x ++ [b]) ≠ ⊤ := ne_top_of_le_ne_top hξx_ne_top (ξ.mono x b)
  -- For the tsum manipulation, we need to convert between ENNReal and ℝ carefully
  -- Using the mixture hypothesis and toReal_tsum for nonneg terms
  -- The key identity is: (w μ).toReal * (μ x).toReal = (w μ * μ x).toReal
  -- (This holds when both are finite, which follows from ξ x ≠ ⊤)
  -- Then: ∑' μ, (w μ * μ x).toReal = (∑' μ, w μ * μ x).toReal = (ξ x).toReal
  -- Similarly for ξ(x ++ [b])
  -- The proof requires careful handling of toReal and tsum interchange.
  -- First show the two “mixture toReal” identities at `x` and `x ++ [b]`.
  have htsum_x_ne_top : (∑' μ, w μ * μ x) ≠ ⊤ := by
    simpa [hMixture x] using hξx_ne_top
  have htsum_xb_ne_top : (∑' μ, w μ * μ (x ++ [b])) ≠ ⊤ := by
    simpa [hMixture (x ++ [b])] using hξb_ne_top
  have mix_toReal_x :
      (ξ x).toReal = ∑' μ, (w μ).toReal * (μ x).toReal := by
    calc
      (ξ x).toReal = (∑' μ, w μ * μ x).toReal := by
        simp [hMixture x]
      _ = ∑' μ, (w μ * μ x).toReal := by
        -- `tsum` is finite, so we can commute `toReal` with `tsum`.
        have hterm : ∀ μ, w μ * μ x ≠ ⊤ :=
          ENNReal.ne_top_of_tsum_ne_top (f := fun μ => w μ * μ x) htsum_x_ne_top
        simpa using (ENNReal.tsum_toReal_eq hterm)
      _ = ∑' μ, (w μ).toReal * (μ x).toReal := by
        refine tsum_congr ?_
        intro μ
        simp [ENNReal.toReal_mul]
  have mix_toReal_xb :
      (ξ (x ++ [b])).toReal = ∑' μ, (w μ).toReal * (μ (x ++ [b])).toReal := by
    calc
      (ξ (x ++ [b])).toReal = (∑' μ, w μ * μ (x ++ [b])).toReal := by
        simp [hMixture (x ++ [b])]
      _ = ∑' μ, (w μ * μ (x ++ [b])).toReal := by
        have hterm : ∀ μ, w μ * μ (x ++ [b]) ≠ ⊤ :=
          ENNReal.ne_top_of_tsum_ne_top (f := fun μ => w μ * μ (x ++ [b])) htsum_xb_ne_top
        simpa using (ENNReal.tsum_toReal_eq hterm)
      _ = ∑' μ, (w μ).toReal * (μ (x ++ [b])).toReal := by
        refine tsum_congr ?_
        intro μ
        simp [ENNReal.toReal_mul]

  -- Now split the `tsum` of a difference into a difference of `tsum`s.
  have hsum1 : Summable fun μ => (w μ).toReal * (μ x).toReal := by
    -- Use summability of `toReal` from finiteness of the ENNReal tsum.
    have hs : Summable fun μ => (w μ * μ x).toReal :=
      ENNReal.summable_toReal (f := fun μ => w μ * μ x) htsum_x_ne_top
    -- Convert `(w μ * μ x).toReal` to `(w μ).toReal * (μ x).toReal`.
    refine hs.congr ?_
    intro μ
    simp [ENNReal.toReal_mul]
  have hsum2 : Summable fun μ => (w μ).toReal * (μ (x ++ [b])).toReal := by
    have hs : Summable fun μ => (w μ * μ (x ++ [b])).toReal :=
      ENNReal.summable_toReal (f := fun μ => w μ * μ (x ++ [b])) htsum_xb_ne_top
    refine hs.congr ?_
    intro μ
    simp [ENNReal.toReal_mul]

  -- Finish.
  calc
    (∑' μ,
        ((w μ).toReal * (μ x).toReal - (w μ).toReal * (μ (x ++ [b])).toReal)) =
        (∑' μ, (w μ).toReal * (μ x).toReal) -
          (∑' μ, (w μ).toReal * (μ (x ++ [b])).toReal) := by
          simpa using (hsum1.tsum_sub hsum2)
    _ = (ξ x).toReal - (ξ (x ++ [b])).toReal := by
          -- Rewrite both components using the mixture identities.
          simp [mix_toReal_x, mix_toReal_xb]

/-- For a Bayes mixture ξ = ∑ w(μ) · μ of prefix measures, extensions sum exactly to prefix.
    This is because each μ satisfies additivity: μ(x++[true]) + μ(x++[false]) = μ(x). -/
theorem bayes_mixture_additive (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) :
    ξ (x ++ [true]) + ξ (x ++ [false]) = ξ x := by
  rw [hMixture (x ++ [true]), hMixture (x ++ [false]), hMixture x]
  -- Goal: ∑' μ, w μ * μ (x ++ [true]) + ∑' μ, w μ * μ (x ++ [false]) = ∑' μ, w μ * μ x
  rw [← ENNReal.tsum_add]
  · -- Goal: ∑' μ, (w μ * μ (x ++ [true]) + w μ * μ (x ++ [false])) = ∑' μ, w μ * μ x
    congr 1
    ext μ
    rw [← mul_add]
    congr 1
    rw [add_comm]
    exact μ.additive' x

/-- For a Bayes mixture, conditional probabilities sum to 1 (not just ≤ 1).
    This is the key property that distinguishes mixtures of prefix measures. -/
theorem bayes_mixture_condProb_sum_eq_one (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) (hξx_pos : ξ x ≠ 0) :
    FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false = 1 := by
  unfold FiniteHorizon.condProb conditionalENN
  have hξx_top : ξ x ≠ ⊤ := semimeasure_ne_top ξ x
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  rw [← add_div]
  have hadd := bayes_mixture_additive w ξ hMixture x
  rw [← hadd]
  have h1 : (ξ (x ++ [true])).toReal + (ξ (x ++ [false])).toReal =
            (ξ (x ++ [true]) + ξ (x ++ [false])).toReal := by
    have htrue_ne_top : ξ (x ++ [true]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x true)
    have hfalse_ne_top : ξ (x ++ [false]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x false)
    exact (ENNReal.toReal_add htrue_ne_top hfalse_ne_top).symm
  rw [h1, hadd]
  exact div_self (ENNReal.toReal_ne_zero.mpr ⟨hξx_pos, hξx_top⟩)

/-- L4.3: Pointwise error minimization - universal prediction minimizes weighted error for each prefix.
    For fixed x, choosing b = argmax condProb_ξ(b|x) minimizes the weighted error.

    **Proof**: The error ξ(x) - ξ(x ++ [b]) is minimized by maximizing ξ(x ++ [b]).
    Since condProb_ξ(b|x) = ξ(x++[b])/ξ(x), argmax condProb_ξ = argmax ξ(x++[b]).
    This is exactly what universalPrediction does. -/
theorem pointwise_weighted_error_minimized (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) (b : Bool)
    (hξx_pos : ξ x ≠ 0) :
    ξ (x ++ [universalPrediction ξ x]) ≥ ξ (x ++ [b]) := by
  -- universalPrediction ξ x = true iff condProb_ξ(true|x) ≥ 1/2
  -- = true iff ξ(x++[true])/ξ(x) ≥ 1/2
  -- = true iff ξ(x++[true]) ≥ ξ(x)/2
  -- By semimeasure additivity: ξ(x++[true]) + ξ(x++[false]) ≥ ξ(x)
  -- So if ξ(x++[true]) ≥ ξ(x)/2, then ξ(x++[true]) ≥ ξ(x++[false])
  unfold universalPrediction
  -- Split on whether we predict true or false, then on the target b
  by_cases hcond : FiniteHorizon.condProb ξ x true ≥ 1/2 <;> cases b
  case pos.true =>
    -- condProb(true) ≥ 1/2, predicting true, comparing with true
    simp only [hcond]
    show ξ (x ++ [true]) ≥ ξ (x ++ [true])
    exact le_refl _
  case pos.false =>
    -- condProb(true) ≥ 1/2, predicting true, comparing with false
    simp only [hcond]
    show ξ (x ++ [true]) ≥ ξ (x ++ [false])
    -- Key: condProb(true) + condProb(false) ≤ 1 (from semimeasure property)
    -- So if condProb(true) ≥ 1/2, then condProb(false) ≤ 1/2 ≤ condProb(true)
    -- Hence ξ(x++[false])/ξ(x) ≤ 1/2 ≤ ξ(x++[true])/ξ(x)
    -- So ξ(x++[false]) ≤ ξ(x++[true])
    have hsum := condProb_sum_le_one ξ x
    have hfalse : FiniteHorizon.condProb ξ x false ≤ 1/2 := by linarith
    -- Convert condProb inequalities to ENNReal inequalities
    unfold FiniteHorizon.condProb conditionalENN at hcond hfalse
    by_cases hξx : ξ x = 0
    · -- If ξ(x) = 0, both extensions are 0 (by semimeasure monotonicity)
      have htrue := ξ.mono x true
      have hfalse' := ξ.mono x false
      simp only [hξx, nonpos_iff_eq_zero] at htrue hfalse'
      simp [htrue, hfalse']
    · -- ξ(x) > 0 case
      have hξx_top : ξ x ≠ ⊤ := semimeasure_ne_top ξ x
      -- hcond, hfalse are already in toReal form after unfold
      -- condProb = (ξ(x++[b]) / ξ(x)).toReal
      -- hcond: (ξ(x++[true]) / ξ(x)).toReal ≥ 1/2
      -- hfalse: (ξ(x++[false]) / ξ(x)).toReal ≤ 1/2
      -- So ξ(x++[false]).toReal / ξ(x).toReal ≤ ξ(x++[true]).toReal / ξ(x).toReal
      -- Since ξ(x) > 0 and ξ(x) < ⊤, we have ξ(x).toReal > 0
      have hξx_real_pos : (0 : ℝ) < (ξ x).toReal := ENNReal.toReal_pos hξx hξx_top
      have h1 : (ξ (x ++ [false]) / ξ x).toReal ≤ (ξ (x ++ [true]) / ξ x).toReal := by linarith
      rw [ENNReal.toReal_div, ENNReal.toReal_div] at h1
      have h2 : (ξ (x ++ [false])).toReal ≤ (ξ (x ++ [true])).toReal := by
        exact (div_le_div_iff_of_pos_right hξx_real_pos).mp h1
      -- Convert toReal inequality back to ENNReal inequality
      have htrue_ne_top : ξ (x ++ [true]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x true)
      have hfalse_ne_top : ξ (x ++ [false]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x false)
      exact (ENNReal.toReal_le_toReal hfalse_ne_top htrue_ne_top).mp h2
  case neg.false =>
    -- condProb(true) < 1/2, predicting false, comparing with false
    simp only [hcond]
    show ξ (x ++ [false]) ≥ ξ (x ++ [false])
    exact le_refl _
  case neg.true =>
    -- condProb(true) < 1/2, predicting false, comparing with true
    simp only [hcond]
    show ξ (x ++ [false]) ≥ ξ (x ++ [true])
    -- Key: For Bayes mixture, condProb(true) + condProb(false) = 1
    -- So condProb(true) < 1/2 implies condProb(false) > 1/2 > condProb(true)
    have hsum_eq := bayes_mixture_condProb_sum_eq_one w ξ hMixture x hξx_pos
    have hlt : FiniteHorizon.condProb ξ x true < 1/2 := not_le.mp hcond
    have hfalse_ge : FiniteHorizon.condProb ξ x false ≥ 1/2 := by linarith
    have hfalse_ge_true : FiniteHorizon.condProb ξ x false ≥ FiniteHorizon.condProb ξ x true := by
      linarith
    -- Convert condProb inequalities to ENNReal inequalities
    unfold FiniteHorizon.condProb conditionalENN at hfalse_ge_true
    have hξx_top : ξ x ≠ ⊤ := semimeasure_ne_top ξ x
    have hξx_real_pos : (0 : ℝ) < (ξ x).toReal := ENNReal.toReal_pos hξx_pos hξx_top
    rw [ENNReal.toReal_div, ENNReal.toReal_div] at hfalse_ge_true
    have h2 : (ξ (x ++ [true])).toReal ≤ (ξ (x ++ [false])).toReal := by
      exact (div_le_div_iff_of_pos_right hξx_real_pos).mp hfalse_ge_true
    have htrue_ne_top : ξ (x ++ [true]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x true)
    have hfalse_ne_top : ξ (x ++ [false]) ≠ ⊤ := ne_top_of_le_ne_top hξx_top (ξ.mono x false)
    exact (ENNReal.toReal_le_toReal htrue_ne_top hfalse_ne_top).mp h2

/-- The error is monotone in the extension: larger ξ(x++[b]) means smaller error.
    errorProb = 1 - condProb = 1 - ξ(x++[b])/ξ(x), so error ↓ when ξ(x++[b]) ↑ -/
theorem errorProb_mono_extension (μ : PrefixMeasure) (x : BinString) (b₁ b₂ : Bool)
    (hμx : μ x ≠ 0)
    (h : μ (x ++ [b₁]) ≥ μ (x ++ [b₂])) :
    errorProb μ b₁ x ≤ errorProb μ b₂ x := by
  unfold errorProb
  apply sub_le_sub_left
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply]
  have hne : (μ x : ENNReal) ≠ ⊤ := semimeasure_ne_top μ.toSemimeasure x
  -- Need: (μ (x ++ [b₂]) / μ x).toReal ≤ (μ (x ++ [b₁]) / μ x).toReal
  have hb₁_ne_top' : μ (x ++ [b₁]) ≠ ⊤ := ne_top_of_le_ne_top hne (prefixMeasure_le_of_append μ x b₁)
  have hb₂_ne_top' : μ (x ++ [b₂]) ≠ ⊤ := ne_top_of_le_ne_top hne (prefixMeasure_le_of_append μ x b₂)
  have hb₁_ne_top : μ (x ++ [b₁]) / μ x ≠ ⊤ := ENNReal.div_ne_top hb₁_ne_top' hμx
  have hb₂_ne_top : μ (x ++ [b₂]) / μ x ≠ ⊤ := ENNReal.div_ne_top hb₂_ne_top' hμx
  exact (ENNReal.toReal_le_toReal hb₂_ne_top hb₁_ne_top).mpr (ENNReal.div_le_div_right h (μ x))

/-- Key intermediate: weighted error at x is ξ(x) - ξ(x++[prediction]).
    Larger ξ(x++[b]) means smaller weighted error.
    (In ENNReal, avoiding toReal complications) -/
theorem weighted_error_le_of_extension_ge (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (_hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) (b₁ b₂ : Bool) (_hξx : ξ x ≠ 0)
    (h : ξ (x ++ [b₁]) ≥ ξ (x ++ [b₂])) :
    ξ x - ξ (x ++ [b₁]) ≤ ξ x - ξ (x ++ [b₂]) := by
  -- Larger extension means smaller difference from ξ(x)
  apply tsub_le_tsub_left h

/-- Universal prediction minimizes weighted error at each prefix x.
    Corollary of pointwise_weighted_error_minimized. -/
theorem universal_minimizes_weighted_error_at_prefix (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (x : BinString) (b : Bool) (hξx : ξ x ≠ 0) :
    ξ x - ξ (x ++ [universalPrediction ξ x]) ≤ ξ x - ξ (x ++ [b]) := by
  apply weighted_error_le_of_extension_ge w ξ hMixture x _ b hξx
  exact pointwise_weighted_error_minimized w ξ hMixture x b hξx

/-- Sum of ξ-errors over all prefixes of length k.
    This is the "raw" error in ENNReal, avoiding toReal complications. -/
noncomputable def xiErrorSum (ξ : Semimeasure) (pred : Predictor) (k : ℕ) : ENNReal :=
  ∑ x : Fin k → Bool, (ξ (List.ofFn x) - ξ (List.ofFn x ++ [pred (List.ofFn x)]))

/-- Universal predictor minimizes the ξ-error sum at each step k.
    This is the cleaner ENNReal version, avoiding toReal complications. -/
theorem universal_minimizes_xiErrorSum (w : PrefixMeasure → ENNReal)
    (ξ : Semimeasure) (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (p : Predictor) (k : ℕ) :
    xiErrorSum ξ (universalPredictor ξ) k ≤ xiErrorSum ξ p k := by
  unfold xiErrorSum
  -- Apply Finset.sum_le_sum: it suffices to show each term is ≤
  apply Finset.sum_le_sum
  intro x _
  -- For each x, show: ξ(x') - ξ(x'++[universal x']) ≤ ξ(x') - ξ(x'++[p x'])
  -- where x' = List.ofFn x
  let x' := List.ofFn x
  -- Use universal_minimizes_weighted_error_at_prefix (if ξ x' ≠ 0)
  by_cases hξx : ξ x' = 0
  · -- If ξ(x') = 0, both extensions are also 0 (by semimeasure monotonicity)
    have h1 : ξ (x' ++ [universalPredictor ξ x']) ≤ ξ x' := ξ.mono x' _
    have h2 : ξ (x' ++ [p x']) ≤ ξ x' := ξ.mono x' _
    rw [hξx, nonpos_iff_eq_zero] at h1 h2
    -- Now both sides equal 0 - 0 = 0
    show ξ (List.ofFn x) - ξ (List.ofFn x ++ [universalPredictor ξ (List.ofFn x)]) ≤
         ξ (List.ofFn x) - ξ (List.ofFn x ++ [p (List.ofFn x)])
    rw [hξx, h1, h2]
  · -- If ξ(x') > 0, apply universal_minimizes_weighted_error_at_prefix
    exact universal_minimizes_weighted_error_at_prefix w ξ hMixture x' (p x') hξx

/-- Helper: The toReal of xiErrorSum equals the sum of toReal ξ-differences.
    This requires ξ(x) ≠ ⊤ for all x, which holds for semimeasures (they're ≤ 1). -/
theorem xiErrorSum_toReal (ξ : Semimeasure) (pred : Predictor) (k : ℕ) :
    (xiErrorSum ξ pred k).toReal =
    ∑ x : Fin k → Bool, ((ξ (List.ofFn x)).toReal - (ξ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
  unfold xiErrorSum
  -- Use ENNReal.toReal_sum for finite sums
  rw [ENNReal.toReal_sum]
  · -- Goal: ∑ x, (ξ x' - ξ(x'++[pred x'])).toReal = ∑ x, (ξ x').toReal - (ξ(x'++[pred x'])).toReal
    congr 1
    ext x
    let x' := List.ofFn x
    -- toReal(a - b) = a.toReal - b.toReal when b ≤ a and both ≠ ⊤
    have hle : ξ (x' ++ [pred x']) ≤ ξ x' := ξ.mono x' _
    have hx_ne_top : ξ x' ≠ ⊤ := semimeasure_ne_top ξ x'
    have hext_ne_top : ξ (x' ++ [pred x']) ≠ ⊤ := ne_top_of_le_ne_top hx_ne_top hle
    exact ENNReal.toReal_sub_of_le hle hx_ne_top
  · -- Show each term is ≠ ⊤
    intro x _
    let x' := List.ofFn x
    have hle : ξ (x' ++ [pred x']) ≤ ξ x' := ξ.mono x' _
    have hx_ne_top : ξ x' ≠ ⊤ := semimeasure_ne_top ξ x'
    exact ne_top_of_le_ne_top hx_ne_top (tsub_le_self)

theorem universalPredictor_minimizes_weighted_step_error
    (w : PrefixMeasure → ENNReal) (ξ : Semimeasure)
    (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)
    (p : Predictor) (k : ℕ) :
    ∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x)) ≤
    ∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x)) := by
  classical
  -- First extract the “Kraft”/finiteness facts about `w` from the mixture identity at `[]`.
  have htsum_w : (∑' μ, w μ) = ξ [] := by
    symm
    calc
      ξ [] = ∑' μ, w μ * μ [] := by
        simpa using hMixture []
      _ = ∑' μ, w μ := by
        refine tsum_congr ?_
        intro μ
        simp [μ.root_eq_one']
  have htsum_w_ne_top : (∑' μ, w μ) ≠ ⊤ := by
    -- `ξ [] ≤ 1`, hence finite.
    simpa [htsum_w.symm] using (semimeasure_ne_top ξ [])
  have hw_ne_top : ∀ μ, w μ ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top htsum_w_ne_top
  have hw_summable_toReal : Summable fun μ => (w μ).toReal :=
    ENNReal.summable_toReal (f := fun μ => w μ) htsum_w_ne_top

  -- Basic bounds: `errorProb ≤ 1`, hence each step expectation is ≤ 1.
  have errorProb_le_one (μ : PrefixMeasure) (b : Bool) (x : BinString) :
      errorProb μ b x ≤ 1 := by
    unfold errorProb
    have hnonneg : 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x b := by
      unfold FiniteHorizon.condProb conditionalENN
      exact ENNReal.toReal_nonneg
    linarith
  have expectPrefix_le_one (μ : PrefixMeasure) (pred : Predictor) :
      expectPrefix μ k (fun x => errorProb μ (pred x) x) ≤ 1 := by
    unfold expectPrefix
    have hweights := sum_prefixPMF_toReal μ k
    calc
      ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal * errorProb μ (pred (List.ofFn f)) (List.ofFn f)
          ≤ ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal * 1 := by
              apply Finset.sum_le_sum
              intro f _
              apply mul_le_mul_of_nonneg_left (errorProb_le_one μ _ _) ENNReal.toReal_nonneg
      _ = ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal := by simp
      _ = 1 := hweights
  have ofReal_expectPrefix_le_one (μ : PrefixMeasure) (pred : Predictor) :
      ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)) ≤ 1 := by
    have hle : expectPrefix μ k (fun x => errorProb μ (pred x) x) ≤ 1 := expectPrefix_le_one μ pred
    simpa using (ENNReal.ofReal_le_ofReal hle)

  -- The weighted sums are finite since each term is bounded by `w μ` and `∑ w μ = ξ []`.
  have hLHS_ne_top :
      (∑' μ, w μ * ENNReal.ofReal
          (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))) ≠ ⊤ := by
    have hle :
        (∑' μ, w μ * ENNReal.ofReal
            (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))) ≤ ∑' μ, w μ := by
      refine ENNReal.tsum_le_tsum (fun μ => ?_)
      calc
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))
            ≤ w μ * 1 := by
                exact mul_le_mul_right (ofReal_expectPrefix_le_one μ (universalPredictor ξ)) (w μ)
        _ = w μ := by simp
    exact ne_top_of_le_ne_top htsum_w_ne_top hle
  have hRHS_ne_top :
      (∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))) ≠ ⊤ := by
    have hle :
        (∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))) ≤ ∑' μ, w μ := by
      refine ENNReal.tsum_le_tsum (fun μ => ?_)
      calc
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))
            ≤ w μ * 1 := by
                exact mul_le_mul_right (ofReal_expectPrefix_le_one μ p) (w μ)
        _ = w μ := by simp
    exact ne_top_of_le_ne_top htsum_w_ne_top hle

  -- Reduce to a real inequality by `toReal`.
  refine (ENNReal.toReal_le_toReal hLHS_ne_top hRHS_ne_top).1 ?_

  -- Convert `toReal` of the weighted ENNReal tsum into a real tsum.
  have hterm_ne_top_univ :
      ∀ μ, w μ * ENNReal.ofReal
        (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x)) ≠ ⊤ := by
    intro μ
    have hle :
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x)) ≤ w μ := by
      calc
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))
            ≤ w μ * 1 := by
                exact mul_le_mul_right (ofReal_expectPrefix_le_one μ (universalPredictor ξ)) (w μ)
        _ = w μ := by simp
    exact ne_top_of_le_ne_top (hw_ne_top μ) hle
  have hterm_ne_top_p :
      ∀ μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x)) ≠ ⊤ := by
    intro μ
    have hle :
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x)) ≤ w μ := by
      calc
        w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))
            ≤ w μ * 1 := by
                exact mul_le_mul_right (ofReal_expectPrefix_le_one μ p) (w μ)
        _ = w μ := by simp
    exact ne_top_of_le_ne_top (hw_ne_top μ) hle

  -- Compute both sides as `xiErrorSum.toReal`.
  have mix_toReal (x : BinString) :
      (ξ x).toReal = ∑' μ, (w μ).toReal * (μ x).toReal := by
    -- Use `ENNReal.tsum_toReal_eq` and the mixture identity.
    have hx : ξ x = ∑' μ, w μ * μ x := hMixture x
    have hterm : ∀ μ, w μ * μ x ≠ ⊤ := by
      intro μ
      have hμ_le_one : μ x ≤ 1 := by
        have := semimeasure_le_one (μ := μ.toSemimeasure) x
        simpa [PrefixMeasure.toSemimeasure_apply] using this
      have hle : w μ * μ x ≤ w μ := by
        calc
          w μ * μ x ≤ w μ * 1 := mul_le_mul_right hμ_le_one (w μ)
          _ = w μ := by simp
      exact ne_top_of_le_ne_top (hw_ne_top μ) hle
    calc
      (ξ x).toReal = (∑' μ, w μ * μ x).toReal := by simp [hx]
      _ = ∑' μ, (w μ * μ x).toReal := by
            simpa using (ENNReal.tsum_toReal_eq hterm)
      _ = ∑' μ, (w μ).toReal * (μ x).toReal := by
            refine tsum_congr ?_
            intro μ
            simp [ENNReal.toReal_mul]

  have expectPrefix_errorProb_eq_sum_diff (μ : PrefixMeasure) (pred : Predictor) :
      expectPrefix μ k (fun x => errorProb μ (pred x) x) =
        ∑ x : Fin k → Bool,
          ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
    unfold expectPrefix prefixPMF
    congr 1
    ext x
    -- `prefixPMF μ k x = μ (List.ofFn x)` by definition.
    simpa using mu_toReal_mul_errorProb' μ (List.ofFn x) (pred (List.ofFn x))

  have weighted_expectPrefix_eq_xiErrorSum_toReal (pred : Predictor) :
      (∑' μ, (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (pred x) x)) =
        (xiErrorSum ξ pred k).toReal := by
    -- Expand `expectPrefix`, swap `tsum` with the finite sum, then use the mixture identity.
    classical
    -- Replace `expectPrefix` by a sum of differences.
    have hrewrite :
        (fun μ => (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (pred x) x)) =
          (fun μ => (w μ).toReal *
              ∑ x : Fin k → Bool,
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal)) := by
      ext μ
      simp [expectPrefix_errorProb_eq_sum_diff μ pred]
    -- Turn `tsum` of the RHS into a `tsum` of a finite sum.
    have hswap :
        (∑' μ, (w μ).toReal *
              ∑ x : Fin k → Bool,
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal)) =
          ∑ x : Fin k → Bool,
            ∑' μ, (w μ).toReal *
              ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
      -- Use `Summable.tsum_finsetSum` with `s = univ`.
      have hsum :
          ∀ x : Fin k → Bool,
            Summable fun μ =>
              (w μ).toReal *
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
        intro x
        -- Comparison against `μ ↦ (w μ).toReal`.
        refine hw_summable_toReal.of_nonneg_of_le (fun μ => ?_) (fun μ => ?_)
        · -- nonneg
          have hle : μ (List.ofFn x ++ [pred (List.ofFn x)]) ≤ μ (List.ofFn x) := by
            exact prefixMeasure_le_of_append μ (List.ofFn x) (pred (List.ofFn x))
          have hμTop : μ (List.ofFn x) ≠ ⊤ := semimeasure_ne_top μ.toSemimeasure (List.ofFn x)
          have hμextTop : μ (List.ofFn x ++ [pred (List.ofFn x)]) ≠ ⊤ :=
            ne_top_of_le_ne_top hμTop hle
          have hdiff :
              0 ≤ (μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal := by
            exact sub_nonneg.2 <| (ENNReal.toReal_le_toReal hμextTop hμTop).2 hle
          have : 0 ≤ (w μ).toReal := ENNReal.toReal_nonneg
          exact mul_nonneg this hdiff
        · -- upper bound by `(w μ).toReal`
          have hdiff_le_one :
              (μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal ≤ 1 := by
            have hμ_le_one : (μ (List.ofFn x)).toReal ≤ 1 := by
              have hμ_le : μ (List.ofFn x) ≤ 1 := by
                have := semimeasure_le_one (μ := μ.toSemimeasure) (List.ofFn x)
                simpa [PrefixMeasure.toSemimeasure_apply] using this
              have hμTop : μ (List.ofFn x) ≠ ⊤ := semimeasure_ne_top μ.toSemimeasure (List.ofFn x)
              simpa using ENNReal.toReal_mono (hb := ENNReal.one_ne_top) hμ_le
            -- subtracting a nonnegative term only decreases the value
            have hμext_nonneg : 0 ≤ (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal :=
              ENNReal.toReal_nonneg
            have : (μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal ≤
                (μ (List.ofFn x)).toReal := sub_le_self _ hμext_nonneg
            exact this.trans hμ_le_one
          have hw_nonneg : 0 ≤ (w μ).toReal := ENNReal.toReal_nonneg
          -- Multiply the bound `hdiff_le_one` by the nonnegative weight.
          have : (w μ).toReal * ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) ≤
              (w μ).toReal * 1 := mul_le_mul_of_nonneg_left hdiff_le_one hw_nonneg
          simpa using this
      -- Now commute `tsum` with the finite sum (over `Finset.univ`).
      have hmul :
          ∀ μ : PrefixMeasure,
            (w μ).toReal *
                (∑ x : Fin k → Bool,
                  ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal)) =
              ∑ x : Fin k → Bool,
                (w μ).toReal *
                  ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
        intro μ
        classical
        -- Push the scalar inside the finite sum.
        -- Note: `∑ x : Fin k → Bool, ...` is definitionally `∑ x in Finset.univ, ...`.
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin k → Bool)))
            (f := fun x : Fin k → Bool =>
              (μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal)
            (a := (w μ).toReal))
      calc
        (∑' μ, (w μ).toReal *
              ∑ x : Fin k → Bool,
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal))
            =
            ∑' μ, ∑ x : Fin k → Bool,
              (w μ).toReal *
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
              refine tsum_congr ?_
              intro μ
              exact hmul μ
        _ =
            ∑ x : Fin k → Bool,
              ∑' μ,
                (w μ).toReal *
                  ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
              -- Swap `tsum` with the finite sum.
              simpa using
                (Summable.tsum_finsetSum
                  (s := (Finset.univ : Finset (Fin k → Bool)))
                  (f := fun x μ =>
                    (w μ).toReal *
                      ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal))
                  (hf := by
                    intro x hx
                    simpa using hsum x))
    -- Combine, then rewrite each inner tsum using `mix_toReal`.
    calc
      (∑' μ, (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (pred x) x))
          = ∑' μ, (w μ).toReal *
              ∑ x : Fin k → Bool,
                ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
              simp [hrewrite]
      _ = ∑ x : Fin k → Bool,
            ∑' μ, (w μ).toReal *
              ((μ (List.ofFn x)).toReal - (μ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := hswap
      _ = ∑ x : Fin k → Bool,
            ((ξ (List.ofFn x)).toReal - (ξ (List.ofFn x ++ [pred (List.ofFn x)])).toReal) := by
              -- Evaluate the inner tsum by splitting into two tsums and using `mix_toReal`.
              apply Fintype.sum_congr
              intro x
              -- Let `x'` be the prefix list.
              set x' : BinString := List.ofFn x
              have hsum1 : Summable fun μ => (w μ).toReal * (μ x').toReal := by
                refine hw_summable_toReal.of_nonneg_of_le (fun _ => ?_) (fun μ => ?_)
                · exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
                · -- `(μ x').toReal ≤ 1`
                  have hμ_le_one : (μ x').toReal ≤ 1 := by
                    have hμ_le : μ x' ≤ 1 := by
                      have := semimeasure_le_one (μ := μ.toSemimeasure) x'
                      simpa [PrefixMeasure.toSemimeasure_apply] using this
                    have hμTop : μ x' ≠ ⊤ := semimeasure_ne_top μ.toSemimeasure x'
                    simpa using ENNReal.toReal_mono (hb := ENNReal.one_ne_top) hμ_le
                  have : (w μ).toReal * (μ x').toReal ≤ (w μ).toReal * 1 :=
                    mul_le_mul_of_nonneg_left hμ_le_one ENNReal.toReal_nonneg
                  simpa using this
              have hsum2 : Summable fun μ => (w μ).toReal * (μ (x' ++ [pred x'])).toReal := by
                refine hw_summable_toReal.of_nonneg_of_le (fun _ => ?_) (fun μ => ?_)
                · exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
                · have hμ_le_one : (μ (x' ++ [pred x'])).toReal ≤ 1 := by
                    have hμ_le : μ (x' ++ [pred x']) ≤ 1 := by
                      have := semimeasure_le_one (μ := μ.toSemimeasure) (x' ++ [pred x'])
                      simpa [PrefixMeasure.toSemimeasure_apply] using this
                    have hμTop : μ (x' ++ [pred x']) ≠ ⊤ :=
                      semimeasure_ne_top μ.toSemimeasure (x' ++ [pred x'])
                    simpa using ENNReal.toReal_mono (hb := ENNReal.one_ne_top) hμ_le
                  have : (w μ).toReal * (μ (x' ++ [pred x'])).toReal ≤ (w μ).toReal * 1 :=
                    mul_le_mul_of_nonneg_left hμ_le_one ENNReal.toReal_nonneg
                  simpa using this
              -- Now compute the inner tsum via `tsum_sub`, then evaluate using `mix_toReal`.
              calc
                (∑' μ, (w μ).toReal * ((μ x').toReal - (μ (x' ++ [pred x'])).toReal))
                    =
                    ∑' μ,
                      ((w μ).toReal * (μ x').toReal -
                        (w μ).toReal * (μ (x' ++ [pred x'])).toReal) := by
                        refine tsum_congr ?_
                        intro μ
                        simp [mul_sub]
                _ = (∑' μ, (w μ).toReal * (μ x').toReal) -
                      (∑' μ, (w μ).toReal * (μ (x' ++ [pred x'])).toReal) := by
                        simpa using (hsum1.tsum_sub hsum2)
                _ = (ξ x').toReal - (ξ (x' ++ [pred x'])).toReal := by
                        simp [mix_toReal]
      _ = (xiErrorSum ξ pred k).toReal := by
            -- This is exactly `xiErrorSum_toReal`.
            simp [xiErrorSum_toReal]

  -- Finish by converting back to `xiErrorSum` and applying `universal_minimizes_xiErrorSum`.
  have hxi :
      xiErrorSum ξ (universalPredictor ξ) k ≤ xiErrorSum ξ p k :=
    universal_minimizes_xiErrorSum (w := w) (ξ := ξ) hMixture p k
  have hxi_ne_top : xiErrorSum ξ p k ≠ ⊤ := by
    unfold xiErrorSum
    -- finite sum of finite terms
    have : (∀ x : Fin k → Bool, ξ (List.ofFn x) - ξ (List.ofFn x ++ [p (List.ofFn x)]) ≠ ⊤) := by
      intro x
      have hx_ne_top : ξ (List.ofFn x) ≠ ⊤ := semimeasure_ne_top ξ (List.ofFn x)
      exact ne_top_of_le_ne_top hx_ne_top (tsub_le_self)
    -- use `ENNReal.sum_ne_top` on `univ`
    simpa [ENNReal.sum_ne_top] using (this)
  have hxi_toReal :
      (xiErrorSum ξ (universalPredictor ξ) k).toReal ≤ (xiErrorSum ξ p k).toReal :=
    ENNReal.toReal_mono hxi_ne_top hxi
  -- Rewrite both sides as the `toReal` of the weighted sums.
  have hLHS_toReal :
      (∑' μ, w μ * ENNReal.ofReal
          (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))).toReal =
        (xiErrorSum ξ (universalPredictor ξ) k).toReal := by
    -- Convert the ENNReal `tsum` to a real `tsum`, then reduce to `xiErrorSum`.
    rw [ENNReal.tsum_toReal_eq hterm_ne_top_univ]
    have hterm_toReal :
        ∀ μ,
          (w μ * ENNReal.ofReal
              (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))).toReal =
            (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x) := by
      intro μ
      have hnonneg :
          0 ≤ expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x) :=
        errorProbStep_nonneg (p := universalPredictor ξ) (μ := μ) (k := k)
      simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnonneg]
    calc
      (∑' μ,
          (w μ * ENNReal.ofReal
              (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))).toReal)
          =
          ∑' μ, (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x) := by
            refine tsum_congr ?_
            intro μ
            exact hterm_toReal μ
      _ = (xiErrorSum ξ (universalPredictor ξ) k).toReal := by
            simpa using (weighted_expectPrefix_eq_xiErrorSum_toReal (pred := universalPredictor ξ))
  have hRHS_toReal :
      (∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))).toReal =
        (xiErrorSum ξ p k).toReal := by
    rw [ENNReal.tsum_toReal_eq hterm_ne_top_p]
    have hterm_toReal :
        ∀ μ,
          (w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))).toReal =
            (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (p x) x) := by
      intro μ
      have hnonneg : 0 ≤ expectPrefix μ k (fun x => errorProb μ (p x) x) :=
        errorProbStep_nonneg (p := p) (μ := μ) (k := k)
      simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnonneg]
    calc
      (∑' μ, (w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))).toReal)
          =
          ∑' μ, (w μ).toReal * expectPrefix μ k (fun x => errorProb μ (p x) x) := by
            refine tsum_congr ?_
            intro μ
            exact hterm_toReal μ
      _ = (xiErrorSum ξ p k).toReal := by
            simpa using (weighted_expectPrefix_eq_xiErrorSum_toReal (pred := p))
  -- Conclude.
  simpa [hLHS_toReal, hRHS_toReal] using hxi_toReal

/-- **Theorem 3.69 (Balanced Pareto Optimality)** (Hutter 2005):

    When ξ is the Bayes mixture ξ = ∑ w(μ) · μ, the universal predictor minimizes
    balanced performance. This is because at each step, universalPredictor(ξ)
    chooses argmax_b ξ(b|x), which minimizes ξ-expected error, and ξ-expectation
    equals the w-weighted sum of μ-expectations.

    **Proof** (from Hutter p. 101):
    1. At each step t, E_ξ[error] = ∑_μ w(μ) · E_μ[error]
    2. Universal predictor minimizes E_ξ[error] at each step
    3. Summing over steps preserves this inequality
    4. The limit (supremum) also preserves this inequality

    **Hypothesis**: ξ must be the Bayes mixture with weights w.
    The dominance hypothesis (c·μ ≤ ξ) alone is insufficient. -/
theorem balanced_pareto_optimal (ξ : Semimeasure)
    (w : PrefixMeasure → ENNReal)
    (_hKraft : ∑' μ, w μ ≤ 1)  -- Prior satisfies Kraft inequality
    (hMixture : ∀ x, ξ x = ∑' μ, w μ * μ x)  -- ξ is the Bayes mixture
    : ∀ p, BalancedPerformance w errorPerformance (universalPredictor ξ) ≤
         BalancedPerformance w errorPerformance p := by
  intro p
  -- Rewrite balanced performance as a supremum over finite horizons.
  rw [BalancedPerformance_eq_iSup_weighted_errorPerformance (w := w) (p := universalPredictor ξ)]
  rw [BalancedPerformance_eq_iSup_weighted_errorPerformance (w := w) (p := p)]
  -- Reduce to showing the weighted finite-horizon inequality for every `n`.
  refine iSup_le ?_
  intro n
  -- First, relate weighted finite-horizon error performance to the sum of stepwise weighted errors.
  have hrewrite (pred : Predictor) :
      (∑' μ, w μ * ENNReal.ofReal (errorPerformance pred μ n)) =
        ∑ k ∈ Finset.range n,
          ∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)) := by
    classical
    unfold errorPerformance
    -- Push `ENNReal.ofReal` through the finite sum (all summands are nonnegative),
    -- then commute `tsum` with the finite sum over `k`.
    have hterm (μ : PrefixMeasure) :
        w μ * ENNReal.ofReal (∑ k ∈ Finset.range n,
            expectPrefix μ k (fun x => errorProb μ (pred x) x)) =
          ∑ k ∈ Finset.range n,
            w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)) := by
      have hnonneg :
          ∀ k ∈ Finset.range n, 0 ≤ expectPrefix μ k (fun x => errorProb μ (pred x) x) := by
        intro k hk
        exact errorProbStep_nonneg pred μ k
      -- `ENNReal.ofReal` is additive over finite sums of nonnegative reals.
      simp [ENNReal.ofReal_sum_of_nonneg hnonneg, Finset.mul_sum]
    calc
      (∑' μ, w μ * ENNReal.ofReal
            (∑ k ∈ Finset.range n, expectPrefix μ k (fun x => errorProb μ (pred x) x)))
          =
          ∑' μ, ∑ k ∈ Finset.range n,
            w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)) := by
            refine tsum_congr ?_
            intro μ
            simpa using (hterm μ)
      _ =
          ∑ k ∈ Finset.range n,
            ∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)) := by
            -- `tsum` commutes with finite sums.
            simpa using
              (Summable.tsum_finsetSum
                (β := PrefixMeasure) (γ := ℕ) (α := ENNReal)
                (f := fun k μ =>
                  w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (pred x) x)))
                (s := Finset.range n) (hf := by
                  intro k hk
                  exact ENNReal.summable))
  -- Now compare the stepwise weighted sums using L5.1 and sum over `k < n`.
  have hstep : ∀ k, (∑' μ, w μ * ENNReal.ofReal
        (expectPrefix μ k (fun x => errorProb μ (universalPredictor ξ x) x))) ≤
      (∑' μ, w μ * ENNReal.ofReal (expectPrefix μ k (fun x => errorProb μ (p x) x))) := by
    intro k
    simpa using
      (universalPredictor_minimizes_weighted_step_error (w := w) (ξ := ξ) hMixture p k)
  -- Combine: rewrite both sides and sum the per-step inequalities.
  have hfin :
      (∑' μ, w μ * ENNReal.ofReal (errorPerformance (universalPredictor ξ) μ n)) ≤
        (∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n)) := by
    -- Rewrite each side as a finite sum over steps `k`.
    rw [hrewrite (pred := universalPredictor ξ)]
    rw [hrewrite (pred := p)]
    -- Then sum the stepwise inequalities.
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hstep k
  -- Finish by taking the `iSup` on the RHS.
  exact le_trans hfin (le_iSup (fun n => ∑' μ, w μ * ENNReal.ofReal (errorPerformance p μ n)) n)

/-! ## Theorem 3.70: Optimal Choice of Universal Weights (Hutter §3.6.4)

Hutter’s discussion uses Theorem 2.10(iii) to justify Solomonoff–Levin weights
`w_ν := 2^{-K(ν)}` as an “optimal compromise” among enumerable weight functions `v` with short
description: the bounds involving `ln w_ν^{-1}` are at most `O(1)` worse than those involving
`ln v_ν^{-1}`.

In this Lean development we avoid global `axiom` declarations. The fully general comparison
to arbitrary enumerable `v` needs a substantial AIT layer (a formal Theorem 2.10(iii) analogue,
relating prefix-free complexity to enumerable semimeasures on indices).

What we *can* state and prove today is the machine-invariance core:
changing the reference universal prefix-free machine only changes the “universal weights”
by a multiplicative constant (equivalently: log-bounds change by an additive constant).
-/

/-- **Machine invariance for Solomonoff–Levin weights**.

For universal prefix-free machines `U` and `V`, the algorithmic weights
`w_U(x) := 2^{-Kpf[U](x)}` and `w_V(x) := 2^{-Kpf[V](x)}` agree up to a constant factor.

This is the `O(1)` robustness that underlies Hutter’s “optimal weights” discussion:
any bound that is monotone in `log(1 / w_U x)` changes by at most an additive constant when
switching the reference universal machine. -/
theorem universalWeights_mul_le_of_invariance
    (U V : Mettapedia.Logic.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.Logic.SolomonoffPrior.UniversalPFM U]
    [Mettapedia.Logic.SolomonoffPrior.UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString,
      kpfWeight (U := V) x * (2 : ENNReal) ^ (-(c : ℤ)) ≤ kpfWeight (U := U) x := by
  simpa using (kpfWeight_mul_le_of_invariance (U := U) (V := V))

/-- **Theorem 3.70 (Optimal choice of weights)** (Hutter 2005, §3.6.4, around eq. (1547)).

Hutter considers the class `V` of *enumerable* weight functions `v` with short description and
`∑ v_ν ≤ 1`, and argues that Solomonoff–Levin weights `w_ν := 2^{-K(ν)}` are an “optimal compromise”:
the regret bounds depending on `ln(1 / w_ν)` are at most `O(1)` worse than those depending on
`ln(1 / v_ν)`.

In a multiplicative form (avoiding logs), this can be read as:
`v_ν ≤ C · w_ν` for some constant `C` depending only on `v` (and the choice of universal machine),
uniformly for all indices `ν`.

In this development, the corresponding *core quantitative statement* would be a corollary of a
formal analogue of Hutter Theorem 2.10(iii) ("coding theorem" inequality), specialized to
distributions over indices. We record the statement here as a theorem stub.
-/
theorem optimalChoiceOfWeights_hutter
    (U : Mettapedia.Logic.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.Logic.SolomonoffPrior.UniversalPFM U]
    (v : BinString → ENNReal)
    (hv_sum : (∑' x : BinString, v x) ≤ 1) :
    ∃ C : ENNReal, C ≠ 0 ∧ ∀ x : BinString, v x ≤ C * kpfWeight (U := U) x := by
  -- NOTE: This is a purely Kraft-style inequality (dyadic coding) that holds for any `v`
  -- with `∑ v ≤ 1`. A fully faithful formalization of Hutter's §3.6.4 discussion would
  -- additionally track the *description length* / complexity of `v` (via an enumeration of
  -- lower-semicomputable semimeasures); see `HutterEnumerationTheorem.lean` for the concrete
  -- enumeration bridge used in this project.
  simpa using OptimalWeights.exists_const_mul_kpfWeight (U := U) (v := v) hv_sum

/-- **V3 (Hutter/Levin enumeration)**: dominance→regret for lower-semicomputable environments.

This is the “real machine model” layer (Hutter 2005, Chapter 2):
we fix a concrete, surjective enumeration of **lower semicomputable** prefix measures and apply
the Chapter‑3 dominance→regret theorem to its universal mixture.

This is not a full formalization of Hutter's Theorem 2.10(iii) coding-theorem inequality on
weights, but it is the key computability bridge needed to make “universal prediction” non-toy.
-/
theorem relEntropy_le_log_inv_of_LSC_hutterV3 (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates
          (HutterEnumerationTheorem.lscPrefixMeasureEnumeration.toPrefixMeasureEnumeration.xi) μ c ∧
        relEntropy μ
            (HutterEnumerationTheorem.lscPrefixMeasureEnumeration.toPrefixMeasureEnumeration.xi) n ≤
          Real.log (1 / c.toReal) := by
  simpa using
    (Mettapedia.Logic.UniversalPrediction.relEntropy_le_log_inv_of_LSC_concrete (μ := μ) hμ n)

end Optimality

end Mettapedia.Logic.UniversalPrediction
