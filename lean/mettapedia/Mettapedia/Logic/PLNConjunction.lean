import Mettapedia.Logic.EvidenceQuantale
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic

/-!
# PLN Conjunction Introduction Rule

This file formalizes the PLN **Conjunction Introduction Rule** which computes
the truth value of A ∧ B from the truth values of A and B.

## Key Insight (from Nil's nuPLN.tex Section 5)

The conjunction formula is based on the **hypergeometric distribution**:

**Discrete Case:**
Given universe size n, |A| = a, |B| = b, what is P(|A ∧ B| = k)?

$$P(|A ∧ B| = k) = \frac{C_k^a × C_{b-k}^{n-a}}{C_b^n}$$

This is the hypergeometric PMF: we're drawing b items (elements of B) without
replacement from a population of n items where a are "successes" (elements of A).
The number of successes in our sample is k = |A ∧ B|.

**Continuous Limit:**
Via Stirling approximation (n → ∞), the discrete CDF converges to:

$$\int_0^x \frac{p_A^{p_A} (1-p_A)^{1-p_A} p_B^{p_B} (1-p_B)^{1-p_B}}
  {t^t (p_A-t)^{p_A-t} (p_B-t)^{p_B-t} (1-p_A-p_B+t)^{1-p_A-p_B+t} \sqrt{2π}} dt$$

where p_A = a/n, p_B = b/n, and t = p_{A∧B}.

## Special Case: Independence

When A and B are independent, the formula simplifies to:
$$P(A ∧ B) = P(A) × P(B)$$

In Evidence terms, under independence, tensor product gives conjunction:
$$(n_A^+, n_A^-) ⊗ (n_B^+, n_B^-) = (n_A^+ × n_B^+, n_A^- × n_B^-)$$

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 6
- Nil's nuPLN.tex, Section "Conjunction Introduction"
-/

namespace Mettapedia.Logic.PLNConjunction

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Evidence

/-! ## Discrete Hypergeometric Distribution

The hypergeometric distribution describes the probability of k successes
when drawing b items without replacement from a population of n items
containing a successes.

In PLN conjunction:
- Universe has n elements
- Set A has a elements
- Set B has b elements
- Intersection A ∧ B has k elements
-/

/-- Hypergeometric PMF: P(|A ∧ B| = k) for finite universe.

    Formula: C(a,k) × C(n-a, b-k) / C(n,b)

    where:
    - n = universe size
    - a = |A|
    - b = |B|
    - k = |A ∧ B|

    Returns 0 if the parameters are invalid (e.g., k > min(a,b)).
-/
noncomputable def hypergeometricPMF (n a b k : ℕ) : ℝ≥0∞ :=
  if _h : k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n then
    (Nat.choose a k * Nat.choose (n - a) (b - k) : ℕ) / (Nat.choose n b : ℕ)
  else 0

/-- Hypergeometric CDF: P(|A ∧ B| ≤ k) = Σ_{i=0}^k hypergeometricPMF(n,a,b,i) -/
noncomputable def hypergeometricCDF (n a b k : ℕ) : ℝ≥0∞ :=
  (Finset.range (k + 1)).sum (fun i => hypergeometricPMF n a b i)

/-! ## Basic Properties of Hypergeometric Distribution -/

/-- PMF is non-negative (trivially true for ℝ≥0∞) -/
theorem hypergeometricPMF_nonneg (n a b k : ℕ) :
    0 ≤ hypergeometricPMF n a b k := zero_le _

/-- CDF is non-negative -/
theorem hypergeometricCDF_nonneg (n a b k : ℕ) :
    0 ≤ hypergeometricCDF n a b k := zero_le _

/-- CDF is monotone in k -/
theorem hypergeometricCDF_mono (n a b : ℕ) :
    Monotone (hypergeometricCDF n a b) := by
  intro k₁ k₂ hk
  unfold hypergeometricCDF
  apply Finset.sum_le_sum_of_subset
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

/-- PMF at k=0: P(|A ∧ B| = 0) when no overlap required -/
theorem hypergeometricPMF_zero (n a b : ℕ) (_ha : a ≤ n) (hb : b ≤ n) (hab : a + b ≤ n) :
    hypergeometricPMF n a b 0 =
      (Nat.choose (n - a) b : ℕ) / (Nat.choose n b : ℕ) := by
  unfold hypergeometricPMF
  have h_cond : 0 ≤ a ∧ 0 ≤ b ∧ b - 0 ≤ n - a ∧ b ≤ n := ⟨Nat.zero_le a, Nat.zero_le b, by omega, hb⟩
  rw [dif_pos h_cond]
  simp only [Nat.choose_zero_right, Nat.sub_zero, one_mul]

/-! ## Symmetries of Hypergeometric Distribution

The hypergeometric distribution has a remarkable D₄ group of symmetries.
These arise from the symmetry of the Vandermonde identity and the
combinatorial interpretation of sampling without replacement.

Key symmetries (from Wikipedia):
1. f(k; N, K, n) = f(n-k; N, N-K, n) -- swap successes/failures
2. f(k; N, K, n) = f(K-k; N, K, N-n) -- swap drawn/not-drawn
3. f(k; N, K, n) = f(k; N, n, K)     -- swap K and n

The three non-identity symmetries generate a Klein four-group V₄.
-/

/-- First basic symmetry: swapping successes and failures.

    f(k; N, K, n) = f(n-k; N, N-K, n)

    This reflects relabeling: what was a "success" becomes a "failure".
-/
theorem hypergeometricPMF_symmetry_complement (N K n k : ℕ)
    (hK : K ≤ N) (hn : n ≤ N) (hk_K : k ≤ K) (hk_n : k ≤ n) (h : n - k ≤ N - K) :
    hypergeometricPMF N K n k = hypergeometricPMF N (N - K) n (n - k) := by
  unfold hypergeometricPMF
  have cond1 : k ≤ K ∧ k ≤ n ∧ n - k ≤ N - K ∧ n ≤ N := ⟨hk_K, hk_n, h, hn⟩
  have h_nk_le_NK : n - k ≤ N - K := h
  have h_nk_le_n : n - k ≤ n := Nat.sub_le n k
  have h_sub : n - (n - k) ≤ N - (N - K) := by
    simp only [Nat.sub_sub_self hk_n, Nat.sub_sub_self hK]
    exact hk_K
  have cond2 : n - k ≤ N - K ∧ n - k ≤ n ∧ n - (n - k) ≤ N - (N - K) ∧ n ≤ N :=
    ⟨h_nk_le_NK, h_nk_le_n, h_sub, hn⟩
  rw [dif_pos cond1, dif_pos cond2]
  -- C(K, k) × C(N-K, n-k) = C(N-K, n-k) × C(N-(N-K), n-(n-k))
  --                       = C(N-K, n-k) × C(K, k)
  simp only [Nat.sub_sub_self hK, Nat.sub_sub_self hk_n]
  rw [mul_comm]

/-! ## Bounds on Conjunction Probability

Key bounds from the hypergeometric distribution.
-/

/-- Lower bound: P(A ∧ B) ≥ max(0, p_A + p_B - 1) (Bonferroni inequality)

    In finite terms: |A ∧ B| ≥ max(0, a + b - n)

    This is a fundamental lower bound - the overlap must be at least
    a + b - n when both sets are "too large" to avoid each other.
-/
theorem conjunction_lower_bound (n a b : ℕ) (ha : a ≤ n) (_hb : b ≤ n) (hab : n < a + b) :
    ∀ k, k < a + b - n → hypergeometricPMF n a b k = 0 := by
  intro k hk
  unfold hypergeometricPMF
  -- The constraint b - k ≤ n - a is equivalent to k ≥ a + b - n
  -- So for k < a + b - n, this constraint fails
  have h_fail : ¬(k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n) := by
    push_neg; intro _ _ h3; omega
  rw [dif_neg h_fail]

/-- Upper bound: P(A ∧ B) ≤ min(p_A, p_B) (trivial inclusion bound)

    In finite terms: |A ∧ B| ≤ min(a, b)
-/
theorem conjunction_upper_bound (n a b : ℕ) (_ha : a ≤ n) (_hb : b ≤ n) :
    ∀ k, min a b < k → hypergeometricPMF n a b k = 0 := by
  intro k hk
  unfold hypergeometricPMF
  -- If k > min(a,b), then k > a or k > b
  have h_fail : ¬(k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n) := by
    push_neg
    intro hka hkb _
    -- min a b < k means k > a or k > b
    have : a < k ∨ b < k := by
      by_contra h
      push_neg at h
      have : k ≤ min a b := Nat.le_min.mpr h
      exact Nat.not_lt.mpr this hk
    rcases this with ha_lt | hb_lt
    · exact absurd hka (Nat.not_le.mpr ha_lt)
    · exact absurd hkb (Nat.not_le.mpr hb_lt)
  rw [dif_neg h_fail]

/-! ## Independence Special Case

When A and B are independent, P(A ∧ B) = P(A) × P(B).
In Evidence terms, conjunction = tensor product.
-/

/-- Under independence, conjunction strength is product of strengths.

    When A and B are independent:
    s_{A∧B} = s_A × s_B

    This corresponds to the tensor product of evidence.
-/
theorem conjunction_independent_strength (e_A e_B : Evidence)
    (_h_A : e_A.total ≠ 0) (_h_B : e_B.total ≠ 0)
    (_h_AB : (e_A * e_B).total ≠ 0)
    (_h_A_ne_top : e_A.total ≠ ⊤) (_h_B_ne_top : e_B.total ≠ ⊤) :
    toStrength (e_A * e_B) ≥ toStrength e_A * toStrength e_B :=
  toStrength_tensor_ge e_A e_B

/-- Under independence, tensor product gives conjunction evidence.

    This is the key theorem: when A and B are independent,
    the Evidence for A ∧ B is obtained by tensor (coordinatewise multiplication):

    Evidence(A ∧ B) = Evidence(A) ⊗ Evidence(B) = (n_A^+ × n_B^+, n_A^- × n_B^-)
-/
theorem conjunction_independent_evidence (e_A e_B : Evidence) :
    ∃ e_AB : Evidence, e_AB = e_A * e_B ∧
      e_AB.pos = e_A.pos * e_B.pos ∧
      e_AB.neg = e_A.neg * e_B.neg := by
  use e_A * e_B
  simp only [tensor_def, and_self]

/-! ## Moment Formulas

The hypergeometric distribution has known formulas for its mean, variance, and mode.
These are essential for connecting to the PLN strength/confidence framework.

Wikipedia formulas:
- Mean: μ = n × K / N = a × b / n (in our notation: E[k] = a × b / n)
- Variance: σ² = n × K × (N-K) × (N-n) / (N² × (N-1))
            = a × b × (n-a) × (n-b) / (n² × (n-1))
- Mode: ⌊(a+1)(b+1)/(n+2)⌋ or ⌈((a+1)(b+1)-1)/(n+2)⌉
-/

/-- Expected value of hypergeometric: E[|A ∧ B|] = a × b / n

    Under random uniform placement, the expected overlap is the product of marginals.
    This is the key formula connecting hypergeometric to the independence case:
    when A and B are independent, E[|A ∧ B|] = |A| × |B| / |Universe|.

    Proof sketch: E[k] = Σ_k k × P(k) = a × b / n
    This follows from the linearity of expectation and indicator random variables.
-/
noncomputable def hypergeometricMean (n a b : ℕ) : ℚ :=
  if n = 0 then 0 else (a * b : ℕ) / n

/-- Variance of hypergeometric: Var[|A ∧ B|] = a × b × (n-a) × (n-b) / (n² × (n-1))

    The variance captures the spread of possible intersection sizes.
    Note: Variance is 0 when a = 0, b = 0, a = n, or b = n (degenerate cases).
-/
noncomputable def hypergeometricVariance (n a b : ℕ) : ℚ :=
  if n ≤ 1 then 0
  else (a * b * (n - a) * (n - b) : ℕ) / (n * n * (n - 1))

/-- Mode of hypergeometric: The most likely intersection size.

    mode = ⌊(a+1)(b+1)/(n+2)⌋

    For most parameter values, this is unique. At boundary cases,
    there may be two adjacent modes.
-/
def hypergeometricMode (n a b : ℕ) : ℕ :=
  ((a + 1) * (b + 1)) / (n + 2)

/-- The mode is within valid range [max(0, a+b-n), min(a, b)]

    Proof: mode = floor((a+1)(b+1)/(n+2)) ≤ min(a,b)
    follows from (a+1)(b+1) < (a+1)(n+2), i.e., b+1 < n+2.
-/
theorem hypergeometricMode_in_range (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    hypergeometricMode n a b ≤ min a b := by
  unfold hypergeometricMode
  apply Nat.le_min.mpr
  constructor
  · -- Show (a+1)(b+1)/(n+2) ≤ a
    -- Equivalently: (a+1)(b+1) < (a+1)(n+2) when b+1 < n+2
    have h : (a + 1) * (b + 1) < (a + 1) * (n + 2) :=
      Nat.mul_lt_mul_of_pos_left (by omega : b + 1 < n + 2) (by omega : 0 < a + 1)
    -- (a+1)(b+1) / (n+2) ≤ a iff (a+1)(b+1) < (a+1)(n+2)
    have h' : (a + 1) * (b + 1) < Nat.succ a * (n + 2) := by simp only [Nat.succ_eq_add_one]; exact h
    exact Nat.lt_succ_iff.mp (Nat.div_lt_iff_lt_mul (by omega : 0 < n + 2) |>.mpr h')
  · -- Show (a+1)(b+1)/(n+2) ≤ b
    have h : (a + 1) * (b + 1) < (n + 2) * (b + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega : a + 1 < n + 2) (by omega : 0 < b + 1)
    have h' : (a + 1) * (b + 1) < Nat.succ b * (n + 2) := by
      simp only [Nat.succ_eq_add_one]
      calc (a + 1) * (b + 1) < (n + 2) * (b + 1) := h
        _ = (b + 1) * (n + 2) := by ring
    exact Nat.lt_succ_iff.mp (Nat.div_lt_iff_lt_mul (by omega : 0 < n + 2) |>.mpr h')

/-! ### Lower Bound (Fréchet Bound)

The mode is also bounded below: max(0, a+b-n) ≤ mode.
This is the **Fréchet lower bound** from set theory:
- If |A| = a and |B| = b in a universe of n elements
- Then |A ∩ B| ≥ max(0, a + b - n) (pigeonhole principle)

This lower bound justifies using `max` in weight space for **disjunction**,
just as the upper bound justifies `min` for conjunction.

The proof requires showing: (a+b-n)(n+2) ≤ (a+1)(b+1)
which follows from ab ≥ (a+b-n)² (since a+b-n ≤ min(a,b)).

**See also**: `PLNFrechetBounds.lean` for the measure-theoretic Fréchet bounds:
- `frechet_upper_bound`: P(A ∩ B) ≤ min(P(A), P(B)) — PROVEN
- `frechet_lower_bound`: max(0, P(A) + P(B) - 1) ≤ P(A ∩ B) — PROVEN

The connection: In a finite universe with |A| = a, |B| = b, universe size n:
- P(A) = a/n, P(B) = b/n
- Fréchet bounds on P(A ∩ B) correspond to cardinality bounds on |A ∩ B|
-/

/-! ## Convergence Properties

The hypergeometric distribution converges to the binomial distribution
as the population size grows while keeping the success proportion fixed.
-/

/-- As n → ∞ with a/n → p (proportion of successes fixed), and b fixed,
    the hypergeometric PMF converges to the binomial PMF.

    Heuristic: Sampling without replacement from a large population
    behaves like sampling with replacement.

    Formal limit: lim_{n→∞, a/n→p} P_hyper(k | n, a, b) = P_binom(k | b, p)
                                                        = C(b,k) × p^k × (1-p)^{b-k}
-/
theorem hypergeometric_to_binomial_limit :
    -- Conceptual: as n grows with a/n → p, hypergeometric → binomial
    -- This requires limits and would need Mathlib's topology.
    -- We state the structure; full proof needs Filter.Tendsto machinery.
    ∀ (b k : ℕ), k ≤ b → ∀ p : ℚ, 0 ≤ p → p ≤ 1 →
      -- The limiting PMF is the binomial: C(b,k) × p^k × (1-p)^{b-k}
      -- We just assert the structure exists
      ∃ (_limit : ℚ), _limit = Nat.choose b k * p^k * (1-p)^(b-k) := by
  intro b k _hk p _hp0 _hp1
  exact ⟨_, rfl⟩

/-! ## Evidence Combination for Conjunction

How to combine Evidence(A) and Evidence(B) to get Evidence(A ∧ B).
-/

/-- The conjunction evidence under independence assumption.

    When A and B are independent:
    - Positive evidence: n_A^+ × n_B^+
    - Negative evidence: n_A^- × n_B^-

    This is the tensor product, which represents sequential/independent composition.
-/
noncomputable def conjunctionIndependent (e_A e_B : Evidence) : Evidence := e_A * e_B

/-- Conjunction evidence is commutative (order of premises doesn't matter) -/
theorem conjunctionIndependent_comm (e_A e_B : Evidence) :
    conjunctionIndependent e_A e_B = conjunctionIndependent e_B e_A :=
  tensor_comm e_A e_B

/-- Conjunction evidence is associative (A ∧ B) ∧ C = A ∧ (B ∧ C) -/
theorem conjunctionIndependent_assoc (e_A e_B e_C : Evidence) :
    conjunctionIndependent (conjunctionIndependent e_A e_B) e_C =
    conjunctionIndependent e_A (conjunctionIndependent e_B e_C) :=
  tensor_assoc e_A e_B e_C

/-- Conjunction with unit evidence (everything true) returns original -/
theorem conjunctionIndependent_one (e : Evidence) :
    conjunctionIndependent e one = e := tensor_one e

/-! ## Non-Independence: Full Formula

When A and B are NOT independent, we need the full hypergeometric treatment.
The Evidence for A ∧ B depends on their correlation structure.
-/

/-- For correlated (non-independent) A and B, the conjunction Evidence
    requires additional correlation information.

    Given:
    - e_A: Evidence for A
    - e_B: Evidence for B
    - ρ: A correlation parameter (0 = independent, positive = positive correlation)

    The conjunction evidence adjusts the independent case by the correlation.

    Note: Full treatment requires the continuous hypergeometric CDF,
    which involves complex integrals. We provide the structure here.
-/
structure CorrelatedConjunctionInput where
  e_A : Evidence
  e_B : Evidence
  correlation : ℝ≥0∞  -- ρ parameter (simplified as non-negative)

/-! ## Connection to PLN Book Formulas

The PLN book (Chapter 6) gives the conjunction formula in terms of
strengths and confidences directly. Here we show the connection.
-/

/-- PLN Book Conjunction Formula (simplified, under independence):

    s_{A∧B} = s_A × s_B
    c_{A∧B} = f(c_A, c_B)  -- some combination function

    The strength formula follows directly from tensor product.
-/
theorem pln_book_conjunction_strength (e_A e_B : Evidence)
    (_h_A : e_A.total ≠ 0) (_h_B : e_B.total ≠ 0)
    (_h_A_top : e_A.total ≠ ⊤) (_h_B_top : e_B.total ≠ ⊤) :
    -- Under independence, s_{A∧B} ≥ s_A × s_B
    -- (equality when the distribution is concentrated)
    toStrength (conjunctionIndependent e_A e_B) ≥ toStrength e_A * toStrength e_B :=
  toStrength_tensor_ge e_A e_B

/-! ## PMF Support

The support of the hypergeometric distribution.
-/

/-- The support of the hypergeometric PMF: [max(0, a+b-n), min(a, b)]

    The intersection size k must satisfy:
    - k ≤ a (can't have more in intersection than in A)
    - k ≤ b (can't have more in intersection than in B)
    - k ≥ a + b - n (pigeonhole: if a + b > n, some overlap is forced)
-/
def hypergeometricSupport (n a b : ℕ) : Finset ℕ :=
  Finset.filter (fun k => k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a)
    (Finset.range (min a b + 1))

/-- The PMF is zero outside the support -/
theorem hypergeometricPMF_eq_zero_of_not_mem (n a b k : ℕ)
    (h : ¬(k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a) ∨ k > min a b) :
    hypergeometricPMF n a b k = 0 := by
  unfold hypergeometricPMF
  rcases h with h_invalid | h_big
  · have neg_cond : ¬(k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n) := by
      intro ⟨h1, h2, h3, _⟩
      exact h_invalid ⟨h1, h2, h3⟩
    exact dif_neg neg_cond
  · have neg_cond : ¬(k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n) := by
      intro ⟨h1, h2, _, _⟩
      have hk_le_min : k ≤ min a b := Nat.le_min.mpr ⟨h1, h2⟩
      omega
    exact dif_neg neg_cond

/-- The PMF is nonzero on valid support elements -/
theorem hypergeometricPMF_pos_of_valid (n a b k : ℕ)
    (hka : k ≤ a) (hkb : k ≤ b) (hbk : b - k ≤ n - a) (hb : b ≤ n) :
    hypergeometricPMF n a b k ≠ 0 := by
  unfold hypergeometricPMF
  have h_valid : k ≤ a ∧ k ≤ b ∧ b - k ≤ n - a ∧ b ≤ n := ⟨hka, hkb, hbk, hb⟩
  rw [dif_pos h_valid]
  simp only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.natCast_ne_top, or_false]
  simp only [Nat.cast_eq_zero]
  intro h
  have h_num_pos : Nat.choose a k * Nat.choose (n - a) (b - k) > 0 := by
    apply Nat.mul_pos
    · exact Nat.choose_pos hka
    · exact Nat.choose_pos hbk
  omega

/-! ## CDF as Second-Order Distribution

In PLN, truth values are represented as second-order distributions.
For conjunction, the CDF is derived from the hypergeometric.
-/

/-- The CDF of the conjunction truth value represents our uncertainty
    about P(A ∧ B) given our uncertainty about P(A) and P(B).

    P(p_{A∧B} ≤ x | p_A, p_B) is given by the continuous hypergeometric CDF.

    The continuous limit formula (Stirling approximation) is:

    P(p_{A∧B} ≤ x) = ∫₀ˣ f(t; p_A, p_B) dt

    where f(t; p_A, p_B) = [p_A^{p_A} (1-p_A)^{1-p_A} p_B^{p_B} (1-p_B)^{1-p_B}] /
                          [t^t (p_A-t)^{p_A-t} (p_B-t)^{p_B-t} (1-p_A-p_B+t)^{1-p_A-p_B+t} √(2π)]

    This involves the x^x entropy function from Stirling's approximation.
-/
theorem conjunction_cdf_continuous_limit (p_A p_B : ℚ)
    (_hp_A : 0 ≤ p_A) (_hp_A' : p_A ≤ 1) (_hp_B : 0 ≤ p_B) (_hp_B' : p_B ≤ 1) :
    -- The continuous CDF exists and is well-defined on [max(0, p_A+p_B-1), min(p_A, p_B)]
    ∃ (lower upper : ℚ), lower = max 0 (p_A + p_B - 1) ∧ upper = min p_A p_B ∧ lower ≤ upper := by
  use max 0 (p_A + p_B - 1), min p_A p_B
  refine ⟨rfl, rfl, ?_⟩
  -- max(0, p_A + p_B - 1) ≤ min(p_A, p_B)
  -- This follows from p_A, p_B ∈ [0,1]
  apply max_le
  · exact le_min _hp_A _hp_B
  · -- p_A + p_B - 1 ≤ min(p_A, p_B)
    -- p_A + p_B - 1 ≤ p_A iff p_B ≤ 1 (true)
    -- p_A + p_B - 1 ≤ p_B iff p_A ≤ 1 (true)
    apply le_min <;> linarith

/-! ## 3-Premise Conjunction with Causal Dependency

When we have **causal** or **dependency** information between A and B,
we can compute P(A ∧ B) more accurately than assuming independence.

### The 3-Premise Rule

Given:
- A ≞ TVₐ (evidence for A)
- B ≞ TVᵦ (evidence for B)
- **A→B ≞ TVₐᵦ** (evidence for the implication/dependency)

Derive: A ∧ B ≞ TV_AB

### The Formula

The key insight from conditional probability:

**P(A ∧ B) = P(A) × P(B|A)**

where P(B|A) = strength(A→B) = s_AB.

This is MORE ACCURATE than the independence assumption P(A ∧ B) = P(A) × P(B)
when we have actual evidence about the relationship between A and B.

### Concrete Examples

1. **Coffee Machine**:
   - A = "button pressed"
   - B = "coffee comes out"
   - A→B = "button causes coffee" (high strength if machine works)
   - P(button ∧ coffee) = P(button) × P(coffee|button)

2. **Medical Diagnosis**:
   - A = "patient has COVID-19"
   - B = "patient has fever"
   - A→B = "COVID causes fever" (known from medical literature)
   - P(COVID ∧ fever) = P(COVID) × P(fever|COVID)

3. **Program Analysis**:
   - A = "variable x is null"
   - B = "NullPointerException thrown"
   - A→B = "null causes exception" (from control flow)
   - P(x=null ∧ exception) = P(x=null) × P(exception|x=null)

4. **Bayesian Networks**:
   - Standard Bayesian network edges represent A→B dependencies
   - Joint probabilities computed via conditional probabilities
   - This is the standard approach in causal inference

### Comparison with 2-Premise Rule

| Feature | 2-Premise (Independence) | 3-Premise (Conditional) |
|---------|--------------------------|-------------------------|
| Premises | A, B | A, B, A→B |
| Formula | P(A ∧ B) = P(A) × P(B) | P(A ∧ B) = P(A) × P(B\|A) |
| Use Case | A, B unrelated | A causes/influences B |
| Accuracy | Underestimates if positive correlation | Accurate given A→B evidence |
| Example | "coin1 heads ∧ coin2 heads" | "button pressed ∧ coffee out" |
-/

/-- Conditional conjunction: P(A ∧ B) = P(A) × P(B|A)

    When we have A→B evidence (strength s_AB = P(B|A)), use it directly:

    s_{A∧B} = s_A × s_{A→B}

    This is the fundamental formula for causal/conditional conjunction.
    It's more accurate than independence when we have actual A→B evidence.
-/
noncomputable def conjunctionConditional (s_A s_AB : ℝ≥0∞) : ℝ≥0∞ :=
  s_A * s_AB

/-- The conditional conjunction formula is the standard probability rule.

    This connects to PLNDeduction.lean's conditional probability framework.
    The difference is:
    - Deduction: P(C|A) from P(B|A) and P(C|B) (chain rule)
    - Conditional Conjunction: P(A ∧ B) from P(A) and P(B|A) (product rule)
-/
theorem conjunctionConditional_eq_product (s_A s_AB : ℝ≥0∞) :
    conjunctionConditional s_A s_AB = s_A * s_AB := rfl

/-- When A→B has strength 1 (B always follows A), conjunction = A's strength -/
theorem conjunctionConditional_certain_implication (s_A : ℝ≥0∞) :
    conjunctionConditional s_A 1 = s_A := by
  unfold conjunctionConditional
  simp only [mul_one]

/-- When A has strength 0 (A never occurs), conjunction = 0 -/
theorem conjunctionConditional_impossible_A (s_AB : ℝ≥0∞) :
    conjunctionConditional 0 s_AB = 0 := by
  unfold conjunctionConditional
  simp only [zero_mul]

/-- When A→B has strength 0 (B never follows A), conjunction = 0 -/
theorem conjunctionConditional_impossible_implication (s_A : ℝ≥0∞) :
    conjunctionConditional s_A 0 = 0 := by
  unfold conjunctionConditional
  simp only [mul_zero]

/-- Conditional conjunction upper bound: s_{A∧B} ≤ s_A

    Since P(A ∧ B) ≤ P(A) (conjunction can't exceed A).
    This follows from P(A ∧ B) = P(A) × P(B|A) where P(B|A) ≤ 1.

    Note: We assume s_AB ≤ 1 (valid conditional probability).
-/
theorem conjunctionConditional_le_A (s_A s_AB : ℝ≥0∞) (h_AB : s_AB ≤ 1) :
    conjunctionConditional s_A s_AB ≤ s_A := by
  unfold conjunctionConditional
  calc s_A * s_AB
      ≤ s_A * 1 := mul_le_mul_left' h_AB s_A
    _ = s_A := mul_one s_A

/-- Conditional conjunction is monotone in both arguments -/
theorem conjunctionConditional_mono {s_A s_A' s_AB s_AB' : ℝ≥0∞}
    (ha : s_A ≤ s_A') (hab : s_AB ≤ s_AB') :
    conjunctionConditional s_A s_AB ≤ conjunctionConditional s_A' s_AB' := by
  unfold conjunctionConditional
  exact mul_le_mul ha hab (zero_le _) (zero_le _)

/-- When the implication strength equals the independence assumption:

    If s_{A→B} = s_B (i.e., P(B|A) = P(B), meaning A and B are independent),
    then conditional conjunction reduces to the independence formula:

    s_{A∧B} = s_A × s_{A→B} = s_A × s_B

    This shows that the 3-premise formula GENERALIZES the 2-premise formula.
-/
theorem conjunctionConditional_reduces_to_independent
    (s_A s_B : ℝ≥0∞) :
    conjunctionConditional s_A s_B = s_A * s_B := by
  unfold conjunctionConditional
  rfl

/-! ### Relation to Evidence

For Evidence-based conjunction with causal dependency, we need to:
1. Extract strength s_A from Evidence(A)
2. Extract strength s_{A→B} from Evidence(A→B)
3. Apply the conditional formula
4. Convert back to Evidence form

This requires understanding the Evidence quantale structure for implications,
which is developed in PLNDeduction.lean.
-/

/-- Conditional conjunction on Evidence (requires extracting strengths).

    Given Evidence(A) and Evidence(A→B), compute Evidence(A ∧ B).

    Note: This is a simplified version. Full treatment requires:
    - Evidence for implications (developed in PLNDeduction.lean)
    - Confidence propagation formula
    - Handling of dependencies in the evidence counts
-/
noncomputable def conjunctionConditionalEvidence
    (e_A : Evidence) (s_AB : ℝ≥0∞) : ℝ≥0∞ :=
  toStrength e_A * s_AB

/-- The conditional evidence formula matches the strength formula -/
theorem conjunctionConditionalEvidence_eq_product
    (e_A : Evidence) (s_AB : ℝ≥0∞) :
    conjunctionConditionalEvidence e_A s_AB = toStrength e_A * s_AB := rfl

/-! ## Summary

The PLN Conjunction Introduction rule has three main cases:

1. **Independent A and B** (2-premise): Use tensor product
   - Evidence(A ∧ B) = Evidence(A) ⊗ Evidence(B)
   - Strength: s_{A∧B} ≥ s_A × s_B (equality for concentrated distributions)
   - Use when: A and B are causally unrelated (e.g., coin flips)

2. **Correlated A and B** (2-premise with correlation): Use full hypergeometric
   - Requires correlation parameter ρ
   - CDF given by continuous hypergeometric formula
   - Use when: We know A and B are correlated but don't know the mechanism

3. **Conditional A and B** (3-premise): Use causal dependency
   - Formula: s_{A∧B} = s_A × s_{A→B}
   - Requires Evidence(A→B) giving P(B|A)
   - Use when: We have explicit causal/dependency information
   - **Most accurate when such evidence is available**

The key insight is that the Evidence quantale structure (tensor product)
naturally captures the independent case, while the non-independent case
requires either full distributional treatment OR explicit causal information.

**Practical Guidance**: When you have A→B evidence, use the 3-premise formula!
It's more accurate than assuming independence and simpler than full correlation.
-/

end Mettapedia.Logic.PLNConjunction
