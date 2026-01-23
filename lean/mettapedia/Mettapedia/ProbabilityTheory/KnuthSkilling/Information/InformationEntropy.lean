import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ConditionalProbability.Basic
import Mettapedia.ProbabilityTheory.Foundations.Distributions.ProbDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# K&S Section 8: Information and Entropy

This file formalizes **Section 8** of Knuth & Skilling (2012), deriving information
and entropy as special cases of the variational potential from Appendix C.

## Key Point: DERIVATION, Not Definition

Shannon entropy is **not just defined** here—it is **derived** from the variational
framework established in Appendix C (Variational/Main.lean). The derivation shows
that the entropy formula is an "inevitable consequence" of seeking a variational
quantity for probability distributions.

## Derivation Chain

1. **Appendix C** establishes: Any variational potential satisfying
   `H'(m_x · m_y) = λ(m_x) + μ(m_y)` with measurability has the form:
   ```
   H(m) = A + B·m + C·(m·log(m) - m)
   ```

2. **Section 6** (Divergence.lean) specializes to divergence with `A = u`, `B = -log(u)`, `C = 1`.

3. **Section 8** (this file) specializes to:
   - **Information (8.1)**: Divergence for probability distributions (normalized measures)
   - **Entropy (8.2)**: Setting `A = 0`, `B = C` gives `H = C·Σ p_k·log(p_k)`
     With `C = -1`, this is Shannon entropy `S(p) = -Σ p_k·log(p_k)`.

## Shannon's Three Properties

K&S claim these are "inevitable consequences of seeking a variational quantity":
1. **Continuity**: S is a continuous function of its arguments
2. **Monotonicity**: If there are n equal choices (p_k = 1/n), then S increases in n
3. **Grouping**: If a choice is broken down, S adds according to expectation

## References

- K&S "Foundations of Inference" (2012), Section 8 "Information and Entropy"
- Shannon, C. E. (1948). "A Mathematical Theory of Communication"
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

open Real Finset BigOperators
open scoped Topology ENNReal

open Mettapedia.ProbabilityTheory.KnuthSkilling.Variational
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence

/-! ## ProbDist (Foundations)

We re-export the finite distribution structure from Foundations so the K&S development
can refer to `ProbDist` without depending on the Foundations namespace directly.
-/

/-- ProbDist is defined in Foundations; we keep the KS-facing alias here. -/
abbrev ProbDist := Mettapedia.ProbabilityTheory.Foundations.Distributions.ProbDist

namespace ProbDist
  export Mettapedia.ProbabilityTheory.Foundations.Distributions.ProbDist
    (ext le_one eq_one_implies_others_zero pointMass pointMass_apply)
end ProbDist

/-! ## The `0 · log(0) = 0` Convention

Shannon entropy uses the convention that `0 · log(0) = 0`, justified by
`lim_{p→0⁺} p · log(p) = 0`. In Lean, this follows from `0 * x = 0` for any `x`,
but we make it explicit here for mathematical clarity.
-/

/-- **The 0·log(0) = 0 convention**: `0 * log(0) = 0` in Lean's reals.

This is the standard convention for entropy calculations. Mathematically justified by
`lim_{p→0⁺} p · log(p) = 0` (L'Hôpital's rule). -/
@[simp]
theorem zero_mul_log_zero : (0 : ℝ) * log 0 = 0 := zero_mul _

/-- The entropy form at `m = 0` simplifies to just `A`.

This is crucial: zero-probability states contribute nothing to entropy. -/
@[simp]
theorem entropyForm_zero (A B C : ℝ) : entropyForm A B C 0 = A := by
  unfold entropyForm
  simp

/-- Atom divergence at `w = 0` equals `u`.

When the actual distribution has zero probability, divergence equals the reference. -/
theorem atomDivergence_zero (u : ℝ) : atomDivergence 0 u = u := by
  unfold atomDivergence
  simp

/-! ## Connection to K&S Derivation

This section connects the standalone `ProbDist` definition to the K&S derivation
of probability theory via `Bivaluation` and `baseMeasure`.

**Key theorem**: Given a normalized Bivaluation on a finite Boolean algebra with atoms
`{a₁, ..., aₙ}`, the values `baseMeasure B aᵢ` form a probability distribution.

This bridges the gap between:
- K&S Section 7: Derives `prob_eq_measure_ratio`: `p(x|t) = m(x ∧ t) / m(t)`
- K&S Section 8: Uses probability distributions for entropy/information

The connection shows that `ProbDist` is not just a standalone definition but is
**grounded in the K&S derivation**.
-/
section ConnectionToDerivation

open Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ConditionalProbability

/-- For Fin (m+1), iSup splits into sup of iSup over Fin m and the last element. -/
theorem iSup_fin_succ {α : Type*} [CompleteLattice α] {m : ℕ} (f : Fin (m + 1) → α) :
    -- Note: This only requires CompleteLattice (no distributivity needed)
    ⨆ i : Fin (m + 1), f i = (⨆ i : Fin m, f (Fin.castSucc i)) ⊔ f (Fin.last m) := by
  apply le_antisymm
  · -- ⨆ f ≤ (⨆ castSucc) ⊔ f(last)
    apply iSup_le
    intro i
    by_cases hi : i = Fin.last m
    · -- i = last m
      rw [hi]
      exact le_sup_right
    · -- i ≠ last m, so i = castSucc j for some j
      have hj : ∃ j : Fin m, i = Fin.castSucc j := by
        rcases Fin.exists_castSucc_eq.mpr hi with ⟨j, hj⟩
        exact ⟨j, hj.symm⟩
      rcases hj with ⟨j, hj⟩
      rw [hj]
      exact le_sup_of_le_left (le_iSup (f ∘ Fin.castSucc) j)
  · -- (⨆ castSucc) ⊔ f(last) ≤ ⨆ f
    apply sup_le
    · apply iSup_le
      intro j
      exact le_iSup f (Fin.castSucc j)
    · exact le_iSup f (Fin.last m)

open Finset in
/-- Helper lemma: For a finite disjoint family, baseMeasure of the supremum equals the sum.

This is the n-ary extension of `baseMeasure.additive`.

Note: Requires `Order.Frame` (or stronger) for `iSup_disjoint_iff` to apply. -/
theorem baseMeasure_sum_eq_sup_of_disjoint
    {α : Type*} [Order.Frame α]
    (B : Bivaluation α)
    {n : ℕ} (atoms : Fin n → α)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (atoms i) (atoms j)) :
    ∑ i : Fin n, baseMeasure B (atoms i) = baseMeasure B (⨆ i, atoms i) := by
  induction n with
  | zero =>
    -- Empty sum is 0, empty iSup is ⊥
    simp only [Finset.univ_eq_empty, sum_empty, iSup_of_empty]
    -- baseMeasure B ⊥ = B.p ⊥ ⊤
    -- If ⊤ = ⊥, then baseMeasure B ⊥ = B.p ⊥ ⊥ which could be anything
    -- But we want 0 = baseMeasure B ⊥
    -- This is tricky because baseMeasure.bot requires hTop : ⊤ ≠ ⊥
    -- For the degenerate case ⊤ = ⊥, we handle separately
    by_cases h : (⊤ : α) = ⊥
    · -- Degenerate: ⊤ = ⊥, so the lattice is trivial
      -- baseMeasure B ⊥ = B.p ⊥ ⊤ = B.p ⊥ ⊥
      -- We need positivity of p only when ⊥ < x, but ⊥ ≤ ⊤ = ⊥ means nothing is > ⊥
      -- Actually in this case ⊥ = ⊤, so baseMeasure B ⊥ = B.p ⊤ ⊤ (by context)
      unfold baseMeasure
      rw [B.p_context ⊥ ⊤]
      simp only [bot_inf_eq]
      -- p(⊥|⊤) when ⊤ = ⊥ means p(⊥|⊥) = p(⊥ ⊓ ⊥|⊥) = p(⊥|⊥)
      -- We need to show this is 0. Use p_sum_disjoint with ⊥ ⊔ ⊥ = ⊥
      have hsum := B.p_sum_disjoint ⊥ ⊥ ⊤ disjoint_bot_left (by simp)
      simp at hsum
      -- hsum : B.p ⊥ ⊤ = 0
      exact hsum.symm
    · -- Non-degenerate: use baseMeasure.bot
      exact (baseMeasure.bot B h).symm
  | succ m ih =>
    -- Split the sum: ∑ i : Fin (m+1), f i = ∑ i : Fin m, f (castSucc i) + f (last m)
    rw [Fin.sum_univ_castSucc]
    -- Split the iSup
    rw [iSup_fin_succ]
    -- Disjointness for the recursive call
    have hDisj' : ∀ i j : Fin m, i ≠ j →
        Disjoint (atoms (Fin.castSucc i)) (atoms (Fin.castSucc j)) := fun i j hij => by
      have h : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_injective m h)
      exact hDisjoint (Fin.castSucc i) (Fin.castSucc j) h
    -- Apply induction hypothesis
    have ih' : ∑ i : Fin m, baseMeasure B (atoms (Fin.castSucc i)) =
        baseMeasure B (⨆ i : Fin m, atoms (Fin.castSucc i)) := ih (atoms ∘ Fin.castSucc) hDisj'
    rw [ih']
    -- Now use binary additivity: need disjointness between (⨆ castSucc) and (last)
    have hDisjLast : Disjoint (⨆ i : Fin m, atoms (Fin.castSucc i)) (atoms (Fin.last m)) := by
      rw [iSup_disjoint_iff]
      intro i
      have h : Fin.castSucc i ≠ Fin.last m := Fin.castSucc_ne_last i
      exact hDisjoint (Fin.castSucc i) (Fin.last m) h
    -- Apply baseMeasure.additive
    rw [← baseMeasure.additive B _ _ hDisjLast]

open Finset in
/-- **Finite partition induces ProbDist** (key connection theorem).

Given a Bivaluation with chaining associativity on a finite Boolean algebra,
and a complete partition of ⊤ into atoms `{a₁, ..., aₙ}`, the baseMeasure
values form a probability distribution.

This connects `ProbDist` to the K&S derivation: probability distributions
arise from the derived `baseMeasure` on finite event spaces.
-/
noncomputable def ProbDist.ofBivaluationPartition
    {α : Type*} [Order.Frame α]
    (B : Bivaluation α) [ChainingAssociativity α B]
    (hNorm : ∀ t : α, ⊥ < t → B.p t t = 1)
    {n : ℕ} (hn : 0 < n) (atoms : Fin n → α)
    (hPos : ∀ i, ⊥ < atoms i)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (atoms i) (atoms j))
    (hCover : ⨆ i, atoms i = ⊤) : ProbDist n where
  p i := baseMeasure B (atoms i)
  nonneg i := le_of_lt (B.p_pos (atoms i) ⊤ (hPos i) le_top)
  sum_one := by
    -- The atoms partition ⊤, so Σᵢ m(aᵢ) = m(⊤) = p(⊤|⊤) = 1
    -- First prove that ⊤ ≠ ⊥ (needed for baseMeasure.top_eq_one)
    have hTop : (⊤ : α) ≠ ⊥ := by
      intro h
      have i0 : Fin n := ⟨0, hn⟩
      have hbot : ⊥ < atoms i0 := hPos i0
      have htop_le : ⊤ ≤ (⊥ : α) := by rw [h]
      have hatoms_le : atoms i0 ≤ ⊤ := le_top
      have : atoms i0 ≤ ⊥ := le_trans hatoms_le htop_le
      have hcontr : atoms i0 = ⊥ := le_antisymm this bot_le
      exact absurd hcontr (ne_of_gt hbot)
    -- Use the sum = sup lemma
    rw [baseMeasure_sum_eq_sup_of_disjoint B atoms hDisjoint]
    -- Use hCover and top_eq_one
    rw [hCover]
    exact baseMeasure.top_eq_one B hNorm hTop

/-- The induced probability distribution agrees with baseMeasure. -/
theorem ProbDist.ofBivaluationPartition_eq
    {α : Type*} [Order.Frame α]
    (B : Bivaluation α) [ChainingAssociativity α B]
    (hNorm : ∀ t : α, ⊥ < t → B.p t t = 1)
    {n : ℕ} (hn : 0 < n) (atoms : Fin n → α)
    (hPos : ∀ i, ⊥ < atoms i)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (atoms i) (atoms j))
    (hCover : ⨆ i, atoms i = ⊤) (i : Fin n) :
    (ProbDist.ofBivaluationPartition B hNorm hn atoms hPos hDisjoint hCover).p i =
      baseMeasure B (atoms i) := rfl

end ConnectionToDerivation

section

/-- **Kullback-Leibler divergence** for probability distributions.

This is the specialization of general divergence (Section 6) to the probability case.
K&S Equation 57: `H(p | q) = Σ_k p_k · log(p_k / q_k)`.

Important: this expression is only mathematically meaningful when the source distribution `q`
is strictly positive (or at least positive on the support of `p`), since otherwise one encounters
the standard `p_k > 0 ∧ q_k = 0` divergence-to-∞ case.

Lean's `Real.log` and `/` are total (`log 0 = 0` and `x / 0 = 0`), so we **must not** define KL
divergence on arbitrary `ProbDist` without extra hypotheses.  We therefore take strict positivity
of `q` on the support of `p` as an explicit input (absolute continuity in the discrete setting),
matching the regime in which the K&S formula is intended to apply.

See `klDivergenceTop` for an **extended** version taking values in `ℝ≥0∞`, which returns `∞`
when this positivity condition fails.
-/
noncomputable def klDivergence {n : ℕ} (P Q : ProbDist n)
    (_hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) : ℝ :=
  ∑ i, P.p i * log (P.p i / Q.p i)

end

/-- **Extended** Kullback-Leibler divergence (`ℝ≥0∞`-valued).

If `Q` is positive on the support of `P`, this is the finite value `ENNReal.ofReal (klDivergence P Q …)`.
Otherwise it is `∞` (the standard `p_i > 0 ∧ q_i = 0` divergence-to-∞ case).

This mirrors mathlib's measure-theoretic definition of `Measure.klDiv`:
`klDiv μ ν = if μ ≪ ν then … else ∞`. -/
noncomputable def klDivergenceTop {n : ℕ} (P Q : ProbDist n) : ℝ≥0∞ := by
  classical
  exact
    if hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i then
      ENNReal.ofReal (klDivergence P Q hQ_pos)
    else
      ⊤

theorem klDivergenceTop_eq_of_support_pos {n : ℕ} (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    klDivergenceTop P Q = ENNReal.ofReal (klDivergence P Q hQ_pos) := by
  classical
  simp [klDivergenceTop, dif_pos hQ_pos]

theorem klDivergenceTop_eq_top_of_support_violation {n : ℕ} (P Q : ProbDist n) (i : Fin n)
    (hPi : P.p i ≠ 0) (hQi : Q.p i = 0) : klDivergenceTop P Q = ⊤ := by
  classical
  have hnot : ¬(∀ j, P.p j ≠ 0 → 0 < Q.p j) := by
    intro h
    have hQi_pos : 0 < Q.p i := h i hPi
    simp [hQi] at hQi_pos
  simp [klDivergenceTop, dif_neg hnot]

/-- **Connection to general divergence**: The KL formula arises from divergence
when the normalization constraints Σp = Σq = 1 are applied.

General divergence: `D(p||q) = Σ (q_i - p_i + p_i·log(p_i/q_i))`
With Σp = Σq = 1: `D(p||q) = (1 - 1) + Σ p_i·log(p_i/q_i) = Σ p_i·log(p_i/q_i)`

Note: This equation holds at the sum level, not term-wise (the (q_i - p_i) terms
cancel when summed over normalized distributions).
-/
theorem klDivergence_from_divergence_formula {n : ℕ} (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    klDivergence P Q hQ_pos = ∑ i, atomDivergence (P.p i) (Q.p i) - (∑ i, Q.p i - ∑ i, P.p i) := by
  simp only [klDivergence, P.sum_one, Q.sum_one, sub_self, sub_zero]
  -- Goal: Σ p*log(p/q) = Σ (q - p + p*log(p/q))
  -- Key: Σ(q-p) = 1 - 1 = 0, so RHS = 0 + Σ p*log(p/q) = LHS
  have hcancel : ∑ i, (Q.p i - P.p i) = 0 := by
    rw [sum_sub_distrib, Q.sum_one, P.sum_one]; ring
  have hrw : ∑ i, atomDivergence (P.p i) (Q.p i) =
      ∑ i, ((Q.p i - P.p i) + P.p i * log (P.p i / Q.p i)) := by
    apply sum_congr rfl
    intro i _
    unfold atomDivergence; ring
  rw [hrw, sum_add_distrib, hcancel, zero_add]

/-- KL divergence is non-negative (Gibbs' inequality).

**Strict version**: Requires all probabilities to be strictly positive.
See `klDivergence_nonneg'` for a relaxed version allowing zeros in P. -/
theorem klDivergence_nonneg {n : ℕ} (P Q : ProbDist n)
    (hP_pos : ∀ i, 0 < P.p i) (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    0 ≤ klDivergence P Q hQ_pos := by
  -- This follows from Gibbs' inequality on the full divergence
  have hdiv_nonneg : 0 ≤ ∑ i, atomDivergence (P.p i) (Q.p i) := by
    apply sum_nonneg
    intro i _
    have hQi : 0 < Q.p i := hQ_pos i (ne_of_gt (hP_pos i))
    exact atomDivergence_nonneg (P.p i) (Q.p i) (hP_pos i) hQi
  -- The (q - p) terms sum to 0 due to normalization
  have hcancel : ∑ i, (Q.p i - P.p i) = 0 := by
    rw [sum_sub_distrib, Q.sum_one, P.sum_one]; ring
  -- Expand atomDivergence and split the sum
  have hexpand : ∑ i, atomDivergence (P.p i) (Q.p i) =
      (∑ i, (Q.p i - P.p i)) + ∑ i, P.p i * log (P.p i / Q.p i) := by
    have hrw : ∑ i, atomDivergence (P.p i) (Q.p i) =
        ∑ i, ((Q.p i - P.p i) + P.p i * log (P.p i / Q.p i)) := by
      apply sum_congr rfl
      intro i _
      unfold atomDivergence; ring
    rw [hrw, sum_add_distrib]
  rw [hexpand, hcancel, zero_add] at hdiv_nonneg
  simpa [klDivergence] using hdiv_nonneg

/-- KL divergence is non-negative (Gibbs' inequality) - **relaxed version**.

This version allows P to have zero probabilities (which contribute 0 to KL
by the convention `0 · log(0) = 0`), but requires Q to be positive on the support
of P (to avoid the `p_i > 0 ∧ q_i = 0` divergence-to-∞ case). -/
theorem klDivergence_nonneg' {n : ℕ} (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    0 ≤ klDivergence P Q hQ_pos := by
  -- Use atomDivergenceExt which handles w = 0
  have hdiv_nonneg : 0 ≤ ∑ i, atomDivergenceExt (P.p i) (Q.p i) := by
    apply sum_nonneg
    intro i _
    by_cases hPi : P.p i = 0
    · -- If P.p i = 0 then atomDivergenceExt 0 u = u, so nonneg follows from Q.nonneg.
      simpa [hPi] using Q.nonneg i
    · have hQi_pos : 0 < Q.p i := hQ_pos i hPi
      exact atomDivergenceExt_nonneg (P.p i) (Q.p i) (P.nonneg i) hQi_pos
  -- The (q - p) terms sum to 0 due to normalization
  have hcancel : ∑ i, (Q.p i - P.p i) = 0 := by
    rw [sum_sub_distrib, Q.sum_one, P.sum_one]; ring
  -- atomDivergenceExt equals atomDivergence for positive p, and u for p = 0
  -- In both cases, the sum structure is the same
  have hexpand : ∑ i, atomDivergenceExt (P.p i) (Q.p i) =
      (∑ i, (Q.p i - P.p i)) + ∑ i, P.p i * log (P.p i / Q.p i) := by
    have hrw : ∑ i, atomDivergenceExt (P.p i) (Q.p i) =
        ∑ i, ((Q.p i - P.p i) + P.p i * log (P.p i / Q.p i)) := by
      apply sum_congr rfl
      intro i _
      unfold atomDivergenceExt
      split_ifs with hp
      · -- Case P.p i = 0: contributes Q.p i = (Q.p i - 0) + 0 * log(...)
        simp [hp]
      · -- Case P.p i ≠ 0: standard formula
        ring
    rw [hrw, sum_add_distrib]
  rw [hexpand, hcancel, zero_add] at hdiv_nonneg
  simpa [klDivergence] using hdiv_nonneg

theorem klDivergenceTop_toReal_eq_of_support_pos {n : ℕ} (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    (klDivergenceTop P Q).toReal = klDivergence P Q hQ_pos := by
  classical
  have h0 : 0 ≤ klDivergence P Q hQ_pos := klDivergence_nonneg' (P := P) (Q := Q) hQ_pos
  rw [klDivergenceTop_eq_of_support_pos (P := P) (Q := Q) hQ_pos]
  simp [ENNReal.toReal_ofReal h0]

/-! ## Section 8.2: Shannon Entropy

K&S derive Shannon entropy as a special case of the variational potential.
The derivation proceeds by choosing parameters that give zero entropy for
certain outcomes.

**Key insight**: Shannon entropy is NOT just defined—it emerges from
the variational framework with specific parameter choices.
-/

/-- **Single-component entropy contribution** from the variational form.

This is `entropyForm A B C` specialized to the entropy case.
K&S set `A = 0`, `B = C` to get the entropy component `C·p·log(p)`. -/
noncomputable def entropyComponent (C : ℝ) (p : ℝ) : ℝ :=
  entropyForm 0 C C p

/-- The entropy component simplifies to `C·p·log(p)` for positive p.

From `entropyForm A B C p = A + B·p + C·(p·log(p) - p)`:
With `A = 0`, `B = C`:
  `= 0 + C·p + C·(p·log(p) - p) = C·p + C·p·log(p) - C·p = C·p·log(p)`
-/
theorem entropyComponent_eq (C : ℝ) (p : ℝ) (_hp : 0 < p) :
    entropyComponent C p = C * p * log p := by
  unfold entropyComponent entropyForm
  ring

/-- The entropy component at `p = 0` is zero.

Zero-probability events contribute nothing to Shannon entropy.
This follows from the `0 · log(0) = 0` convention. -/
@[simp]
theorem entropyComponent_zero (C : ℝ) : entropyComponent C 0 = 0 := by
  unfold entropyComponent
  simp [entropyForm_zero]

/-- **Shannon entropy** derived from the variational framework.

Setting `C = -1` in the entropy component sum gives Shannon entropy:
`S(p) = -Σ p_k · log(p_k)`

This is K&S Equation 58. The minus sign (C = -1) is conventional—it makes
entropy non-negative and gives a maximum (not minimum) for uniform distributions.
-/
noncomputable def shannonEntropy {n : ℕ} (P : ProbDist n) : ℝ :=
  ∑ i, entropyComponent (-1) (P.p i)

/-- Shannon entropy equals the conventional formula `-Σ p_k · log(p_k)`.

**Strict version**: Requires all probabilities to be strictly positive.
See `shannonEntropy_eq'` for a version allowing zero probabilities. -/
theorem shannonEntropy_eq {n : ℕ} (P : ProbDist n) (hP_pos : ∀ i, 0 < P.p i) :
    shannonEntropy P = -∑ i, P.p i * log (P.p i) := by
  unfold shannonEntropy
  have h : ∀ i, entropyComponent (-1) (P.p i) = -1 * P.p i * log (P.p i) := fun i =>
    entropyComponent_eq (-1) (P.p i) (hP_pos i)
  simp only [h]
  rw [← sum_neg_distrib]
  congr 1
  ext i
  ring

/-- Shannon entropy equals the conventional formula `-Σ p_k · log(p_k)` - **relaxed version**.

This version allows zero probabilities (which contribute 0 to entropy by the
convention `0 · log(0) = 0`). The equality holds because `entropyComponent (-1) 0 = 0`. -/
theorem shannonEntropy_eq' {n : ℕ} (P : ProbDist n) :
    shannonEntropy P = -∑ i, P.p i * log (P.p i) := by
  unfold shannonEntropy
  rw [← sum_neg_distrib]
  congr 1
  ext i
  -- Handle both cases: p = 0 and p > 0
  by_cases hp : P.p i = 0
  · -- Case p = 0: both sides are 0
    simp only [hp, entropyComponent_zero, neg_zero, zero_mul]
  · -- Case p > 0: use the standard formula
    have hp_pos : 0 < P.p i := (P.nonneg i).lt_of_ne' hp
    rw [entropyComponent_eq (-1) (P.p i) hp_pos]
    ring

/-- **Connection to variational form**: Shannon entropy is the sum of `entropyForm 0 (-1) (-1)`.

This explicitly shows the derivation from Appendix C. -/
theorem shannonEntropy_from_entropyForm {n : ℕ} (P : ProbDist n) :
    shannonEntropy P = ∑ i, entropyForm 0 (-1) (-1) (P.p i) := rfl

/-! ## Shannon's Three Properties

K&S claim these are "inevitable consequences of seeking a variational quantity."
-/

/-- The uniform distribution over `Fin n` states (for n > 0). -/
noncomputable def uniformDist (n : ℕ) (hn : 0 < n) : ProbDist n where
  p := fun _ => 1 / n
  nonneg := fun _ => by positivity
  sum_one := by
    simp only [sum_const, card_fin]
    rw [nsmul_eq_mul]
    field_simp

/-- Shannon entropy of the uniform distribution is `log(n)`. -/
theorem shannonEntropy_uniform (n : ℕ) (hn : 0 < n) :
    shannonEntropy (uniformDist n hn) = log n := by
  unfold shannonEntropy uniformDist
  have hp : 0 < (1 : ℝ) / n := by positivity
  simp only [entropyComponent_eq (-1) (1 / n) hp]
  simp only [sum_const, card_fin]
  rw [nsmul_eq_mul]
  rw [log_div one_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))]
  simp only [log_one, zero_sub]
  field_simp

/-! ## Entropy vs. KL Divergence to Uniform

This is the standard finite relationship between Shannon entropy and Kullback–Leibler divergence:

`D(P ‖ Uₙ) = log n - S(P)` and equivalently `S(P) = log n - D(P ‖ Uₙ)`.

It is the cleanest “Section 8” bridge between the (derived) entropy formula and the (derived)
divergence formula. -/

theorem klDivergence_uniform_eq_log_sub_shannonEntropy {n : ℕ} (P : ProbDist n) (hn : 0 < n) :
    klDivergence P (uniformDist n hn) (by
      intro i _
      have : 0 < (1 : ℝ) / n := by positivity
      simpa [uniformDist] using this) =
      log n - shannonEntropy P := by
  classical
  -- Rewrite the RHS in the usual `log n + Σ p_i log p_i` form.
  have hRHS : log n - shannonEntropy P = log n + ∑ i, P.p i * log (P.p i) := by
    rw [shannonEntropy_eq' (P := P)]
    ring
  -- Expand KL to the explicit uniform formula.
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hden : ((1 : ℝ) / n) ≠ 0 := div_ne_zero one_ne_zero hn0
  have hlog_unif : log ((1 : ℝ) / n) = -log n := by
    rw [log_div one_ne_zero hn0]
    simp [log_one]
  have hterm :
      ∀ i : Fin n,
        P.p i * log (P.p i / ((1 : ℝ) / n)) = P.p i * log (P.p i) - P.p i * log ((1 : ℝ) / n) := by
    intro i
    by_cases hPi : P.p i = 0
    · simp [hPi]
    · rw [log_div hPi hden]
      ring
  -- Now compute the finite sum.
  have hU :
      klDivergence P (uniformDist n hn) (by
        intro i _
        have : 0 < (1 : ℝ) / n := by positivity
        simpa [uniformDist] using this) =
      (∑ i : Fin n, P.p i * log (P.p i)) - ∑ i : Fin n, P.p i * log ((1 : ℝ) / n) := by
    -- Expand definition and distribute.
    simp only [klDivergence, uniformDist]
    have :
        (∑ i : Fin n, P.p i * log (P.p i / ((1 : ℝ) / n))) =
          ∑ i : Fin n, (P.p i * log (P.p i) - P.p i * log ((1 : ℝ) / n)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa using hterm i
    rw [this, Finset.sum_sub_distrib]
  rw [hU]
  -- Factor out the constant `log(1/n)` and use `∑ p_i = 1`.
  have hsum_const :
      (∑ i : Fin n, P.p i * log ((1 : ℝ) / n)) = (∑ i : Fin n, P.p i) * log ((1 : ℝ) / n) := by
    simpa using
      (Finset.sum_mul (s := (Finset.univ : Finset (Fin n))) (f := fun i : Fin n => P.p i)
        (log ((1 : ℝ) / n))).symm
  -- Finish: `-log(1/n) = log n`.
  have hneg_log_unif : -log ((1 : ℝ) / n) = log n := by
    rw [hlog_unif]
    ring
  -- Put everything together.
  rw [hsum_const, P.sum_one]
  simp only [one_mul]
  -- `Σ p_i log p_i - log(1/n) = log n + Σ p_i log p_i`
  linarith [hRHS, hneg_log_unif]

theorem klDivergenceTop_uniform_toReal {n : ℕ} (P : ProbDist n) (hn : 0 < n) :
    (klDivergenceTop P (uniformDist n hn)).toReal = log n - shannonEntropy P := by
  classical
  let U : ProbDist n := uniformDist n hn
  have hU_pos : ∀ i, P.p i ≠ 0 → 0 < U.p i := by
    intro i _
    have : 0 < (1 : ℝ) / n := by positivity
    simpa [U, uniformDist] using this
  -- Reduce `toReal` of the `ℝ≥0∞`-valued KL to the finite sum definition.
  have hto : (klDivergenceTop P U).toReal = klDivergence P U hU_pos :=
    klDivergenceTop_toReal_eq_of_support_pos (P := P) (Q := U) hU_pos
  -- Use the finite uniform identity.
  have hfin :
      klDivergence P U hU_pos = log n - shannonEntropy P := by
    simpa [U] using klDivergence_uniform_eq_log_sub_shannonEntropy (P := P) hn
  simpa [U] using (hto.trans hfin)

/-- **Property 2: Monotonicity**: For n < m, `S(uniform_n) < S(uniform_m)`. -/
theorem shannonEntropy_uniform_strictMono :
    StrictMono (fun n : {k : ℕ // 0 < k} => shannonEntropy (uniformDist n.1 n.2)) := by
  intro ⟨n, hn⟩ ⟨m, hm⟩ hnm
  simp only [Subtype.mk_lt_mk] at hnm
  simp only [shannonEntropy_uniform n hn, shannonEntropy_uniform m hm]
  exact log_lt_log (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hnm)

/-! ## Why These Parameters? (K&S's Reasoning)

K&S choose parameters to satisfy the requirement that entropy is zero when
one probability equals 1 (certain outcome = no uncertainty).

Given `H(p) = Σ (A + B·p_k + C·(p_k·log(p_k) - p_k))` and requiring `H = 0`
when `p_k = 1` for some k (and thus all other p_j = 0):

The only non-zero term is at k:
  `H = A + B·1 + C·(1·log(1) - 1) = A + B + C·(0 - 1) = A + B - C`

For this to equal 0: `A + B = C`, or equivalently `A = 0` when `B = C`.

The choice `C = -1` is conventional (makes entropy non-negative and maximal
for uniform distributions).
-/

/-- **Parameter derivation**: The condition `A + B = C` ensures zero entropy for certain outcomes.

This theorem shows WHY K&S choose `A = 0, B = C`. -/
theorem entropy_zero_condition (A B C : ℝ) :
    (entropyForm A B C 1 = 0) ↔ (A + B - C = 0) := by
  unfold entropyForm
  simp [log_one]
  constructor <;> intro h <;> linarith

/-- With `A = 0` and `B = C`, the entropy form gives `C·p·log(p)` (for positive p). -/
theorem entropyForm_shannon_params (C : ℝ) (p : ℝ) (_hp : 0 < p) :
    entropyForm 0 C C p = C * p * log p := by
  unfold entropyForm
  ring

/-- **Zero entropy for certain outcome**: When one probability is 1, entropy is 0.

This is what K&S use to determine the parameter choice `A = 0`, `B = C`. -/
theorem shannonEntropy_certain {n : ℕ} (P : ProbDist n) (k : Fin n)
    (hP_certain : P.p k = 1) :
    shannonEntropy P = 0 := by
  unfold shannonEntropy
  have hP_others : ∀ j, j ≠ k → P.p j = 0 :=
    ProbDist.eq_one_implies_others_zero P k hP_certain
  -- Split the sum
  have hsplit : ∑ i, entropyComponent (-1) (P.p i) =
      entropyComponent (-1) (P.p k) + ∑ i ∈ univ.erase k, entropyComponent (-1) (P.p i) := by
    rw [add_comm, sum_erase_add _ _ (mem_univ k)]
  rw [hsplit]
  -- The k-th term: entropyComponent (-1) 1 = -1 * 1 * log 1 = 0
  have hk_term : entropyComponent (-1) (P.p k) = 0 := by
    rw [hP_certain]
    unfold entropyComponent entropyForm
    simp [log_one]
  -- Other terms: entropyComponent (-1) 0 = 0
  have hrest : ∑ i ∈ univ.erase k, entropyComponent (-1) (P.p i) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hj_ne : j ≠ k := (mem_erase.mp hj).1
    rw [hP_others j hj_ne]
    unfold entropyComponent entropyForm
    simp
  rw [hk_term, hrest, add_zero]

/-! ## Extreme Cases -/

/-- **Information gained from certain knowledge**: When p_k = 1 (certain outcome),
`H(p | q) = -log(q_k)`.

This is the "surprise" or "information content" of learning that state k occurred. -/
theorem klDivergence_certain {n : ℕ} (P Q : ProbDist n) (k : Fin n)
    (hP_certain : P.p k = 1) (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    klDivergence P Q hQ_pos = -log (Q.p k) := by
  unfold klDivergence
  have hP_others : ∀ j, j ≠ k → P.p j = 0 :=
    ProbDist.eq_one_implies_others_zero P k hP_certain
  -- Only the k-th term contributes
  have hsplit : ∑ i, P.p i * log (P.p i / Q.p i) =
      P.p k * log (P.p k / Q.p k) + ∑ i ∈ univ.erase k, P.p i * log (P.p i / Q.p i) := by
    rw [add_comm, sum_erase_add _ _ (mem_univ k)]
  rw [hsplit]
  have hrest : ∑ i ∈ univ.erase k, P.p i * log (P.p i / Q.p i) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hj_ne : j ≠ k := (mem_erase.mp hj).1
    simp [hP_others j hj_ne]
  rw [hrest, add_zero, hP_certain]
  simp only [one_mul, one_div]
  rw [log_inv]

/-! ### Property 3: Grouping/Additivity

If a choice is broken down into subsidiary choices, entropy adds according
to probabilistic expectation. This is Shannon's grouping axiom.

For a binary split: `S(p₁, p₂, p₃) = S(p₁, p₂+p₃) + (p₂+p₃)·S(p₂/(p₂+p₃), p₃/(p₂+p₃))`
-/

/-- Binary entropy function `H₂(p) = -p·log(p) - (1-p)·log(1-p)`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -p * log p - (1 - p) * log (1 - p)

/-- The grouping property for binary subdivision (algebraic identity).

`S(p, q, r) = S(p, q+r) + (q+r)·H₂(q/(q+r))`

where `H₂` is binary entropy and `p + q + r = 1`.

**Proof sketch**: Expand H₂ and use log(x/y) = log(x) - log(y).
The (q+r)·log(q+r) terms cancel exactly.
-/
theorem shannonEntropy_grouping_binary {p q r : ℝ}
    (_hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (_hsum : p + q + r = 1) :
    let S3 := -(p * log p + q * log q + r * log r)
    let S2 := -(p * log p + (q + r) * log (q + r))
    let Ssub := (q + r) * binaryEntropy (q / (q + r))
    S3 = S2 + Ssub := by
  simp only [binaryEntropy]
  have hqr : 0 < q + r := by linarith
  have hqr_ne : q + r ≠ 0 := ne_of_gt hqr
  have h_one_minus : 1 - q / (q + r) = r / (q + r) := by field_simp; ring
  -- Rewrite using the complementary fraction
  rw [h_one_minus]
  -- Expand log(q/(q+r)) = log(q) - log(q+r), and similarly for r
  rw [log_div (ne_of_gt hq) hqr_ne, log_div (ne_of_gt hr) hqr_ne]
  -- Algebraic verification: the (q+r)*log(q+r) terms cancel
  -- S3 = -p*log(p) - q*log(q) - r*log(r)
  -- S2 + Ssub = -p*log(p) - (q+r)*log(q+r)
  --           + (q+r)*(-q/(q+r)*(log(q)-log(q+r)) - r/(q+r)*(log(r)-log(q+r)))
  --         = -p*log(p) - (q+r)*log(q+r) - q*log(q) + q*log(q+r) - r*log(r) + r*log(q+r)
  --         = -p*log(p) - q*log(q) - r*log(r) + (q+r-q-r)*log(q+r)
  --         = S3
  field_simp
  ring

/-! ### Grouping for ProbDist

The algebraic identity above can be applied to actual probability distributions.
Here we define the construction and prove the grouping property for `ProbDist`. -/

/-- Construct a 3-state probability distribution from three probabilities. -/
noncomputable def probDist3 (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : p + q + r = 1) : ProbDist 3 where
  p := ![p, q, r]
  nonneg := by
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, hp, hq, hr]
  sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hsum

/-- Construct a 2-state probability distribution from two probabilities. -/
noncomputable def probDist2 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1) : ProbDist 2 where
  p := ![p, q]
  nonneg := by
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, hp, hq]
  sum_one := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hsum

/-- **Property 3: Grouping for ProbDist**.

For a 3-state distribution P = (p, q, r), the entropy satisfies:
`S(P) = S(P') + (q+r)·S(P'')`

where:
- `P' = (p, q+r)` is the 2-state "grouped" distribution
- `P'' = (q/(q+r), r/(q+r))` is the conditional distribution within the group

This connects `shannonEntropy_grouping_binary` to actual `ProbDist` structures. -/
theorem shannonEntropy_grouping_probDist {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hsum : p + q + r = 1) :
    let P3 := probDist3 p q r (le_of_lt hp) (le_of_lt hq) (le_of_lt hr) hsum
    let hqr_pos : 0 ≤ q + r := by linarith
    let hqr_sum : p + (q + r) = 1 := by linarith
    let P2 := probDist2 p (q + r) (le_of_lt hp) hqr_pos hqr_sum
    let _hqr : 0 < q + r := by linarith
    let hq_div : 0 ≤ q / (q + r) := by positivity
    let hr_div : 0 ≤ r / (q + r) := by positivity
    let hcond_sum : q / (q + r) + r / (q + r) = 1 := by field_simp
    let Pcond := probDist2 (q / (q + r)) (r / (q + r)) hq_div hr_div hcond_sum
    shannonEntropy P3 = shannonEntropy P2 + (q + r) * shannonEntropy Pcond := by
  -- Introduce let bindings
  intro P3 hqr_pos hqr_sum P2 _hqr hq_div hr_div hcond_sum Pcond
  have hqr' : 0 < q + r := by linarith
  have hqr_ne : q + r ≠ 0 := ne_of_gt hqr'
  -- Expand P3 entropy
  have hS3 : shannonEntropy P3 = -p * log p - q * log q - r * log r := by
    simp only [shannonEntropy, P3, probDist3]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Manually handle the third element
    have h2 : (![p, q, r] : Fin 3 → ℝ) 2 = r := rfl
    rw [entropyComponent_eq (-1) p hp, entropyComponent_eq (-1) q hq]
    simp only [h2]
    rw [entropyComponent_eq (-1) r hr]
    ring
  -- Expand P2 entropy
  have hS2 : shannonEntropy P2 = -p * log p - (q + r) * log (q + r) := by
    simp only [shannonEntropy, P2, probDist2]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [entropyComponent_eq (-1) p hp, entropyComponent_eq (-1) (q + r) hqr']
    ring
  -- Expand Pcond entropy
  have hScond : shannonEntropy Pcond =
      -q / (q + r) * log (q / (q + r)) - r / (q + r) * log (r / (q + r)) := by
    simp only [shannonEntropy, Pcond, probDist2]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hq_div_pos : 0 < q / (q + r) := by positivity
    have hr_div_pos : 0 < r / (q + r) := by positivity
    rw [entropyComponent_eq (-1) (q / (q + r)) hq_div_pos,
        entropyComponent_eq (-1) (r / (q + r)) hr_div_pos]
    ring
  -- Now use the raw algebraic identity
  rw [hS3, hS2, hScond]
  rw [log_div (ne_of_gt hq) hqr_ne, log_div (ne_of_gt hr) hqr_ne]
  field_simp
  ring

/-! ## Property 1: Continuity

K&S claim that "S is a continuous function of its arguments" is an "inevitable
consequence of seeking a variational quantity."

We prove this by showing `shannonEntropy` is continuous when we equip `ProbDist n`
with the appropriate topology (induced from the product topology on `Fin n → ℝ`).
-/

/-- Shannon entropy is continuous as a function on the probability simplex.

More precisely, the map `P.p ↦ shannonEntropy P` is continuous when restricted
to the probability simplex `{p : Fin n → ℝ | ∀ i, 0 < p i ∧ ∑ i, p i = 1}`.

Note: We state this for the interior of the simplex (all p_i > 0) because
`x ↦ x * log x` is continuous on `(0, ∞)` but not at 0 (though it has a
continuous extension with value 0 at 0). -/
theorem shannonEntropy_continuous_on_interior (n : ℕ) :
    ContinuousOn (fun p : Fin n → ℝ => -∑ i, p i * log (p i))
        {p | ∀ i, 0 < p i} := by
  apply ContinuousOn.neg
  apply continuousOn_finset_sum
  intro i _
  apply ContinuousOn.mul
  · exact (continuous_apply i).continuousOn
  · apply ContinuousOn.comp continuousOn_log (continuous_apply i).continuousOn
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (hp i)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
