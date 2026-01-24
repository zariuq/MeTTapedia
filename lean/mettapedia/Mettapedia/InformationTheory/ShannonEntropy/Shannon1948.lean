import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Basic

/-!
# Shannon (1948): Entropy from the original axioms

This file sets up Shannon's original axiom system from:

* Claude E. Shannon, *A Mathematical Theory of Communication* (1948)
  `/home/zar/claude/literature/shannon_entropy.pdf`

and proves that the standard Shannon entropy `∑ negMulLog(pᵢ)` satisfies these axioms.

## Shannon's Original Axioms (5 total)

1. **Relabeling Invariance**: H is invariant under permutations (= Faddeev's symmetry)
2. **Continuity**: H(p₁,...,pₙ) is continuous in the pᵢ (full continuity)
3. **Monotonicity**: A(n) = H(1/n,...,1/n) is monotonically increasing in n
4. **Grouping**: H satisfies the chain rule / grouping property (= Faddeev's recursivity)
5. **Normalization**: A(2) = H(1/2, 1/2) = 1

## Comparison to Faddeev (1956)

Shannon's original system has **5** axioms; Faddeev's system has only **4**:

| Property | Shannon (1948) | Faddeev (1956) |
|----------|----------------|----------------|
| Relabeling/Symmetry | ASSUMES | ASSUMES |
| Full continuity | **ASSUMES** | DERIVES |
| Binary continuity | - | ASSUMES |
| Monotonicity | **ASSUMES** | **DERIVES** |
| Grouping/Recursivity | ASSUMES | ASSUMES |
| Normalization | ASSUMES | ASSUMES |
| **Total axioms** | **5** | **4** |

The key difference: Faddeev assumes only **binary** continuity and PROVES monotonicity
and full continuity. Shannon assumes **full** continuity and monotonicity outright.

See `Faddeev.lean` for the minimal system and `Interface.lean` for the unified view.

## Main Results

* `ShannonEntropy` - Structure encoding Shannon's 1948 axioms
* `shannonEntropy_satisfies` - Shannon entropy satisfies the axioms
* Uniqueness argument (Shannon's Appendix 2)
-/

namespace Mettapedia.InformationTheory

open scoped Topology

open Classical
open Finset Real
open Filter

/-! ## Probability distributions on finite types -/

namespace Prob

variable {α : Type*} [Fintype α]

theorem nonneg (p : Prob α) (a : α) : 0 ≤ p.1 a := p.2.1 a

theorem sum_eq_one (p : Prob α) : (∑ a : α, p.1 a) = 1 := p.2.2

/-- Relabel a distribution along an equivalence. -/
noncomputable def map {β : Type*} [Fintype β] (e : α ≃ β) (p : Prob α) : Prob β :=
  ⟨fun b => p.1 (e.symm b), by
    constructor
    · intro b; exact p.nonneg (e.symm b)
    ·
      -- `∑ b, p(e.symm b) = ∑ a, p(a) = 1`
      calc
        (∑ b : β, p.1 (e.symm b)) = ∑ a : α, p.1 a := by
          simpa using (e.symm.sum_comp fun a : α => p.1 a)
        _ = 1 := p.sum_eq_one⟩

@[simp] theorem map_apply {β : Type*} [Fintype β] (e : α ≃ β) (p : Prob α) (b : β) :
    (map e p).1 b = p.1 (e.symm b) := rfl

end Prob

/-! ## Shannon entropy on a finite type -/

/-- Shannon entropy on a finite type (natural-log base), as a finite sum of `negMulLog`. -/
noncomputable def shannonEntropyFin (α : Type*) [Fintype α] (p : Prob α) : ℝ :=
  ∑ a : α, negMulLog (p.1 a)

@[simp] theorem shannonEntropyFin_fin (n : ℕ) (p : ProbVec n) :
    shannonEntropyFin (Fin n) p = shannonEntropy p := rfl

/-! ## Shannon's grouping/composition operation -/

/-- Compose a base distribution `p` with conditional distributions `q a` (Shannon grouping).

This is the standard operadic "chain rule" composition: it builds a distribution on `Σ a, β a`
by `p(a) * q_a(b)`.
-/
noncomputable def comp
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    (p : Prob α) (q : ∀ a, Prob (β a)) : Prob (Sigma β) :=
  ⟨fun ab => p.1 ab.1 * (q ab.1).1 ab.2, by
    constructor
    · intro ab
      exact mul_nonneg (p.2.1 ab.1) ((q ab.1).2.1 ab.2)
    · -- Sum over a sigma type: ∑_{(a,b)} p(a) q_a(b) = ∑_a p(a) (∑_b q_a(b)) = ∑_a p(a) = 1.
      classical
      have hq : ∀ a : α, (∑ b : β a, (q a).1 b) = 1 := fun a => (q a).2.2
      calc
        (∑ ab : Sigma β, p.1 ab.1 * (q ab.1).1 ab.2)
            = ∑ a : α, ∑ b : β a, p.1 a * (q a).1 b := by
                simp [Fintype.sum_sigma]  -- `Sigma` is `Σ a, β a`
        _ = ∑ a : α, p.1 a * (∑ b : β a, (q a).1 b) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [Finset.mul_sum]
        _ = ∑ a : α, p.1 a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [hq a]
        _ = 1 := p.2.2⟩

/-! ## Shannon entropy satisfies the chain rule -/

theorem shannonEntropyFin_comp
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    (p : Prob α) (q : ∀ a, Prob (β a)) :
    shannonEntropyFin (Sigma β) (comp p q)
      = shannonEntropyFin α p + ∑ a : α, p.1 a * shannonEntropyFin (β a) (q a) := by
  classical
  unfold shannonEntropyFin comp
  -- Rewrite the sigma sum as an iterated sum over `a : α` then `b : β a`.
  have hsum :
      (∑ ab : Sigma β, negMulLog (p.1 ab.1 * (q ab.1).1 ab.2))
        = ∑ a : α, ∑ b : β a, negMulLog (p.1 a * (q a).1 b) := by
          simp [Fintype.sum_sigma]
  rw [hsum]
  have hqsum : ∀ a : α, (∑ b : β a, (q a).1 b) = 1 := fun a => (q a).2.2
  -- Expand `negMulLog` over products and separate the two contributions.
  calc
    (∑ a : α, ∑ b : β a, negMulLog (p.1 a * (q a).1 b))
        = ∑ a : α, ∑ b : β a,
            ((q a).1 b * negMulLog (p.1 a) + p.1 a * negMulLog ((q a).1 b)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          -- `negMulLog_mul` is symmetric up to commutativity.
          simp [negMulLog_mul, mul_comm]
    _ = ∑ a : α,
          ((∑ b : β a, (q a).1 b * negMulLog (p.1 a))
            + (∑ b : β a, p.1 a * negMulLog ((q a).1 b))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [Finset.sum_add_distrib]
    _ = ∑ a : α,
          (((∑ b : β a, (q a).1 b) * negMulLog (p.1 a))
            + (p.1 a * ∑ b : β a, negMulLog ((q a).1 b))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          -- Factor out the constant terms from each inner sum.
          simp [Finset.sum_mul, Finset.mul_sum, mul_comm]
    _ = (∑ a : α, negMulLog (p.1 a)) + ∑ a : α, p.1 a * (∑ b : β a, negMulLog ((q a).1 b)) := by
          -- Simplify using `∑_b q_a(b) = 1` and distribute `∑ a` across `+`.
          have :
              (∑ a : α,
                  ((∑ b : β a, (q a).1 b) * negMulLog (p.1 a)
                    + p.1 a * ∑ b : β a, negMulLog ((q a).1 b)))
                =
                (∑ a : α, negMulLog (p.1 a))
                  + ∑ a : α, p.1 a * (∑ b : β a, negMulLog ((q a).1 b)) := by
            -- Push the simplification pointwise.
            simp [hqsum, Finset.sum_add_distrib]
          simpa using this
    _ = shannonEntropyFin α p + ∑ a : α, p.1 a * shannonEntropyFin (β a) (q a) := by
          simp [shannonEntropyFin]

/-! ## Shannon 1948 axiom interface -/

/-- Shannon's original axiom system (1948).

We model Shannon's "grouping" axiom as the chain rule for the sigma-type composition `comp`.

Notes:
- Shannon also implicitly assumes invariance under relabeling; we make this explicit as `relabel`.
- Shannon does not fix a normalization constant; uniqueness is therefore (at best) "up to scale".
  Normalizations such as `H(1/2,1/2)=1` can be added separately when needed.
-/
structure Shannon1948Entropy where
  H : ∀ {α : Type} [Fintype α], Prob α → ℝ
  relabel :
    ∀ {α β : Type} [Fintype α] [Fintype β], ∀ e : α ≃ β, ∀ p : Prob α,
      H (α := β) (Prob.map e p) = H (α := α) p
  continuity : ∀ {α : Type} [Fintype α], Continuous (H (α := α))
  /-- Monotonicity for uniform distributions on `Fin n`. -/
  monotone_uniform :
    ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), m ≤ n →
      H (α := Fin m) (uniformDist m hm) ≤ H (α := Fin n) (uniformDist n hn)
  /-- Grouping / chain rule (Shannon's axiom (3)). -/
  grouping :
    ∀ {α : Type} [Fintype α] {β : α → Type} [∀ a, Fintype (β a)],
      ∀ (p : Prob α) (q : ∀ a, Prob (β a)),
        H (comp p q) = H p + ∑ a : α, p.1 a * H (q a)

/-! ## Shannon entropy satisfies Shannon's axioms -/

noncomputable def shannonEntropyFinNormalized (α : Type*) [Fintype α] (p : Prob α) : ℝ :=
  shannonEntropyFin α p / log 2

theorem shannonEntropyFinNormalized_relabel
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : Prob α) :
    shannonEntropyFinNormalized β (Prob.map e p) = shannonEntropyFinNormalized α p := by
  classical
  unfold shannonEntropyFinNormalized shannonEntropyFin
  -- change of variables in the finite sum
  have : (∑ b : β, negMulLog (p.1 (e.symm b))) = ∑ a : α, negMulLog (p.1 a) := by
    simpa using (e.symm.sum_comp fun a => negMulLog (p.1 a))
  simp [Prob.map, this]

theorem continuous_shannonEntropyFin {α : Type*} [Fintype α] :
    Continuous (fun p : Prob α => shannonEntropyFin α p) := by
  classical
  unfold shannonEntropyFin
  apply continuous_finset_sum
  intro a _
  -- `p ↦ p.val a` is continuous, and `negMulLog` is continuous.
  exact continuous_negMulLog.comp (continuous_apply a |>.comp continuous_subtype_val)

theorem shannonEntropyFinNormalized_monotone_uniform {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n) :
    shannonEntropyFinNormalized (Fin m) (uniformDist m hm)
      ≤ shannonEntropyFinNormalized (Fin n) (uniformDist n hn) := by
  unfold shannonEntropyFinNormalized
  -- Use `H(uniform n) = log n`.
  simp [shannonEntropyFin_fin, shannonEntropy_uniform]
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : log (m : ℝ) ≤ log (n : ℝ) :=
    log_le_log hm' (Nat.cast_le.mpr hmn)
  have hden : 0 < log 2 := log_pos one_lt_two
  exact div_le_div_of_nonneg_right hlog (le_of_lt hden)

theorem shannonEntropyFinNormalized_grouping
    {α : Type*} [Fintype α] {β : α → Type*} [∀ a, Fintype (β a)]
    (p : Prob α) (q : ∀ a, Prob (β a)) :
    shannonEntropyFinNormalized (Sigma β) (comp p q)
      =
      shannonEntropyFinNormalized α p + ∑ a : α, p.1 a * shannonEntropyFinNormalized (β a) (q a) := by
  classical
  unfold shannonEntropyFinNormalized
  have h := shannonEntropyFin_comp (p := p) (q := q)
  -- Divide Shannon's chain rule by `log 2`, distributing division across sums.
  have hsum_div :
      (∑ a : α, p.1 a * shannonEntropyFin (β a) (q a)) / log 2
        =
        ∑ a : α, p.1 a * (shannonEntropyFin (β a) (q a) / log 2) := by
      -- Rewrite division as multiplication by a constant and use distributivity.
      simp [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm]
  calc
    shannonEntropyFin (Sigma β) (comp p q) / log 2
        = (shannonEntropyFin α p + ∑ a : α, p.1 a * shannonEntropyFin (β a) (q a)) / log 2 := by
            simp [h]
    _ = shannonEntropyFin α p / log 2 + (∑ a : α, p.1 a * shannonEntropyFin (β a) (q a)) / log 2 := by
          simp [add_div]
    _ = shannonEntropyFin α p / log 2 + ∑ a : α, p.1 a * (shannonEntropyFin (β a) (q a) / log 2) := by
          simp [hsum_div]

/-- The normalized Shannon entropy is a model of Shannon's 1948 axiom system. -/
noncomputable def shannon1948Model : Shannon1948Entropy where
  H := fun {α} _ p => shannonEntropyFinNormalized α p
  relabel := by
    intro α β _ _ e p
    simpa using shannonEntropyFinNormalized_relabel (e := e) (p := p)
  continuity := by
    intro α _
    -- continuity of Shannon entropy, then scale by a constant
    simpa [shannonEntropyFinNormalized] using (continuous_shannonEntropyFin (α := α)).div_const (log 2)
  monotone_uniform := by
    intro m n hm hn hmn
    simpa using shannonEntropyFinNormalized_monotone_uniform (m := m) (n := n) hm hn hmn
  grouping := by
    intro α _ β _ p q
    simpa using shannonEntropyFinNormalized_grouping (p := p) (q := q)

set_option maxHeartbeats 1000000 in
/-- Shannon (1948) uniqueness: any model is a constant multiple of Shannon entropy. -/
theorem shannon1948_uniqueness (E : Shannon1948Entropy) :
    ∃ K : ℝ, ∀ {α : Type} [Fintype α] (p : Prob α),
      E.H (α := α) p = K * shannonEntropyFinNormalized α p := by
  classical
  -- Define the scale constant `K` by the value at the fair coin.
  let K : ℝ := E.H (α := Fin 2) (uniformDist 2 (by norm_num : 0 < 2))
  refine ⟨K, ?_⟩
  intro α _ p
  -- Reduce to `Fin n` via relabeling.
  classical
  let n : ℕ := Fintype.card α
  let e : α ≃ Fin n := Fintype.equivFin α
  have hn : 0 < n := by
    -- If `n = 0` then `α` is empty, contradicting `∑ p = 1`.
    by_contra hn0
    have hn0' : Fintype.card α = 0 := by
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      simpa [n] using this
    haveI : IsEmpty α := (Fintype.card_eq_zero_iff.mp hn0')
    have hsum0 : (∑ a : α, p.1 a) = (0 : ℝ) := by
      simp
    have : (0 : ℝ) = 1 := by
      simpa [hsum0] using (Prob.sum_eq_one (p := p))
    exact (zero_ne_one this)
  have h_relabel_H :
      E.H (α := α) p = E.H (α := Fin n) (Prob.map e p) := by
        simpa [n, e] using (E.relabel (α := α) (β := Fin n) e p).symm
  have h_relabel_S :
      shannonEntropyFinNormalized α p = shannonEntropyFinNormalized (Fin n) (Prob.map e p) := by
        simpa [n, e] using (shannonEntropyFinNormalized_relabel (e := e) (p := p)).symm
  -- It therefore suffices to prove the formula on `Fin n`.
  -- We now prove `E.H = K * shannonEntropyFinNormalized` on every `ProbVec n` by approximation
  -- by rational distributions (built from counting measures).
  have h_fin :
      ∀ (p' : Prob (Fin n)), E.H (α := Fin n) p' = K * shannonEntropyFinNormalized (Fin n) p' := by
    intro p'
    -- Abbreviate the uniform entropy `A(n) = H(uniform_n)` for `n > 0`.
    let A : ℕ → ℝ := fun k =>
      if hk : 0 < k then E.H (α := Fin k) (uniformDist k hk) else 0

    have A_mul :
        ∀ m n : ℕ, (hm : 0 < m) → (hn : 0 < n) →
          A (m * n) = A m + A n := by
      intro m n hm hn
      -- Apply the grouping axiom to the uniform distribution on `m` with constant conditionals `uniform_n`.
      let β : Fin m → Type := fun _ => Fin n
      let p₀ : Prob (Fin m) := uniformDist m hm
      let q₀ : ∀ a : Fin m, Prob (β a) := fun _ => uniformDist n hn
      have h_group := E.grouping (p := p₀) (q := q₀)
      -- The composed distribution is uniform on a set of size `m * n`.
      have h_card : Fintype.card (Sigma β) = m * n := by
        classical
        -- `card (Σ a, β a) = ∑ a, card (β a) = m * n`
        simp [β, Fintype.card_sigma, Finset.sum_const]
      let eσ : Sigma β ≃ Fin (m * n) :=
        (Fintype.equivFin (Sigma β)).trans (finCongr h_card)
      have h_comp_uniform :
          Prob.map eσ (comp p₀ q₀) = uniformDist (m * n) (Nat.mul_pos hm hn) := by
        apply Subtype.ext
        funext i
        -- Both sides are constant `1 / (m*n)`.
        simp [Prob.map, comp, uniformDist, p₀, q₀, β, eσ, mul_comm, div_eq_mul_inv]
      -- Rewrite the left side of grouping using relabel invariance to `Fin (m*n)`.
      have h_comp_H :
          E.H (α := Sigma β) (comp p₀ q₀) = A (m * n) := by
        -- `H(comp) = H(Prob.map eσ comp) = H(uniformDist (m*n))`.
        have := E.relabel (α := Sigma β) (β := Fin (m * n)) eσ (comp p₀ q₀)
        -- `this : H (Prob.map eσ (comp p₀ q₀)) = H (comp p₀ q₀)`
        -- Rewrite with `h_comp_uniform`.
        simp [h_comp_uniform] at this
        simpa [A, Nat.mul_pos hm hn] using this.symm
      -- Evaluate the sum on the right side of grouping: `∑ a, p(a) * H(q a) = H(uniform_n)`.
      have h_sum :
          (∑ a : Fin m, p₀.1 a * E.H (q₀ a)) = A n := by
        have hp_sum : (∑ a : Fin m, p₀.1 a) = 1 := (Prob.sum_eq_one p₀)
        -- `q₀ a` is constant, so we factor it out of the sum.
        have :
            (∑ a : Fin m, p₀.1 a * E.H (uniformDist n hn)) =
              (∑ a : Fin m, p₀.1 a) * E.H (uniformDist n hn) := by
          simpa using
            (Finset.sum_mul (s := (Finset.univ : Finset (Fin m))) (f := fun a => p₀.1 a)
              (a := E.H (uniformDist n hn))).symm
        -- Now use `∑ p₀ = 1`.
        simp [q₀, A, hn, hp_sum, this]
      -- Assemble.
      have : A (m * n) = A m + A n := by
        -- From grouping: `H(comp) = H(p₀) + ∑ a, p₀ a * H(q₀ a)`.
        -- Replace `H(comp)` and the sum by the uniform entropies.
        have hA_m : E.H p₀ = A m := by
          -- `p₀` is `uniformDist m hm`.
          simp [p₀, A, hm]
        have hA_n : E.H (uniformDist n hn) = A n := by simp [A, hn]
        calc
          A (m * n) = E.H (α := Sigma β) (comp p₀ q₀) := by
            simpa using h_comp_H.symm
          _ = E.H p₀ + ∑ a : Fin m, p₀.1 a * E.H (q₀ a) := h_group
          _ = A m + A n := by
            simp [hA_m, h_sum]
      exact this

    have A_one : A 1 = 0 := by
      have h := A_mul 1 1 (by norm_num : 0 < 1) (by norm_num : 0 < 1)
      -- `A 1 = A 1 + A 1`.
      linarith

    have A_pow_two :
        ∀ k : ℕ, A (2 ^ k) = (k : ℝ) * A 2 := by
      intro k
      induction k with
      | zero =>
        simp [A, A_one]
      | succ k ih =>
        have h_mul := A_mul (2 ^ k) 2 (by positivity : 0 < 2 ^ k) (by norm_num : 0 < 2)
        -- Rewrite `2^(k+1) = 2^k * 2` and use IH.
        have : A (2 ^ (k + 1)) = A (2 ^ k) + A 2 := by
          simpa [pow_succ] using h_mul
        -- Convert to the explicit linear form.
        simpa [ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using this

    have A_pow :
        ∀ k m : ℕ, (hk : 0 < k) → A (k ^ m) = (m : ℝ) * A k := by
      intro k m hk
      induction m with
      | zero =>
        -- `k^0 = 1` and `A 1 = 0`.
        simp [A_one]
      | succ m ih =>
        have h_mul := A_mul (k ^ m) k (by positivity : 0 < k ^ m) hk
        -- `A(k^(m+1)) = A(k^m) + A(k)`.
        have hstep : A (k ^ (m + 1)) = A (k ^ m) + A k := by
          simpa [pow_succ] using h_mul
        -- Substitute IH and rewrite.
        have : A (k ^ (m + 1)) = (m : ℝ) * A k + A k := by
          have hstep' := hstep
          rw [ih] at hstep'
          simpa using hstep'
        simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using this

    have A_ge_zero : 0 ≤ A 2 := by
      -- Monotonicity from `1 ≤ 2` and `A(1)=0`.
      have hmono :=
        E.monotone_uniform (m := 1) (n := 2) (by norm_num : 0 < 1) (by norm_num : 0 < 2)
          (by decide : 1 ≤ 2)
      have hmonoA : A 1 ≤ A 2 := by
        simpa [A, (by norm_num : 0 < 1), (by norm_num : 0 < 2)] using hmono
      -- `A 1 = 0` by `A_one`.
      simpa [A_one] using hmonoA

    have A_uniform_log :
        ∀ k : ℕ, (hk : 0 < k) →
          A k = K * (log k / log 2) := by
      intro k hk
      by_cases hk1 : k = 1
      · subst hk1
        simp [A, A_one, K]
      have hk2 : 2 ≤ k := by
        have : 1 < k := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) (Ne.symm hk1)
        exact Nat.succ_le_iff.mp this
      -- If `A(2)=0` then everything collapses to `0` by multiplicativity + monotonicity.
      by_cases hA2 : A 2 = 0
      · have hzero : A k = 0 := by
          -- Choose `j` with `k ≤ 2^j`; monotonicity gives `A k ≤ A(2^j)=0`, and `A(1)=0 ≤ A k`.
          have hk' : (1 : ℕ) ≤ k := Nat.succ_le_iff.mp hk
          let j : ℕ := k + 1
          have hj : k ≤ 2 ^ j := by
            have hlt : k < 2 ^ (k + 1) :=
              lt_trans (Nat.lt_succ_self k) (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
            simpa [j] using (Nat.le_of_lt hlt)
          have hmono1 : E.H (uniformDist 1 (by norm_num : 0 < 1)) ≤ E.H (uniformDist k hk) :=
            E.monotone_uniform (m := 1) (n := k) (by norm_num : 0 < 1) hk hk'
          have hmono2 : E.H (uniformDist k hk) ≤ E.H (uniformDist (2 ^ j) (by positivity : 0 < 2 ^ j)) :=
            E.monotone_uniform (m := k) (n := 2 ^ j) hk (by positivity : 0 < 2 ^ j) hj
          have hmono1A : A 1 ≤ A k := by
            simpa [A, (by norm_num : 0 < 1), hk] using hmono1
          have hmono2A : A k ≤ A (2 ^ j) := by
            simpa [A, hk, (by positivity : 0 < 2 ^ j)] using hmono2
          have hpow : A (2 ^ j) = 0 := by
            simp [A_pow_two, hA2]
          have hA_nonneg : 0 ≤ A k := by
            -- `A 1 = 0 ≤ A k`.
            simpa [A_one] using hmono1A
          have hA_le : A k ≤ 0 := le_trans hmono2A (by simp [hpow])
          exact le_antisymm hA_le hA_nonneg
        -- With `K = A 2`, the formula is `0 = 0`.
        have hK : K = 0 := by
          -- `A 2 = 0` and `2 > 0` means `K = H(uniform_2) = 0`.
          simpa [A, K, (by norm_num : 0 < 2)] using hA2
        simp [hzero, hK]
      -- Otherwise, compare `A(k)` to logs by Shannon's sandwich argument.
      have hA2_pos : 0 < A 2 := lt_of_le_of_ne' A_ge_zero hA2
      -- Show `A(k) / A(2) = log k / log 2` by an `ε`-argument using powers.
      let s : ℝ := A k / A 2
      let r : ℝ := log k / log 2
      have hs :
          ∀ m : ℕ, 0 < m →
            |s - r| ≤ 1 / (m : ℝ) := by
        intro m hm
        -- Pick `j` such that `2^j ≤ k^m < 2^(j+1)` (Archimedean property of powers).
        have hk_pow : 1 ≤ k ^ m := by
          exact Nat.one_le_pow _ _ hk
        obtain ⟨j, hj₁, hj₂⟩ :=
          exists_nat_pow_near (R := ℕ) (x := k ^ m) (y := 2) hk_pow (by decide : 1 < (2 : ℕ))
        have hj₂' : k ^ m ≤ 2 ^ (j + 1) := Nat.le_of_lt hj₂
        have hkpow_pos : 0 < k ^ m := by positivity
        have h2pow_pos : 0 < 2 ^ j := by positivity
        have h2pow_succ_pos : 0 < 2 ^ (j + 1) := by positivity
        -- Apply monotonicity: `A(2^j) ≤ A(k^m) ≤ A(2^(j+1))`.
        have hmono_lo :=
          E.monotone_uniform (m := 2 ^ j) (n := k ^ m) h2pow_pos hkpow_pos hj₁
        have hmono_hi :=
          E.monotone_uniform (m := k ^ m) (n := 2 ^ (j + 1)) hkpow_pos h2pow_succ_pos hj₂'
        have hmono_loA : A (2 ^ j) ≤ A (k ^ m) := by
          simpa [A, h2pow_pos, hkpow_pos] using hmono_lo
        have hmono_hiA : A (k ^ m) ≤ A (2 ^ (j + 1)) := by
          simpa [A, hkpow_pos, h2pow_succ_pos] using hmono_hi
        -- Rewrite in terms of `A(2)` and `A(k)`.
        have hpow2j :
            A (2 ^ j) = (j : ℝ) * A 2 := by
          simpa using A_pow_two j
        have hpow2j1 :
            A (2 ^ (j + 1)) = (j + 1 : ℝ) * A 2 := by
          simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using A_pow_two (j + 1)
        have hpowkm : A (k ^ m) = (m : ℝ) * A k := A_pow k m hk
        -- Convert the monotone inequalities to bounds on `s`.
        have hs_lo : (j : ℝ) / (m : ℝ) ≤ s := by
          have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          -- Start with: `A(2^j) ≤ A(k^m)`, rewritten as `j*A2 ≤ m*A(k)`.
          have h' : (j : ℝ) * A 2 ≤ (m : ℝ) * A k := by
            simpa [hpow2j, hpowkm] using hmono_loA
          -- Divide by `m*A2` (both positive) by rewriting the goal and `field_simp`.
          have : (j : ℝ) / (m : ℝ) ≤ A k / A 2 := by
            -- `field_simp` turns this into `j * A2 ≤ m * A(k)`.
            field_simp [hmR.ne', hA2_pos.ne'] 
            simpa [mul_assoc, mul_comm, mul_left_comm] using h'
          simpa [s] using this
        have hs_hi : s ≤ (j + 1 : ℝ) / (m : ℝ) := by
          have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          have h' : (m : ℝ) * A k ≤ (j + 1 : ℝ) * A 2 := by
            -- from `A(k^m) ≤ A(2^(j+1))`
            have : A (k ^ m) ≤ A (2 ^ (j + 1)) := hmono_hiA
            simpa [hpowkm, hpow2j1] using this
          have : A k / A 2 ≤ (j + 1 : ℝ) / (m : ℝ) := by
            -- `field_simp` turns this into `m * A(k) ≤ (j+1) * A2`.
            field_simp [hmR.ne', hA2_pos.ne']
            simpa [mul_assoc, mul_comm, mul_left_comm] using h'
          -- Rewrite to `s ≤ (j+1)/m`.
          simpa [s, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        -- The log ratio `r` is squeezed into the same interval `[j/m, (j+1)/m)`.
        have hr_lo : (j : ℝ) / (m : ℝ) ≤ r := by
          have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          have hj₁R : (2 : ℝ) ^ j ≤ (k : ℝ) ^ m := by
            exact_mod_cast hj₁
          -- Apply `log_le_log` and simplify.
          have hlog : log ((2 : ℝ) ^ j) ≤ log ((k : ℝ) ^ m) := by
            have hpos2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
            have hposk : (0 : ℝ) < (k : ℝ) ^ m := by
              have : (0 : ℝ) < k := Nat.cast_pos.mpr hk
              positivity
            exact log_le_log hpos2 hj₁R
          -- `log(2^j) = j*log 2`, `log(k^m)=m*log k`.
          have : (j : ℝ) / (m : ℝ) ≤ log k / log 2 := by
            have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
            have h' : (j : ℝ) * log 2 ≤ (m : ℝ) * log k := by
              simpa [Real.log_pow, mul_assoc, mul_comm, mul_left_comm] using hlog
            -- Divide by `m*log 2` using `field_simp` on the goal.
            have : (j : ℝ) / (m : ℝ) ≤ log k / log 2 := by
              field_simp [hmR.ne', hlog2.ne']
              -- goal is `j * log 2 ≤ m * log k`
              simpa [mul_assoc, mul_comm, mul_left_comm] using h'
            exact this
          simpa [r, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        have hr_hi : r < (j + 1 : ℝ) / (m : ℝ) := by
          have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          have hj₂R : (k : ℝ) ^ m < (2 : ℝ) ^ (j + 1) := by
            exact_mod_cast hj₂
          have hlog : log ((k : ℝ) ^ m) < log ((2 : ℝ) ^ (j + 1)) := by
            have hposk : (0 : ℝ) < (k : ℝ) ^ m := by
              have : (0 : ℝ) < k := Nat.cast_pos.mpr hk
              positivity
            have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
            exact log_lt_log hposk hj₂R
          have : log k / log 2 < (j + 1 : ℝ) / (m : ℝ) := by
            have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
            have h' : (m : ℝ) * log k < (j + 1 : ℝ) * log 2 := by
              simpa [Real.log_pow, mul_assoc, mul_comm, mul_left_comm] using hlog
            have : log k / log 2 < (j + 1 : ℝ) / (m : ℝ) := by
              field_simp [hmR.ne', hlog2.ne']
              -- goal is `m * log k < (j+1) * log 2`
              simpa [mul_assoc, mul_comm, mul_left_comm] using h'
            exact this
          simpa [r, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        -- Since `s` and `r` both lie in `[j/m, (j+1)/m]`, their distance is at most `1/m`.
        have : |s - r| ≤ 1 / (m : ℝ) := by
          have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          have hlen :
              ((j + 1 : ℝ) / (m : ℝ)) - ((j : ℝ) / (m : ℝ)) = 1 / (m : ℝ) := by
            field_simp [hmR.ne']
            ring
          -- `|s-r| ≤ 1/m` is equivalent to two inequalities `s-r ≤ 1/m` and `r-s ≤ 1/m`.
          refine abs_sub_le_iff.2 ?_
          constructor
          · -- `s - r ≤ 1/m`
            have hs' : s ≤ (j + 1 : ℝ) / (m : ℝ) := hs_hi
            have hr' : (j : ℝ) / (m : ℝ) ≤ r := hr_lo
            -- `s - r ≤ (hi - lo) = 1/m`.
            have : s - r ≤ ((j + 1 : ℝ) / (m : ℝ)) - ((j : ℝ) / (m : ℝ)) := by
              nlinarith
            simpa [hlen] using this
          · -- `r - s ≤ 1/m`
            have hr' : r ≤ (j + 1 : ℝ) / (m : ℝ) := le_of_lt hr_hi
            have hs' : (j : ℝ) / (m : ℝ) ≤ s := hs_lo
            have : r - s ≤ ((j + 1 : ℝ) / (m : ℝ)) - ((j : ℝ) / (m : ℝ)) := by
              nlinarith
            simpa [hlen] using this
        exact this

      have hs_eq : s = r := by
        -- If the distance is bounded by `1/m` for all `m`, it must be `0`.
        by_contra hne
        have hpos : 0 < |s - r| := abs_pos.mpr (sub_ne_zero.mpr hne)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hpos
        have hm' : 0 < m + 1 := Nat.succ_pos m
        have hbound := hs (m + 1) hm'
        have hlt : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < |s - r| := by
          simpa using hm
        exact not_lt_of_ge hbound hlt

      -- Convert back from `s = r`.
      have hAk : A k = A 2 * r := by
        have hs' : A k / A 2 = r := by
          simpa [s] using hs_eq
        have hA2_ne : A 2 ≠ 0 := ne_of_gt hA2_pos
        -- Multiply by `A 2` and simplify.
        have := congrArg (fun t => t * A 2) hs'
        -- `((A k / A 2) * A 2) = A k` and `r * A 2 = A 2 * r`.
        simpa [div_eq_mul_inv, hA2_ne, mul_assoc, mul_left_comm, mul_comm] using this
      -- Rewrite `A 2` as `K`.
      have hA2K : A 2 = K := by
        -- `A 2` is by definition `H(uniform_2)` since `0 < 2`.
        simp [A, K, (by norm_num : 0 < 2)]
      simpa [hA2K, r] using hAk

    -- Rational distributions from natural counts.
    have h_of_counts :
        ∀ {n : ℕ} (hn : 0 < n) (m : Fin n → ℕ) (hm : ∀ i, 0 < m i),
          let N : ℕ := ∑ i : Fin n, m i
          have hN : 0 < N := by
            classical
            let i0 : Fin n := ⟨0, hn⟩
            have hm0 : 0 < m i0 := hm i0
            have hle : m i0 ≤ ∑ i : Fin n, m i := by
              simpa using
                (Finset.single_le_sum (f := fun i : Fin n => m i) (fun i _ => Nat.zero_le (m i))
                  (Finset.mem_univ i0))
            simpa [N] using lt_of_lt_of_le hm0 hle
          let pNat : ProbVec n :=
            ⟨fun i => (m i : ℝ) / N, by
              constructor
              · intro i; positivity
              ·
                have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
                calc
                  (∑ i : Fin n, (m i : ℝ) / (N : ℝ))
                      = (∑ i : Fin n, (m i : ℝ)) / (N : ℝ) := by
                          simpa using
                            (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
                              (f := fun i : Fin n => (m i : ℝ)) (a := (N : ℝ))).symm
                  _ = (N : ℝ) / (N : ℝ) := by simp [N]
                  _ = 1 := by simp [hN']⟩
          E.H pNat = K * shannonEntropyFinNormalized (Fin n) pNat := by
      intro n hn m hm
      classical
      -- Use grouping on `pNat` with uniform conditionals of sizes `m i`.
      let N : ℕ := ∑ i : Fin n, m i
      have hN : 0 < N := by
        classical
        let i0 : Fin n := ⟨0, hn⟩
        have hm0 : 0 < m i0 := hm i0
        have hle : m i0 ≤ ∑ i : Fin n, m i := by
          simpa using
            (Finset.single_le_sum (f := fun i : Fin n => m i) (fun i _ => Nat.zero_le (m i))
              (Finset.mem_univ i0))
        simpa [N] using lt_of_lt_of_le hm0 hle
      let pNat : ProbVec n :=
        ⟨fun i => (m i : ℝ) / N, by
          constructor
          · intro i; positivity
          ·
            have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
            -- `∑ (m_i / N) = (∑ m_i) / N = N/N = 1`.
            calc
              (∑ i : Fin n, (m i : ℝ) / (N : ℝ))
                  = (∑ i : Fin n, (m i : ℝ)) / (N : ℝ) := by
                      simpa using
                        (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
                          (f := fun i : Fin n => (m i : ℝ)) (a := (N : ℝ))).symm
              _ = (N : ℝ) / (N : ℝ) := by simp [N]
              _ = 1 := by simp [hN']⟩
      let β : Fin n → Type := fun i => Fin (m i)
      let qNat : ∀ i : Fin n, Prob (β i) := fun i => uniformDist (m i) (hm i)
      have h_group := E.grouping (p := pNat) (q := qNat)
      have h_card : Fintype.card (Sigma β) = N := by
        classical
        simp [β, N, Fintype.card_sigma]
      let eσ : Sigma β ≃ Fin N := Fintype.equivFin (Sigma β) |>.trans (finCongr h_card)
      have h_comp_uniform :
          Prob.map eσ (comp pNat qNat) = uniformDist N hN := by
        apply Subtype.ext
        funext i
        -- Expand `Prob.map` and split the sigma coordinate.
        change (comp pNat qNat).1 (eσ.symm i) = (uniformDist N hN).1 i
        rcases eσ.symm i with ⟨a, b⟩
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        have hma0 : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
        -- Now it's a pure arithmetic identity: `(m a / N) * (1 / m a) = 1 / N`.
        simp [comp, pNat, qNat, uniformDist, N, div_eq_mul_inv, hma0, mul_comm, mul_left_comm]
      have h_comp_H : E.H (comp pNat qNat) = A N := by
        have h' :
            E.H (α := Sigma β) (comp pNat qNat) = E.H (α := Fin N) (uniformDist N hN) := by
          simpa [h_comp_uniform] using
            (E.relabel (α := Sigma β) (β := Fin N) eσ (comp pNat qNat)).symm
        simpa [A, hN] using h'
      have h_sum :
          (∑ i : Fin n, pNat.1 i * E.H (qNat i)) =
            ∑ i : Fin n, pNat.1 i * A (m i) := by
        -- Each `qNat i` is a uniform distribution, and `A (m i)` is its entropy by definition.
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [A, qNat, hm i]
      -- Rearrange grouping to solve for `E.H pNat`.
      have hE :
          E.H pNat = A N - ∑ i : Fin n, pNat.1 i * A (m i) := by
        -- `A N = H(comp) = H(pNat) + sum`, hence `H(pNat) = A N - sum`.
        have := congrArg (fun t => t - ∑ i : Fin n, pNat.1 i * E.H (qNat i)) h_group
        -- Simplify.
        -- Avoid `simp` heartbeats by rewriting `H(comp)` and the sum explicitly.
        have h1 :
            E.H pNat
              =
              E.H (comp pNat qNat) - ∑ i : Fin n, pNat.1 i * E.H (qNat i) := by
          linarith [h_group]
        -- Replace `H(comp)` by `A N` and the sum by `∑ pNat i * A (m i)`.
        simpa [h_comp_H, h_sum] using h1
      -- Now compute the same identity for Shannon entropy and compare.
      have hS :
          shannonEntropyFinNormalized (Fin n) pNat =
            shannonEntropyFinNormalized (Fin N) (uniformDist N hN)
              - ∑ i : Fin n, pNat.1 i * shannonEntropyFinNormalized (Fin (m i)) (uniformDist (m i) (hm i)) := by
        -- Use Shannon's chain rule for `comp pNat qNat`, noting this is `uniformDist N`.
        have h_chain :=
          shannonEntropyFinNormalized_grouping (p := pNat) (q := qNat)
        -- Rewrite the left side as `uniformDist N` via `h_comp_uniform`.
        have h_left :
            shannonEntropyFinNormalized (Sigma β) (comp pNat qNat)
              = shannonEntropyFinNormalized (Fin N) (uniformDist N hN) := by
          -- Use relabel invariance of Shannon entropy.
          have := shannonEntropyFinNormalized_relabel (e := eσ) (p := comp pNat qNat)
          -- `this` has the reverse orientation.
          simpa [h_comp_uniform] using this.symm
        -- Rearrange `H(comp) = H(pNat) + sum` as `H(pNat) = H(comp) - sum`.
        have h1 :
            shannonEntropyFinNormalized (Fin n) pNat =
              shannonEntropyFinNormalized (Sigma β) (comp pNat qNat)
                - ∑ i : Fin n, pNat.1 i
                    * shannonEntropyFinNormalized (Fin (m i)) (uniformDist (m i) (hm i)) := by
          linarith [h_chain]
        simpa [h_left] using h1
      -- Substitute the uniform formula `A(k)=K*log(k)/log 2` into `hE` and compare with `hS`.
      have hA_N : A N = K * shannonEntropyFinNormalized (Fin N) (uniformDist N hN) := by
        -- Both sides reduce to `K * log N / log 2`.
        have : A N = K * (log (N : ℝ) / log 2) := by
          simp [A_uniform_log (k := N) hN]
        -- `shannonEntropyFinNormalized` on a uniform distribution is `log N / log 2`.
        simp [this, shannonEntropyFinNormalized, shannonEntropyFin_fin, shannonEntropy_uniform,
          div_eq_mul_inv, mul_assoc, mul_comm]
      have hA_m :
          ∀ i : Fin n, A (m i) = K * shannonEntropyFinNormalized (Fin (m i)) (uniformDist (m i) (hm i)) := by
        intro i
        have hm' : 0 < m i := hm i
        have : A (m i) = K * (log (m i : ℝ) / log 2) := by
          simp [A_uniform_log (k := m i) hm']
        simp [this, shannonEntropyFinNormalized, shannonEntropyFin_fin, shannonEntropy_uniform,
          div_eq_mul_inv, mul_assoc, mul_comm]
      -- Finish by rewriting `hE` using `hA_N` and `hA_m`, then comparing to `hS`.
      -- This proves the target `E.H pNat = K * Shannon(pNat)`.
      calc
        E.H pNat
            = A N - ∑ i : Fin n, pNat.1 i * A (m i) := hE
        _ = K * (shannonEntropyFinNormalized (Fin N) (uniformDist N hN)
              - ∑ i : Fin n, pNat.1 i * shannonEntropyFinNormalized (Fin (m i)) (uniformDist (m i) (hm i))) := by
              -- Push `K` inside and use the uniform identities.
              simp [hA_N, hA_m, mul_sub, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
        _ = K * shannonEntropyFinNormalized (Fin n) pNat := by
              -- Use Shannon's chain-rule rearrangement.
              simp [hS]

    -- Approximate an arbitrary `p'` by rational distributions built from floor counts.
    -- Define `p_N` with counts `m_N(i) = ⌊p'(i) * (N+1)⌋ + 1`.
    let approxCounts : ℕ → (Fin n → ℕ) :=
      fun N i => ⌊p'.1 i * (N + 1 : ℝ)⌋₊ + 1
    have approxCounts_pos : ∀ N i, 0 < approxCounts N i := by
      intro N i
      simp [approxCounts]
    let approxDenom : ℕ → ℕ := fun N => ∑ i : Fin n, approxCounts N i
    have approxDenom_pos : ∀ N, 0 < approxDenom N := by
      intro N
      classical
      let i0 : Fin n := ⟨0, hn⟩
      have h0 : 0 < approxCounts N i0 := approxCounts_pos N i0
      have hle : approxCounts N i0 ≤ ∑ i : Fin n, approxCounts N i := by
        simpa using
          (Finset.single_le_sum (f := fun i : Fin n => approxCounts N i)
            (fun i _ => Nat.zero_le (approxCounts N i)) (Finset.mem_univ i0))
      have : 0 < ∑ i : Fin n, approxCounts N i := lt_of_lt_of_le h0 hle
      simpa [approxDenom] using this
    let approx : ℕ → ProbVec n :=
      fun N =>
        ⟨fun i => (approxCounts N i : ℝ) / approxDenom N, by
          constructor
          · intro i
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          ·
            have hD : (approxDenom N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (approxDenom_pos N))
            calc
              (∑ i : Fin n, (approxCounts N i : ℝ) / (approxDenom N : ℝ))
                  = (∑ i : Fin n, (approxCounts N i : ℝ)) / (approxDenom N : ℝ) := by
                      simpa using
                        (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
                          (f := fun i : Fin n => (approxCounts N i : ℝ))
                          (a := (approxDenom N : ℝ))).symm
              _ = (approxDenom N : ℝ) / (approxDenom N : ℝ) := by simp [approxDenom]
              _ = 1 := by simp [hD]⟩

    have h_approx_formula :
        ∀ N, E.H (approx N) = K * shannonEntropyFinNormalized (Fin n) (approx N) := by
      intro N
      -- Apply the natural-counts lemma to `approxCounts N`.
      simpa [approx, approxDenom, approxCounts] using
        h_of_counts (n := n) hn (m := approxCounts N) (hm := approxCounts_pos N)

    have h_approx_tendsto : Tendsto approx atTop (𝓝 p') := by
      -- Convergence is checked in the ambient `Fin n → ℝ`.
      have h_tendsto_coe :
          Tendsto (fun N i => (approx N).1 i) atTop (𝓝 fun i => p'.1 i) := by
        -- Componentwise convergence using `tendsto_nat_floor_mul_div_atTop` on each coordinate.
        -- We use the normalization trick: divide numerator and denominator by `(N+1)`.
        refine tendsto_pi_nhds.2 ?_
        intro i
        have hp0 : 0 ≤ p'.1 i := (ProbVec.nonneg (p := p') i)
        have h_num :
            Tendsto (fun N : ℕ => ((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1) / (N + 1 : ℝ))
              atTop (𝓝 (p'.1 i)) := by
          -- `(floor(a*(N+1)))/(N+1) → a`, and `1/(N+1) → 0`.
          have hfloor :
              Tendsto (fun N : ℕ => (⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ))
                atTop (𝓝 (p'.1 i)) := by
            -- Compose the real-variable limit with `N ↦ (N+1 : ℝ)`.
            have hreal :=
              (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := p'.1 i) hp0)
            -- `N ↦ (N+1 : ℝ)` tends to `atTop` (in `ℝ`).
            have hcast : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
              -- `((N+1 : ℕ) : ℝ)` tends to `atTop`, and this equals `(N : ℝ) + 1`.
              have h :=
                (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
              have hfun :
                  (Nat.cast ∘ fun a : ℕ => a + 1) = (fun N : ℕ => (↑N : ℝ) + 1) := by
                funext N
                simp [Function.comp, Nat.cast_add, Nat.cast_one]
              simpa [hfun] using h
            exact hreal.comp hcast
          have hone :
              Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
            simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          -- Combine: `(floor + 1)/(N+1) = floor/(N+1) + 1/(N+1)`.
          have : Tendsto (fun N : ℕ =>
              (⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ) + (1 : ℝ) / (N + 1 : ℝ))
              atTop (𝓝 (p'.1 i + 0)) := (hfloor.add hone)
          simpa [add_div, add_assoc, add_comm, add_left_comm] using this
        have h_den :
            Tendsto (fun N : ℕ => (approxDenom N : ℝ) / (N + 1 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
          -- Denominator/(N+1) tends to `∑ p_i = 1`.
          have hsum :
              Tendsto (fun N : ℕ => (∑ j : Fin n, (⌊p'.1 j * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ)))
                atTop (𝓝 (∑ j : Fin n, p'.1 j)) := by
            -- Rewrite the `Fintype` sum as a `Finset.univ` sum and apply `tendsto_finset_sum`.
            have hsum' :
                Tendsto
                    (fun N : ℕ =>
                      Finset.sum (Finset.univ : Finset (Fin n)) fun j =>
                        (⌊p'.1 j * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ))
                    atTop
                    (𝓝 (Finset.sum (Finset.univ : Finset (Fin n)) fun j => p'.1 j)) := by
              refine tendsto_finset_sum _ ?_
              intro j _
              have hp0j : 0 ≤ p'.1 j := (ProbVec.nonneg (p := p') j)
              have hreal :=
                (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := p'.1 j) hp0j)
              have hcast : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
                have h :=
                  (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
                have hfun :
                    (Nat.cast ∘ fun a : ℕ => a + 1) = (fun N : ℕ => (↑N : ℝ) + 1) := by
                  funext N
                  simp [Function.comp, Nat.cast_add, Nat.cast_one]
                simpa [hfun] using h
              exact hreal.comp hcast
            simpa using hsum'
          have honeN : Tendsto (fun N : ℕ => (n : ℝ) / (N + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
            -- `n/(N+1) → 0`.
            have h :=
              (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (C := (n : ℝ))).comp
                (tendsto_add_atTop_nat 1)
            have hfun :
                (fun n_1 : ℕ => (n : ℝ) / (n_1 : ℝ)) ∘ (fun a : ℕ => a + 1)
                  =
                (fun N : ℕ => (n : ℝ) / (N + 1 : ℝ)) := by
              funext N
              simp [Function.comp, Nat.cast_add, Nat.cast_one]
            simpa [hfun] using h
          -- `(approxDenom N)/(N+1) = (∑ floor/(N+1)) + n/(N+1)`.
          have hsum1 : (∑ j : Fin n, p'.1 j) = 1 := ProbVec.sum_eq_one p'
          have :
              Tendsto (fun N : ℕ =>
                  (∑ j : Fin n, (⌊p'.1 j * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ))
                    + (n : ℝ) / (N + 1 : ℝ))
                atTop (𝓝 (1 + 0)) := by
            simpa [hsum1] using hsum.add honeN
          -- Rewrite the left side to `(approxDenom N)/(N+1)`.
          -- `approxDenom = ∑ (floor + 1)`.
          have hrew :
              (fun N : ℕ =>
                (approxDenom N : ℝ) / (N + 1 : ℝ))
                =
              (fun N : ℕ =>
                (∑ j : Fin n, (⌊p'.1 j * (N + 1 : ℝ)⌋₊ : ℝ) / (N + 1 : ℝ))
                  + (n : ℝ) / (N + 1 : ℝ)) := by
            funext N
            have hD : (N + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
            -- Expand `approxDenom` and distribute division.
            simp [approxDenom, approxCounts, Finset.sum_add_distrib, add_div, Finset.sum_div, add_comm]
          -- Combine and simplify.
          simpa [hrew] using this
        -- Now `(approx N).1 i = ((approxCounts N i)/(N+1)) / ((approxDenom N)/(N+1))`.
        have hfrac :
            Tendsto (fun N : ℕ => (approx N).1 i) atTop (𝓝 (p'.1 i)) := by
          -- Rewrite by dividing numerator and denominator by `(N+1)`.
          have hden' :
              Tendsto (fun N : ℕ => ((approxDenom N : ℝ) / (N + 1 : ℝ))) atTop (𝓝 (1 : ℝ)) :=
            h_den
          have hdiv :=
            (h_num.div hden' (by simp : (1 : ℝ) ≠ 0))
          have hdiv' :
              Tendsto
                  (fun N : ℕ =>
                    (((((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1) / (N + 1 : ℝ))
                        / ((approxDenom N : ℝ) / (N + 1 : ℝ))))) atTop (𝓝 (p'.1 i)) := by
            simpa [div_one] using hdiv
          have hfun :
              (fun N : ℕ =>
                  (((((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1) / (N + 1 : ℝ))
                      / ((approxDenom N : ℝ) / (N + 1 : ℝ)))))
                =
              (fun N : ℕ =>
                  (((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1) / (approxDenom N : ℝ))) := by
            funext N
            have hD : (N + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
            simpa using
              (div_div_div_cancel_right₀ (G₀ := ℝ) hD
                (((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1)) (approxDenom N : ℝ))
          have hfinal :
              Tendsto (fun N : ℕ =>
                  (((⌊p'.1 i * (N + 1 : ℝ)⌋₊ : ℝ) + 1) / (approxDenom N : ℝ)))
                atTop (𝓝 (p'.1 i)) := by
            simpa [hfun] using hdiv'
          -- Convert the numerator to `approxCounts` and the quotient to `(approx N).1 i`.
          simpa [approx, approxCounts] using hfinal
        exact hfrac
      -- Lift convergence from the ambient space to the subtype.
      exact (tendsto_subtype_rng (f := approx) (x := p')).2 h_tendsto_coe

    -- Finish by continuity: take limits along `approx N`.
    have h_lim_H :
        Tendsto (fun N => E.H (approx N)) atTop (𝓝 (E.H p')) := by
      exact (E.continuity (α := Fin n)).tendsto p' |>.comp h_approx_tendsto
    have h_lim_S :
        Tendsto (fun N => shannonEntropyFinNormalized (Fin n) (approx N))
          atTop (𝓝 (shannonEntropyFinNormalized (Fin n) p')) := by
      have hcontS : Continuous (fun p : Prob (Fin n) => shannonEntropyFinNormalized (Fin n) p) := by
        -- `shannonEntropyFin` is continuous, and scaling preserves continuity.
        simpa [shannonEntropyFinNormalized] using (continuous_shannonEntropyFin (α := Fin n)).div_const (log 2)
      exact hcontS.tendsto p' |>.comp h_approx_tendsto
    -- Use `h_approx_formula` pointwise, then pass to the limit.
    have h_lim_eq :
        Tendsto (fun N => E.H (approx N) - K * shannonEntropyFinNormalized (Fin n) (approx N))
          atTop (𝓝 (E.H p' - K * shannonEntropyFinNormalized (Fin n) p')) := by
      exact (h_lim_H.sub (tendsto_const_nhds.mul h_lim_S))
    have h_zero :
        Tendsto (fun N => E.H (approx N) - K * shannonEntropyFinNormalized (Fin n) (approx N))
          atTop (𝓝 (0 : ℝ)) := by
      -- The sequence is constantly `0` by `h_approx_formula`.
      have : (fun N => E.H (approx N) - K * shannonEntropyFinNormalized (Fin n) (approx N)) = fun _ => 0 := by
        funext N
        simp [h_approx_formula N]
      -- Rewrite to a constant function, then apply `tendsto_const_nhds`.
      rw [this]
      exact tendsto_const_nhds
    have : E.H p' - K * shannonEntropyFinNormalized (Fin n) p' = 0 := by
      have := tendsto_nhds_unique h_lim_eq h_zero
      simpa using this
    linarith

  -- Combine reductions.
  calc
    E.H (α := α) p = E.H (α := Fin n) (Prob.map e p) := h_relabel_H
    _ = K * shannonEntropyFinNormalized (Fin n) (Prob.map e p) := h_fin (Prob.map e p)
    _ = K * shannonEntropyFinNormalized α p := by simp [h_relabel_S]

end Mettapedia.InformationTheory
