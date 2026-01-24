import Mettapedia.InformationTheory.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.Field

/-!
# Properties of Shannon Entropy

This file proves fundamental properties of Shannon entropy:
- Non-negativity: H(p) ≥ 0
- Upper bound: H(p) ≤ log n (achieved uniquely at uniform)
- Zero characterization: H(p) = 0 iff p is a point mass
- Continuity
- Symmetry (permutation invariance)

## Main Results

* `shannonEntropy_nonneg` - Shannon entropy is non-negative
* `shannonEntropy_le_log_card` - H(p) ≤ log n
* `shannonEntropy_uniform` - H(uniform) = log n
* `continuous_shannonEntropy` - Shannon entropy is continuous
* `shannonEntropy_permute` - H is invariant under permutations

## References

* Shannon, C.E. "A Mathematical Theory of Communication" (1948)
-/

namespace Mettapedia.InformationTheory

open Finset Real

/-! ## Base-2 Normalization -/

/-- Shannon entropy with base-2 normalization.

This is `shannonEntropy` scaled so that `H(1/2, 1/2) = 1`. -/
noncomputable def shannonEntropyNormalized {n : ℕ} (p : ProbVec n) : ℝ :=
  shannonEntropy p / log 2

/-! ## Recursivity / Grouping -/

/-- Key lemma: the weighted binary entropy identity.

For `s = a + b > 0`, we have
`(a + b) * H(a/s, b/s) = negMulLog(a) + negMulLog(b) - negMulLog(s)`
where `H` is Shannon entropy. -/
theorem weighted_binary_entropy_identity (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < a + b) :
    (a + b) * shannonEntropy (normalizeBinary a b ha hb hs) =
      negMulLog a + negMulLog b - negMulLog (a + b) := by
  let s := a + b
  unfold shannonEntropy normalizeBinary
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hs ⊢
    simp only [zero_div, negMulLog_zero, div_self (ne_of_gt hs), negMulLog_one, add_zero, mul_zero]
    ring
  by_cases hb0 : b = 0
  · subst hb0
    simp only [add_zero] at hs ⊢
    simp only [zero_div, negMulLog_zero, div_self (ne_of_gt hs), negMulLog_one, add_zero, mul_zero]
    ring
  have hs_ne : s ≠ 0 := ne_of_gt hs
  simp only [negMulLog]
  rw [log_div ha0 hs_ne, log_div hb0 hs_ne]
  field_simp
  ring

/-- Shannon entropy satisfies the grouping/recursivity axiom. -/
theorem shannonEntropy_recursivity {n : ℕ} (p : ProbVec (n + 2)) (h : 0 < p.1 0 + p.1 1) :
    shannonEntropy p = shannonEntropy (groupFirstTwo p h) +
      (p.1 0 + p.1 1) * shannonEntropy (normalizeBinary (p.1 0) (p.1 1)
        (p.nonneg 0) (p.nonneg 1) h) := by
  -- Rewrite the weighted binary term into `negMulLog` pieces.
  rw [weighted_binary_entropy_identity (a := p.1 0) (b := p.1 1)
    (ha := p.nonneg 0) (hb := p.nonneg 1) (hs := h)]
  -- Expand `H(p)` into the first two terms plus the tail sum.
  have hp :
      shannonEntropy p =
        negMulLog (p.1 0) + (negMulLog (p.1 1) + ∑ i : Fin n, negMulLog (p.1 i.succ.succ)) := by
    unfold shannonEntropy
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp
  -- Expand `H(groupFirstTwo p)` similarly.
  have hgroup :
      shannonEntropy (groupFirstTwo p h) =
        negMulLog (p.1 0 + p.1 1) + ∑ i : Fin n, negMulLog (p.1 i.succ.succ) := by
    unfold shannonEntropy groupFirstTwo
    rw [Fin.sum_univ_succ]
    have htail :
        (∑ x : Fin n,
            negMulLog
               (if h0 : (Fin.succ x).1 = 0 then p.1 0 + p.1 1
                else p.1 ⟨(Fin.succ x).1 + 1, by
                 exact Nat.succ_lt_succ (Fin.succ x).isLt⟩))
          =
        ∑ i : Fin n, negMulLog (p.1 i.succ.succ) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp
      rfl
    -- Head term is `p₀+p₁`, then use `htail` and reassociate.
    rw [htail]
    simp
  -- Reduce to ring arithmetic.
  rw [hp, hgroup]
  ring

/-! ## Non-negativity -/

/-- Shannon entropy is non-negative.
    This follows from `negMulLog x ≥ 0` for x ∈ [0,1]. -/
theorem shannonEntropy_nonneg {n : ℕ} (p : ProbVec n) : 0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  apply Finset.sum_nonneg
  intro i _
  exact negMulLog_nonneg (p.nonneg i) (p.le_one i)

/-! ## Symmetry (Permutation Invariance) -/

/-- Shannon entropy is invariant under permutations of the distribution.
    This is Faddeev's axiom F2 (symmetry). -/
theorem shannonEntropy_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbVec n) :
    shannonEntropy (permute σ p) = shannonEntropy p := by
  unfold shannonEntropy
  simp only [permute_apply]
  -- ∑ i, negMulLog (p.1 (σ⁻¹ i)) = ∑ j, negMulLog (p.1 j) via change of variables
  exact Equiv.sum_comp σ⁻¹ (fun i => negMulLog (p.1 i))

/-! ## Uniform Distribution -/

/-- The entropy of the uniform distribution is log n.
    This is the maximum entropy for distributions on n outcomes. -/
theorem shannonEntropy_uniform (n : ℕ) (hn : 0 < n) :
    shannonEntropy (uniformDist n hn) = log n := by
  unfold shannonEntropy
  simp only [uniformDist_apply]
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul, negMulLog]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  rw [one_div, log_inv]
  field_simp

/-! ## Upper Bound -/

/-- Shannon entropy is bounded above by log n.
    The maximum is achieved at the uniform distribution.
    Proof uses Jensen's inequality for the concave function negMulLog. -/
theorem shannonEntropy_le_log_card {n : ℕ} (hn : 0 < n) (p : ProbVec n) :
    shannonEntropy p ≤ log n := by
  -- We show H(p) ≤ H(uniform) = log n
  -- By Jensen's inequality: (1/n) ∑ᵢ f(pᵢ) ≤ f((1/n) ∑ᵢ pᵢ) = f(1/n)
  -- which gives ∑ᵢ f(pᵢ) ≤ n * f(1/n) = log n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Uniform weights: wᵢ = 1/n
  have hw_sum : ∑ _i : Fin n, (1 / n : ℝ) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hw_nonneg : ∀ i : Fin n, 0 ≤ (1 / n : ℝ) := fun _ => by positivity
  -- All probabilities are non-negative
  have hp_mem : ∀ i : Fin n, p.1 i ∈ Set.Ici (0 : ℝ) := fun i => p.nonneg i
  -- Sum of probabilities weighted by 1/n is 1/n (since ∑ pᵢ = 1)
  have hsum_p : ∑ i : Fin n, (1 / n : ℝ) * p.1 i = 1 / n := by
    rw [← Finset.mul_sum, p.sum_eq_one, mul_one]
  -- Jensen's inequality: ∑ i, (1/n) * negMulLog(p.1 i) ≤ negMulLog(∑ i, (1/n) * p.1 i)
  have jensen := concaveOn_negMulLog.le_map_sum
    (fun i _ => hw_nonneg i) hw_sum (fun i _ => hp_mem i)
  simp only [smul_eq_mul] at jensen hsum_p
  rw [hsum_p] at jensen
  -- jensen: ∑ i, (1/n) * negMulLog(p.1 i) ≤ negMulLog(1/n)
  -- Factor out: (1/n) * ∑ i, negMulLog(p.1 i) ≤ negMulLog(1/n)
  rw [← Finset.mul_sum] at jensen
  -- Multiply by n: ∑ᵢ negMulLog(pᵢ) ≤ n * negMulLog(1/n)
  have hmul := mul_le_mul_of_nonneg_left jensen (le_of_lt hn_pos)
  rw [← mul_assoc] at hmul
  simp only [one_div, mul_inv_cancel₀ hn_ne, one_mul] at hmul
  -- hmul: ∑ i, negMulLog(p.1 i) ≤ n * negMulLog(n⁻¹)
  -- Now show n * negMulLog(n⁻¹) = log n
  have h_uniform_entropy : (n : ℝ) * negMulLog ((n : ℝ)⁻¹) = log n := by
    simp only [negMulLog, log_inv]
    field_simp
  unfold shannonEntropy
  calc ∑ i, negMulLog (p.1 i) ≤ n * negMulLog ((n : ℝ)⁻¹) := hmul
    _ = log n := h_uniform_entropy

/-! ## Binary Entropy -/

/-- Shannon entropy of the fair coin is log 2. -/
theorem shannonEntropy_binaryUniform :
    shannonEntropy binaryUniform = log 2 := by
  unfold shannonEntropy
  simp only [Fin.sum_univ_two]
  rw [binaryUniform_apply_zero, binaryUniform_apply_one]
  simp only [negMulLog, one_div, log_inv]
  ring

theorem shannonEntropyNormalized_binaryUniform :
    shannonEntropyNormalized binaryUniform = 1 := by
  unfold shannonEntropyNormalized
  rw [shannonEntropy_binaryUniform]
  field_simp

/-! ## Point Mass -/

/-- The entropy of a point mass is zero. -/
theorem shannonEntropy_pointMass {n : ℕ} (i : Fin n) :
    shannonEntropy (pointMass i) = 0 := by
  unfold shannonEntropy
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = i
  · simp only [pointMass, hj, ↓reduceIte, negMulLog_one]
  · simp only [pointMass, hj, ↓reduceIte, negMulLog_zero]

/-- Entropy is zero implies some component is 1.
    (Direction: H = 0 → point mass) -/
theorem exists_eq_one_of_shannonEntropy_eq_zero {n : ℕ} (_hn : 0 < n) (p : ProbVec n)
    (h : shannonEntropy p = 0) : ∃ i, p.1 i = 1 := by
  -- If H(p) = 0 and each summand is nonneg, each summand is 0
  unfold shannonEntropy at h
  have hall : ∀ i ∈ univ, negMulLog (p.1 i) = 0 := by
    apply Finset.sum_eq_zero_iff_of_nonneg (fun i _ => negMulLog_nonneg (p.nonneg i) (p.le_one i)) |>.mp h
  -- negMulLog x = 0 iff x = 0 or x = 1 for x ∈ [0,1]
  have hcases : ∀ i, p.1 i = 0 ∨ p.1 i = 1 := by
    intro i
    have : negMulLog (p.1 i) = 0 := hall i (mem_univ i)
    have hmem := p.mem_Icc i
    rcases (Set.mem_Icc.mp hmem) with ⟨h0, h1⟩
    -- negMulLog x = 0 ↔ x = 0 ∨ x = 1 for x ∈ [0,1]
    by_cases hzero : p.1 i = 0
    · left; exact hzero
    · right
      have hpos : 0 < p.1 i := lt_of_le_of_ne h0 (Ne.symm hzero)
      have : -p.1 i * log (p.1 i) = 0 := this
      have hlog : log (p.1 i) = 0 := by
        have := mul_eq_zero.mp (neg_eq_zero.mp (by linarith : -(p.1 i * log (p.1 i)) = 0))
        rcases this with hp | hlog
        · exact absurd hp (ne_of_gt hpos)
        · exact hlog
      exact exp_log hpos ▸ hlog ▸ exp_zero
  -- Since sum = 1 and each is 0 or 1, exactly one is 1
  have hsum := p.sum_eq_one
  by_contra h_no_one
  push_neg at h_no_one
  have hall_zero : ∀ i, p.1 i = 0 := fun i => (hcases i).resolve_right (h_no_one i)
  simp only [hall_zero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

/-- If some component is 1, entropy is zero.
    (Direction: point mass → H = 0) -/
theorem shannonEntropy_eq_zero_of_exists_eq_one {n : ℕ} (p : ProbVec n)
    (h : ∃ i, p.1 i = 1) : shannonEntropy p = 0 := by
  obtain ⟨i, hi⟩ := h
  unfold shannonEntropy
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = i
  · simp only [hj, hi, negMulLog_one]
  · -- If p.1 i = 1 and sum = 1, then p.1 j = 0 for j ≠ i
    have hj_zero : p.1 j = 0 := by
      have hsum := p.sum_eq_one
      have hle : ∑ k ∈ univ.erase i, p.1 k = 0 := by
        have hdecomp : (∑ k, p.1 k) = p.1 i + ∑ k ∈ univ.erase i, p.1 k := by
          rw [← Finset.add_sum_erase univ (fun k => p.1 k) (mem_univ i)]
        rw [hsum, hi] at hdecomp
        linarith
      have hmem : j ∈ univ.erase i := by simp [hj]
      exact Finset.sum_eq_zero_iff_of_nonneg (fun k _ => p.nonneg k) |>.mp hle j hmem
    simp only [hj_zero, negMulLog_zero]

/-- Entropy is zero iff the distribution is a point mass. -/
theorem shannonEntropy_eq_zero_iff {n : ℕ} (hn : 0 < n) (p : ProbVec n) :
    shannonEntropy p = 0 ↔ ∃ i, p.1 i = 1 :=
  ⟨exists_eq_one_of_shannonEntropy_eq_zero hn p, shannonEntropy_eq_zero_of_exists_eq_one p⟩

/-! ## Continuity -/

/-- Shannon entropy is continuous.
    This follows from the continuity of negMulLog. -/
theorem continuous_shannonEntropy {n : ℕ} :
    Continuous (fun p : ProbVec n => shannonEntropy p) := by
  unfold shannonEntropy
  apply continuous_finset_sum
  intro i _
  exact continuous_negMulLog.comp (continuous_apply i |>.comp continuous_subtype_val)

/-! ## Expansibility -/

/-- Shannon entropy is unchanged when appending a zero probability outcome.
    This is Shannon-Khinchin axiom SK3 (Expansibility): H(p₁,...,pₙ,0) = H(p₁,...,pₙ).
    The proof follows from `negMulLog 0 = 0`. -/
theorem shannonEntropy_expandZero {n : ℕ} (p : ProbVec n) :
    shannonEntropy (expandZero p) = shannonEntropy p := by
  unfold shannonEntropy expandZero
  -- Sum over Fin (n+1) = sum over Fin n (via castSucc) + last term
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, negMulLog_zero, add_zero]

/-! ## Concavity -/

end Mettapedia.InformationTheory
