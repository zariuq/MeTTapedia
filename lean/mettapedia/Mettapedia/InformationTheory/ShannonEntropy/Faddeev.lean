import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Convert

/-!
# Faddeev's Axiomatic Characterization of Shannon Entropy

This file formalizes Faddeev's 1956 axiomatization of Shannon entropy and proves
the uniqueness theorem: any function satisfying Faddeev's axioms must equal
the Shannon entropy (up to a multiplicative constant determined by normalization).

## The Key Insight: Faddeev is MINIMAL

Faddeev's axioms are the **minimal** characterization of Shannon entropy:

**Only 4 axioms** (compared to Shannon-Khinchin's 5):
1. **Binary Continuity (F1)**: H(p, 1-p) is continuous (NOT full continuity!)
2. **Symmetry (F2)**: H is invariant under permutations
3. **Recursivity (F3)**: H satisfies the grouping/chain rule
4. **Normalization (F4)**: H(1/2, 1/2) = 1

## What Faddeev DERIVES (others ASSUME)

| Property | Faddeev | Shannon-Khinchin |
|----------|---------|------------------|
| Binary continuity | **ASSUMES** | - |
| Full continuity | **DERIVES** | ASSUMES |
| Symmetry | ASSUMES | DERIVES |
| Recursivity | ASSUMES | ASSUMES (=strong additivity) |
| Monotonicity | **DERIVES** | - |
| Maximality | **DERIVES** | ASSUMES |
| Expansibility | **DERIVES** | ASSUMES |
| **Total axioms** | **4** | **5** |

## Proof Strategy (via Lemma 9)

1. From recursivity: F(mn) = F(m) + F(n) where F(n) = H(uniform(n))
2. From normalization: F(2) = 1, hence F(2^k) = k
3. Define c_p = F(p)/log(p) for primes p
4. Via prime power analysis and binary continuity: All c_p are equal
5. Conclusion: F(n) = log₂(n) for all n ≥ 1
6. Full continuity, monotonicity, and maximality then follow!

## Main Results

* `FaddeevEntropy` - Structure encoding Faddeev's 4 axioms
* `shannonFaddeev` - Shannon entropy satisfies Faddeev's axioms
* `faddeev_F_eq_log2` - The main uniqueness theorem: F(n) = log₂(n)
* `faddeev_F_monotone` - Derived: F is monotone (Faddeev proves, Shannon assumes)
* `faddeev_c_prime_all_equal` - Key lemma: all c_p = c_2 = 1/log(2)

## References

* Faddeev, D.K. "On the concept of entropy of a finite probabilistic scheme" (1956)
* Leinster, T. "An operadic introduction to entropy" (lecture notes)
-/

namespace Mettapedia.InformationTheory

open scoped Topology

open Finset Real Filter

/-! ## Faddeev's Axioms -/

/-- **Faddeev entropy**: A family of functions H : ProbVec n → ℝ satisfying
    Faddeev's three axioms plus normalization. -/
structure FaddeevEntropy where
  /-- The entropy function for each arity n ≥ 1 -/
  H : ∀ {n : ℕ}, ProbVec n → ℝ
  /-- F1: Continuity of binary entropy -/
  continuous_binary : Continuous (fun p : Set.Icc (0 : ℝ) 1 =>
    H (binaryDist p.1 p.2.1 p.2.2))
  /-- F2: Symmetry under permutations -/
  symmetry : ∀ {n : ℕ} (p : ProbVec n) (σ : Equiv.Perm (Fin n)),
    H (permute σ p) = H p
  /-- F3: Recursivity / Chain Rule / Grouping Property

      H(p₁,...,pₙ) = H(p₁+p₂, p₃,...,pₙ) + (p₁+p₂)·H(p₁/(p₁+p₂), p₂/(p₁+p₂))

      This expresses that grouping the first two outcomes into one
      splits the entropy into two parts. -/
  recursivity : ∀ {n : ℕ} (p : ProbVec (n + 2)) (h : 0 < p.1 0 + p.1 1),
    H p = H (groupFirstTwo p h) + (p.1 0 + p.1 1) * H (normalizeBinary (p.1 0) (p.1 1)
      (p.nonneg 0) (p.nonneg 1) h)
  /-- Normalization: H(1/2, 1/2) = 1 -/
  normalization : H binaryUniform = 1

/-- Shannon entropy (normalized) satisfies all of Faddeev's axioms. -/
noncomputable def shannonFaddeev : FaddeevEntropy :=
  { H := @shannonEntropyNormalized
    continuous_binary := by
      -- Continuity follows from continuity of negMulLog
      unfold shannonEntropyNormalized shannonEntropy binaryDist
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      apply Continuous.div_const
      apply Continuous.add
      · exact continuous_negMulLog.comp (continuous_subtype_val.comp continuous_id)
      · apply continuous_negMulLog.comp
        apply Continuous.sub continuous_const
        exact continuous_subtype_val.comp continuous_id
    symmetry := fun p σ => by
      unfold shannonEntropyNormalized
      rw [shannonEntropy_permute]
    recursivity := fun p h => by
      unfold shannonEntropyNormalized
      -- Use the recursivity of unnormalized Shannon entropy and divide by log 2
      rw [shannonEntropy_recursivity p h]
      ring
    normalization := shannonEntropyNormalized_binaryUniform }

/-! ## Functional Equation Approach -/

/-! ### Helper Lemmas for Uniform Distributions -/

/-- When grouping two equal probabilities a = b, the normalized binary is (1/2, 1/2). -/
theorem normalizeBinary_eq_eq_binaryUniform (a : ℝ) (ha : 0 ≤ a) (hab : 0 < a + a) :
    normalizeBinary a a ha ha hab = binaryUniform := by
  have ha' : a ≠ 0 := by
    intro h; subst h; simp at hab
  have hab' : a + a ≠ 0 := ne_of_gt hab
  have key : a / (a + a) = 1 / 2 := by field_simp; ring
  apply Subtype.ext
  funext i
  fin_cases i
  · -- First component
    show (![a / (a + a), a / (a + a)] : Fin 2 → ℝ) 0 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 0
    simp only [Matrix.cons_val_zero, key]
  · -- Second component
    show (![a / (a + a), a / (a + a)] : Fin 2 → ℝ) 1 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 1
    simp only [Matrix.cons_val_one, key]
    norm_num

/-- Helper: F(2) = 1 follows from normalization since uniform_2 = binaryUniform. -/
theorem faddeev_F2_eq_one (E : FaddeevEntropy) :
    E.H (uniformDist 2 (by norm_num : 0 < 2)) = 1 := by
  -- uniform_2 = (1/2, 1/2) = binaryUniform
  have h : uniformDist 2 (by norm_num : 0 < 2) = binaryUniform := by
    apply Subtype.ext
    funext i
    fin_cases i
    · -- First component: 1/2 = 1/2
      show (1 : ℝ) / 2 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 0
      simp only [Matrix.cons_val_zero]
    · -- Second component: 1/2 = 1 - 1/2 = 1/2
      show (1 : ℝ) / 2 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 1
      simp only [Matrix.cons_val_one]
      norm_num
  rw [h]
  exact E.normalization

/-- F(1) = 0 for any Faddeev entropy.
    This follows directly from recursivity on (1, 0):
    H(1, 0) = H(uniformDist 1) + 1 * H(1, 0) = F(1) + H(1, 0)
    Therefore F(1) = 0. -/
theorem faddeev_F1_eq_zero (E : FaddeevEntropy) :
    E.H (uniformDist 1 (by norm_num : 0 < 1)) = 0 := by
  -- Apply recursivity to (1, 0) ∈ ProbVec 2
  -- p = (1, 0) is a binary distribution
  set p := binaryDist 1 (by norm_num) (by norm_num) with hp
  have h_sum : 0 < p.1 0 + p.1 1 := by
    simp only [hp, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h_rec := E.recursivity p h_sum
  have h_sum_eq : p.1 0 + p.1 1 = 1 := by
    simp only [hp, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [h_sum_eq] at h_rec
  -- normalizeBinary (1) (0) = (1, 0) = p
  have h_norm : normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h_sum = p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp only [hp, normalizeBinary, binaryDist, Matrix.cons_val_zero]; norm_num
    · simp only [hp, normalizeBinary, binaryDist, Matrix.cons_val_one]; norm_num
  rw [h_norm] at h_rec
  -- h_rec: E.H p = E.H (groupFirstTwo p h_sum) + E.H p
  -- Therefore: E.H (groupFirstTwo p h_sum) = 0
  have hF1 : E.H (groupFirstTwo p h_sum) = 0 := by linarith
  -- groupFirstTwo (1, 0) = uniformDist 1
  have h_group : groupFirstTwo p h_sum = uniformDist 1 (by norm_num : 0 < 1) := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp only [groupFirstTwo, uniformDist, hp, binaryDist,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
  rw [← h_group]
  exact hF1

/-- For a Faddeev entropy, H(1, 0) = 0.
    Proof via ternary recursivity + symmetry + continuity:
    For (ε, ε, 1-2ε), by symmetry H(ε, ε, 1-2ε) = H(1-2ε, ε, ε).
    Grouping (ε,ε) gives: f(2ε) + 2ε
    Grouping (1-2ε,ε) gives: f(ε) + (1-ε) * h((1-2ε)/(1-ε))
    As ε → 0: f(0) = f(0) + f(1), hence f(1) = 0. -/
theorem faddeev_H_one_zero (E : FaddeevEntropy) :
    E.H (binaryDist 1 (by norm_num) (by norm_num)) = 0 := by
  -- A purely algebraic proof using just symmetry + recursivity.
  --
  -- Consider the ternary distribution (1/2, 0, 1/2). Grouping (1/2, 0) yields:
  --   H(1/2,0,1/2) = H(1/2,1/2) + (1/2) * H(1,0).
  --
  -- Permuting to (1/2, 1/2, 0) and grouping (1/2,1/2) yields:
  --   H(1/2,1/2,0) = H(1,0) + H(1/2,1/2).
  --
  -- By symmetry, these ternary entropies are equal, so (1/2) * H(1,0) = H(1,0),
  -- hence H(1,0)=0.
  set p : ProbVec 3 :=
      ternaryDist (1/2) 0 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) with hp
  have hp_sum01 : 0 < p.1 0 + p.1 1 := by
    simp [hp, ternaryDist]
  have hrec_p := E.recursivity p hp_sum01
  have hp_sum01_val : p.1 0 + p.1 1 = (1 / 2 : ℝ) := by
    simp [hp, ternaryDist]
  -- normalizeBinary (1/2) 0 = (1,0)
  have hnorm_p :
      normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) hp_sum01 =
        binaryDist 1 (by norm_num) (by norm_num) := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [hp, ternaryDist, normalizeBinary, binaryDist]
    · simp [hp, ternaryDist, normalizeBinary, binaryDist]
  -- groupFirstTwo (1/2,0,1/2) = (1/2,1/2)
  have hgroup_p : groupFirstTwo p hp_sum01 = binaryUniform := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [hp, ternaryDist, groupFirstTwo, binaryUniform, binaryDist]
    ·
      simp [hp, ternaryDist, groupFirstTwo, binaryUniform, binaryDist]
      norm_num
  -- Rewrite the recursivity equation for `p`.
  have hHp :
      E.H p = 1 + (1 / 2 : ℝ) * E.H (binaryDist 1 (by norm_num) (by norm_num)) := by
    -- Use normalization to rewrite H(binaryUniform).
    have hbin : E.H binaryUniform = 1 := E.normalization
    -- Simplify
    simpa [hp_sum01_val, hnorm_p, hgroup_p, hbin] using hrec_p
  -- Now the permuted ternary distribution (1/2,1/2,0).
  set p' : ProbVec 3 :=
      ternaryDist (1/2) (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) with hp'
  have hp'_sum01 : 0 < p'.1 0 + p'.1 1 := by
    simp [hp', ternaryDist]
  have hrec_p' := E.recursivity p' hp'_sum01
  have hp'_sum01_val : p'.1 0 + p'.1 1 = (1 : ℝ) := by
    simp [hp', ternaryDist]
    norm_num
  have hnorm_p' :
      normalizeBinary (p'.1 0) (p'.1 1) (p'.nonneg 0) (p'.nonneg 1) hp'_sum01 =
        binaryUniform := by
    apply Subtype.ext
    funext i
    simp [hp', ternaryDist, normalizeBinary, binaryUniform, binaryDist]
    fin_cases i <;> norm_num
  have hgroup_p' :
      groupFirstTwo p' hp'_sum01 = binaryDist 1 (by norm_num) (by norm_num) := by
    apply Subtype.ext
    funext i
    fin_cases i
    ·
      simp [hp', ternaryDist, groupFirstTwo, binaryDist]
      norm_num
    · simp [hp', ternaryDist, groupFirstTwo, binaryDist]
  have hHp' :
      E.H p' = E.H (binaryDist 1 (by norm_num) (by norm_num)) + 1 := by
    have hbin : E.H binaryUniform = 1 := E.normalization
    simpa [hp'_sum01_val, hnorm_p', hgroup_p', hbin] using hrec_p'
  -- Relate p and p' by a swap permutation (1 ↔ 2).
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hperm : permute σ p' = p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · have hσ : σ⁻¹ (0 : Fin 3) = (0 : Fin 3) := by decide
      simp [permute_apply, hσ, hp, hp', ternaryDist]
    · have hσ : σ⁻¹ (1 : Fin 3) = (2 : Fin 3) := by decide
      simp [permute_apply, hσ, hp, hp', ternaryDist]
    · have hσ : σ⁻¹ (2 : Fin 3) = (1 : Fin 3) := by decide
      simp [permute_apply, hσ, hp, hp', ternaryDist]
  have hsym : E.H p = E.H p' := by
    -- `E.symmetry` gives `H (permute σ p') = H p'`.
    simpa [hperm] using E.symmetry p' σ
  -- Combine the two expressions for `H p` and `H p'`.
  -- 1 + (1/2) * H10 = H10 + 1  ⇒ H10 = 0.
  have : (1 / 2 : ℝ) * E.H (binaryDist 1 (by norm_num) (by norm_num)) =
      E.H (binaryDist 1 (by norm_num) (by norm_num)) := by
    linarith [hHp, hHp', hsym]
  -- Solve `(1/2) * h = h` for `h`.
  linarith

/-!
## Faddeev 1956: “Splitting” Lemma (Lemma 5)

Faddeev’s core technical move is that if we “split” an outcome of weight `p₀`
into a refined distribution `q` (so the refined outcomes have weights `p₀*qᵢ`),
then the entropy changes by `p₀ * H(q)`.

We prove it in a Lean-friendly form where we always split the *first* outcome;
symmetry lets us apply this to any outcome when needed.
-/

/-! ### The split construction -/

/-- Split the first outcome of `p : ProbVec (n+1)` into `m` refined outcomes
according to `q : ProbVec m`.

The resulting distribution has `n + m` outcomes:
- the first `m` outcomes have probabilities `p₀ * qᵢ`;
- the remaining `n` outcomes keep the original probabilities `p₁, …, pₙ`. -/
noncomputable def splitFirst {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) : ProbVec (n + m) := by
  classical
  -- Define the distribution on `Fin (n+m)` by transporting indices to `Fin (m+n)` and using
  -- `Fin.addCases` to splice the split block and the untouched tail.
  refine ⟨fun i : Fin (n + m) =>
      Fin.addCases (motive := fun _ : Fin (m + n) => ℝ)
        (fun j : Fin m => p.1 0 * q.1 j) (fun j : Fin n => p.1 j.succ)
        (i.cast (Nat.add_comm n m)), ?_⟩
  constructor
  · intro i
    -- Nonnegativity is inherited from `p` and `q`.
    refine Fin.addCases (motive := fun j : Fin (m + n) => 0 ≤
      Fin.addCases (motive := fun _ : Fin (m + n) => ℝ)
        (fun j : Fin m => p.1 0 * q.1 j) (fun j : Fin n => p.1 j.succ) j) ?_ ?_
        (i.cast (Nat.add_comm n m))
    · intro j
      simp
      exact mul_nonneg (p.nonneg 0) (q.nonneg j)
    · intro j
      simpa using p.nonneg j.succ
  ·
    classical
    -- For the sum, rewrite to the `Fin (m+n)` sum via `Equiv.sum_comp` and then split blocks.
    set f : Fin m → ℝ := fun j => p.1 0 * q.1 j
    set g : Fin n → ℝ := fun j => p.1 j.succ
    -- Change of variables along `n+m = m+n`.
    have hcast :
        (∑ i : Fin (n + m),
            Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g (i.cast (Nat.add_comm n m)))
          =
          (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i) := by
      -- `Fin.cast (Nat.add_comm n m)` is a permutation of indices.
      let e : Fin (n + m) ≃ Fin (m + n) :=
        { toFun := Fin.cast (Nat.add_comm n m)
          invFun := Fin.cast (Nat.add_comm m n)
          left_inv := by
            intro i
            ext
            simp
          right_inv := by
            intro i
            ext
            simp }
      simpa [e] using (Equiv.sum_comp e (fun i : Fin (m + n) =>
        Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i))
    -- Split the `Fin (m+n)` sum into the `m`-block and the `n`-block.
    have hsum :
        (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i)
          = (∑ i : Fin m, f i) + (∑ i : Fin n, g i) := by
      have h := (Fin.sum_univ_add (f := fun i : Fin (m + n) =>
        Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i))
      simpa [f, g, add_assoc, add_left_comm, add_comm] using h
    -- Tail sum of `p` is `1 - p₀`.
    have htail : (∑ i : Fin n, p.1 i.succ) = 1 - p.1 0 := by
      have : p.1 0 + (∑ i : Fin n, p.1 i.succ) = 1 := by
        simpa [Fin.sum_univ_succ, add_assoc] using
          (p.sum_eq_one : (∑ i : Fin (n + 1), p.1 i) = 1)
      linarith
    -- First block sum is `p₀`.
    have hhead : (∑ i : Fin m, f i) = p.1 0 := by
      have h :=
        (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i : Fin m => q.1 i)
          (p.1 0))
      calc
        (∑ i : Fin m, f i) = p.1 0 * (∑ i : Fin m, q.1 i) := by
          simpa [f] using h.symm
        _ = p.1 0 := by simp [q.sum_eq_one]
    -- Conclude the transported sum equals 1.
    calc
      (∑ i : Fin (n + m),
          Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g (i.cast (Nat.add_comm n m)))
          =
          (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i) := hcast
      _ = (∑ i : Fin m, f i) + (∑ i : Fin n, g i) := hsum
      _ = p.1 0 + (1 - p.1 0) := by simp [hhead, htail, g]
      _ = 1 := by ring

theorem splitFirst_castAdd {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) (i : Fin m) :
    (splitFirst p q).1 ((Fin.castAdd n i).cast (Nat.add_comm m n)) = p.1 0 * q.1 i := by
  simp [splitFirst]

theorem splitFirst_natAdd {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) (i : Fin n) :
    (splitFirst p q).1 ((Fin.natAdd m i).cast (Nat.add_comm m n)) = p.1 i.succ := by
  simp [splitFirst]

/-! ### The binary splitting case (used later) -/

/-- Splitting an outcome into a **binary** sub-distribution.

This is the `m=2` case of Faddeev’s Lemma 5, and it follows directly from the recursivity axiom. -/
theorem faddeev_splitFirst_two {n : ℕ} (E : FaddeevEntropy) (p : ProbVec (n + 1)) (q : ProbVec 2)
    (hp0 : 0 < p.1 0) :
    E.H (splitFirst p q) = E.H p + p.1 0 * E.H q := by
  have hqsum : q.1 0 + q.1 1 = 1 := by
    simpa [Fin.sum_univ_two, add_assoc] using (q.sum_eq_one : (∑ i : Fin 2, q.1 i) = 1)
  have h0 : (splitFirst p q).1 0 = p.1 0 * q.1 0 := by
    -- `0` is in the split block.
    simpa using (splitFirst_castAdd (p := p) (q := q) (n := n) (i := (0 : Fin 2)))
  have h1 : (splitFirst p q).1 1 = p.1 0 * q.1 1 := by
    -- `1` is in the split block.
    simpa using (splitFirst_castAdd (p := p) (q := q) (n := n) (i := (1 : Fin 2)))
  have hsum_eq : (splitFirst p q).1 0 + (splitFirst p q).1 1 = p.1 0 := by
    -- Use `q0+q1=1`.
    calc
      (splitFirst p q).1 0 + (splitFirst p q).1 1 = p.1 0 * (q.1 0 + q.1 1) := by
        simp [h0, h1, mul_add]
      _ = p.1 0 := by simp [hqsum]
  have hsum : 0 < (splitFirst p q).1 0 + (splitFirst p q).1 1 := by
    simpa [hsum_eq] using hp0
  have hrec := E.recursivity (splitFirst p q) hsum
  have hgroup : groupFirstTwo (splitFirst p q) hsum = p := by
    apply Subtype.ext
    funext i
    by_cases h0i : i.1 = 0
    ·
      have hi : i = 0 := by
        ext
        simpa using h0i
      subst hi
      -- grouped head is the sum of the first two split entries
      simp [groupFirstTwo, hsum_eq]
    ·
      -- grouped tail shifts by `+1`; this lands in the original tail of `p`
      cases i using Fin.cases with
      | zero =>
        cases h0i rfl
      | succ i =>
        -- `i : Fin n`, and the split distribution at index `i.succ.succ` is `p i.succ`.
        have htail :
            (splitFirst p q).1 ⟨i.1 + 2, by
              exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ = p.1 i.succ := by
          simpa using (splitFirst_natAdd (p := p) (q := q) (m := 2) (i := i))
        -- unfold `groupFirstTwo` at `Fin.succ i`
        simp [groupFirstTwo, htail]
  have hnorm :
      normalizeBinary ((splitFirst p q).1 0) ((splitFirst p q).1 1)
          ((splitFirst p q).nonneg 0) ((splitFirst p q).nonneg 1) hsum
        = q := by
    apply Subtype.ext
    funext i
    fin_cases i
    ·
      have hp0ne : (p.1 0) ≠ 0 := ne_of_gt hp0
      have hden : p.1 0 * q.1 0 + p.1 0 * q.1 1 = p.1 0 := by
        -- rewrite the grouped sum using `h0`, `h1`
        simpa [h0, h1] using hsum_eq
      -- cancel `p₀` in `(p₀*q₀)/p₀ = q₀`
      simp [normalizeBinary, h0, h1, hden, hp0ne]
    ·
      have hp0ne : (p.1 0) ≠ 0 := ne_of_gt hp0
      have hden : p.1 0 * q.1 0 + p.1 0 * q.1 1 = p.1 0 := by
        simpa [h0, h1] using hsum_eq
      simp [normalizeBinary, h0, h1, hden, hp0ne]
  simpa [hgroup, hnorm, hsum_eq, mul_assoc] using hrec

/-!
### Faddeev Lemma 5 (general splitting, head-positive form)

For the later uniqueness proof we need the “splitting” lemma for arbitrary finite refinements:
splitting the first outcome of weight `p₀` according to a distribution `q` adds `p₀ * H(q)`.

The recursivity axiom only applies when the first two outcomes have positive total weight,
so we state the lemma in a head-positive form (`0 < q₀ + q₁`), which is the regime used in
the core Faddeev argument (uniform distributions have this automatically).  A fully general
version can be recovered by permuting the coordinates using symmetry.
-/

/-- Splitting an outcome into an arbitrary refinement, assuming the first two pieces have
positive total weight. -/
theorem faddeev_splitFirst_headPos {n m : ℕ} (E : FaddeevEntropy)
    (p : ProbVec (n + 1)) (q : ProbVec (m + 2))
    (hp0 : 0 < p.1 0) (hq : 0 < q.1 0 + q.1 1) :
    E.H (splitFirst p q) = E.H p + p.1 0 * E.H q := by
  -- We follow Faddeev’s induction on the refinement size.
  induction m with
  | zero =>
    -- `q : ProbVec 2` is exactly the binary splitting lemma.
    simpa using faddeev_splitFirst_two (E := E) (p := p) (q := q) hp0
  | succ m ih =>
    -- `q : ProbVec (m+3)`.  Group its first two outcomes, and use recursivity on both `q`
    -- and the split distribution.
    set sp : ProbVec (n + (m + 1 + 2)) := splitFirst (n := n) (m := m + 1 + 2) p q with hsp
    have hqsum : 0 ≤ q.1 0 + q.1 1 := by nlinarith [q.nonneg 0, q.nonneg 1]
    set qGroup : ProbVec (m + 2) := groupFirstTwo q hq with hqGroup
    set qBin : ProbVec 2 :=
      normalizeBinary (q.1 0) (q.1 1) (q.nonneg 0) (q.nonneg 1) hq with hqBin
    -- Recursivity on `q`:
    have hq_rec : E.H q = E.H qGroup + (q.1 0 + q.1 1) * E.H qBin := by
      -- `groupFirstTwo q hq = qGroup` and the normalized binary is `qBin` by definition.
      simpa [hqGroup, hqBin] using E.recursivity (n := m + 1) q hq
    -- Head-positivity for the grouped refinement: `(q0+q1) + q2 > 0`.
    have hqGroup_head : 0 < qGroup.1 0 + qGroup.1 1 := by
      -- `qGroup.1 0 = q0+q1` and `qGroup.1 1 = q2`.
      have h0' : qGroup.1 0 = q.1 0 + q.1 1 := by
        simp [qGroup, groupFirstTwo]
      have h1' : qGroup.1 1 = q.1 2 := by
        -- `groupFirstTwo` tail at index `1` is `q[2]`.
        simp [qGroup, groupFirstTwo]
        have hlt : 2 < m + 1 + 2 := by
          omega
        have hidx : (⟨2, hlt⟩ : Fin (m + 1 + 2)) = 2 := by
          ext
          simp [Nat.mod_eq_of_lt hlt]
        simp [hidx]
      -- Use `hq` and nonnegativity of `q2`.
      nlinarith [hq, q.nonneg 2, h0', h1']
    -- Induction hypothesis for the grouped refinement.
    have ih' :
        E.H (splitFirst (n := n) (m := m + 2) p qGroup) = E.H p + p.1 0 * E.H qGroup := by
      -- `m` decreased by 1, and head-positivity is `hqGroup_head`.
      exact ih (q := qGroup) hqGroup_head
    -- Now apply recursivity to the split distribution, grouping the first two split pieces.
    have h0 : sp.1 0 = p.1 0 * q.1 0 := by
      -- `0 = castAdd _ 0` in the split block
      simpa [hsp] using
        (splitFirst_castAdd (p := p) (q := q) (n := n) (i := (0 : Fin (m + 1 + 2))))
    have h1 : sp.1 1 = p.1 0 * q.1 1 := by
      simpa [hsp] using
        (splitFirst_castAdd (p := p) (q := q) (n := n) (i := (1 : Fin (m + 1 + 2))))
    have hsum_eq : sp.1 0 + sp.1 1 = p.1 0 * (q.1 0 + q.1 1) := by
      simp [h0, h1, mul_add]
    have hsum : 0 < sp.1 0 + sp.1 1 := by
      -- `p0 > 0` and `q0+q1 > 0`.
      nlinarith [hp0, hq, hsum_eq]
    -- `splitFirst p q` has length `n + (m+3)`, which we view as `(n + (m+1)) + 2`
    -- to apply the recursivity axiom.
    have hsplit_rec :
        E.H sp =
          E.H (groupFirstTwo sp hsum)
            + (sp.1 0 + sp.1 1) *
              E.H
                (normalizeBinary (sp.1 0) (sp.1 1) (sp.nonneg 0) (sp.nonneg 1) hsum) := by
      -- Coerce along associativity: `(n + (m+1)) + 2 = n + (m+3)`.
      have := E.recursivity (n := n + (m + 1))
        (p := (by
          -- `sp : ProbVec (n + ((m+1)+2))`
          -- and `Nat.add_assoc n (m+1) 2` rewrites `n + ((m+1)+2)` to `(n+(m+1))+2`.
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using sp))
        (h := by
          -- transport the head-positivity proof along the same coercion
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum)
      -- Unfold the coercions back to the original shape.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    -- Identify the grouped split distribution with `splitFirst p qGroup`.
    have hgroup_split : groupFirstTwo sp hsum = splitFirst (n := n) (m := m + 2) p qGroup := by
      apply Subtype.ext
      funext i
      by_cases h0i : i.1 = 0
      ·
        have hi : i = 0 := by
          ext
          simpa using h0i
        subst hi
        -- Head is the sum of the first two split entries.
        have : (splitFirst (n := n) (m := m + 2) p qGroup).1 0 = p.1 0 * (q.1 0 + q.1 1) := by
          -- first entry of `qGroup` is `q0+q1`
          have : qGroup.1 0 = q.1 0 + q.1 1 := by
            simp [qGroup, groupFirstTwo]
          simpa [this] using
            (splitFirst_castAdd (p := p) (q := qGroup) (n := n) (i := (0 : Fin (m + 2))))
        simp [groupFirstTwo, hsum_eq, this]
      ·
        -- Tail indices shift by `+1` on both sides.
        cases i using Fin.cases with
        | zero =>
          cases h0i rfl
        | succ i =>
          -- `i : Fin (n + m + 1)`. We compare the split block and the tail block separately.
          have hL :
              (groupFirstTwo sp hsum).1 (Fin.succ i) =
                sp.1 ⟨i.1 + 2, by
                  exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ := by
            simp [groupFirstTwo]
          -- Case split: is `i` still within the split block (excluding the head) or already in the tail?
          by_cases hi : i.1 < m + 1
          ·
            -- Split-block case: the grouped distribution reads `p₀ * q[i+2]`.
            set iSplit : Fin (m + 1) := ⟨i.1, hi⟩
            have hiSplit : (Fin.succ iSplit : Fin (m + 2)).1 = i.1 + 1 := by
              simp [iSplit]
            have hqIdx :
                (Fin.succ (Fin.succ iSplit) : Fin (m + 1 + 2)).1 = i.1 + 2 := by
              simp [iSplit, Nat.add_assoc]
            -- Identify the relevant indices in the split distributions.
            let idxR : Fin (n + (m + 2)) :=
              ((Fin.castAdd n (Fin.succ iSplit)).cast (Nat.add_comm (m + 2) n))
            have hidxR : idxR = Fin.succ i := by
              ext
              simp [idxR, iSplit, Fin.val_succ]
            let idxL : Fin (n + (m + 1 + 2)) :=
              ((Fin.castAdd n (Fin.succ (Fin.succ iSplit))).cast (Nat.add_comm (m + 1 + 2) n))
            have hidxL :
                idxL =
                  ⟨i.1 + 2, by
                    exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ := by
              ext
              simp [idxL, iSplit, Nat.add_assoc]
            have hidxL' :
                sp.1 ⟨i.1 + 2, by
                  exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ = (splitFirst p q).1 idxL := by
              -- rewrite `sp` back to `splitFirst p q`
              simp [hsp, hidxL]
            -- Compute both sides.
            have hsp_val :
                (splitFirst p q).1 idxL = p.1 0 * q.1 (Fin.succ (Fin.succ iSplit)) := by
              simpa [idxL] using
                (splitFirst_castAdd (p := p) (q := q) (n := n) (i := (Fin.succ (Fin.succ iSplit))))
            have hqGroup_val :
                qGroup.1 (Fin.succ iSplit) = q.1 ⟨i.1 + 2, by
                  exact Nat.succ_lt_succ (Nat.succ_lt_succ hi)⟩ := by
              -- `qGroup` tail at index `succ iSplit` is `q[i+2]`.
              simp [qGroup, groupFirstTwo, iSplit, Nat.add_assoc]
            have hqGroup_val' :
                qGroup.1 (Fin.succ iSplit) = q.1 (Fin.succ (Fin.succ iSplit)) := by
              -- reconcile the `Fin` indices
              have :
                  (Fin.succ (Fin.succ iSplit) : Fin (m + 1 + 2)) =
                    ⟨i.1 + 2, by
                      exact Nat.succ_lt_succ (Nat.succ_lt_succ hi)⟩ := by
                ext
                simp [iSplit]
              simpa [this] using hqGroup_val
            have hrhs :
                (splitFirst p qGroup).1 (Fin.succ i) = p.1 0 * qGroup.1 (Fin.succ iSplit) := by
              -- use the castAdd lemma at the identified index
              simpa [hidxR] using
                (splitFirst_castAdd (p := p) (q := qGroup) (n := n) (i := (Fin.succ iSplit)))
            -- Put everything together.
            calc
              (groupFirstTwo sp hsum).1 (Fin.succ i)
                  = sp.1 ⟨i.1 + 2, by
                      exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ := hL
              _ = (splitFirst p q).1 idxL := hidxL'
              _ = p.1 0 * q.1 (Fin.succ (Fin.succ iSplit)) := hsp_val
              _ = p.1 0 * qGroup.1 (Fin.succ iSplit) := by simp [hqGroup_val']
              _ = (splitFirst p qGroup).1 (Fin.succ i) := by simp [hrhs]
          ·
            -- Tail case: both sides read the untouched tail of `p`.
            have hge : m + 1 ≤ i.1 := le_of_not_gt hi
            have hTailLt : i.1 - (m + 1) < n := by
              -- `i.val < n + (m+1)` and `m+1 ≤ i.val` give the result by subtraction.
              exact (Nat.sub_lt_iff_lt_add hge).2 i.isLt
            set iTail : Fin n := ⟨i.1 - (m + 1), hTailLt⟩
            let idxR : Fin (n + (m + 2)) :=
              ((Fin.natAdd (m + 2) iTail).cast (Nat.add_comm (m + 2) n))
            have hidxR : idxR = Fin.succ i := by
              ext
              -- Unfolding reduces to a plain `Nat` identity.
              simp [idxR, iTail, Fin.val_succ]
              calc
                i.1 - (m + 1) + (m + 2) = (i.1 - (m + 1) + (m + 1)) + 1 := by
                  simp [Nat.add_assoc]
                _ = i.1 + 1 := by
                  simp [Nat.sub_add_cancel hge]
            let idxL : Fin (n + (m + 1 + 2)) :=
              ((Fin.natAdd (m + 1 + 2) iTail).cast (Nat.add_comm (m + 1 + 2) n))
            have hidxL :
                idxL =
                  ⟨i.1 + 2, by
                    exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ := by
              ext
              simp [idxL, iTail]
              calc
                i.1 - (m + 1) + (m + 1 + 2) = (i.1 - (m + 1) + (m + 1)) + 2 := by
                  simp [Nat.add_assoc]
                _ = i.1 + 2 := by
                  simp [Nat.sub_add_cancel hge]
            have hidxL' :
                sp.1 ⟨i.1 + 2, by
                  exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ = (splitFirst p q).1 idxL := by
              simp [hsp, hidxL]
            have hsp_val : (splitFirst p q).1 idxL = p.1 iTail.succ := by
              simpa [idxL] using
                (splitFirst_natAdd (p := p) (q := q) (m := m + 1 + 2) (i := iTail))
            have hrhs : (splitFirst p qGroup).1 (Fin.succ i) = p.1 iTail.succ := by
              simpa [hidxR, idxR] using
                (splitFirst_natAdd (p := p) (q := qGroup) (m := m + 2) (i := iTail))
            calc
              (groupFirstTwo sp hsum).1 (Fin.succ i)
                  = sp.1 ⟨i.1 + 2, by
                      exact Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ := hL
              _ = (splitFirst p q).1 idxL := hidxL'
              _ = p.1 iTail.succ := hsp_val
              _ = (splitFirst p qGroup).1 (Fin.succ i) := hrhs.symm
    -- Identify the normalized binary of the split head with `qBin`.
    have hnorm_split :
        normalizeBinary (sp.1 0) (sp.1 1) (sp.nonneg 0) (sp.nonneg 1) hsum
          = qBin := by
      apply Subtype.ext
      funext i
      fin_cases i
      ·
        have hp0ne : (p.1 0) ≠ 0 := ne_of_gt hp0
        have hqne : (q.1 0 + q.1 1) ≠ 0 := ne_of_gt hq
        -- cancel `p₀` in `(p₀*q₀)/(p₀*(q₀+q₁)) = q₀/(q₀+q₁)`
        have hfrac :
            p.1 0 * q.1 0 / (p.1 0 * q.1 0 + p.1 0 * q.1 1) = q.1 0 / (q.1 0 + q.1 1) := by
          -- rewrite the denominator and cancel `p₀`
          field_simp [hp0ne, hqne]
        -- Unfold both normalized binaries.
        simpa [qBin, hqBin, normalizeBinary, h0, h1, mul_add] using hfrac
      ·
        have hp0ne : (p.1 0) ≠ 0 := ne_of_gt hp0
        have hqne : (q.1 0 + q.1 1) ≠ 0 := ne_of_gt hq
        have hfrac :
            p.1 0 * q.1 1 / (p.1 0 * q.1 0 + p.1 0 * q.1 1) = q.1 1 / (q.1 0 + q.1 1) := by
          field_simp [hp0ne, hqne]
        simpa [qBin, hqBin, normalizeBinary, h0, h1, mul_add] using hfrac
    -- Assemble: recursivity on the split, induction on `qGroup`, and recursivity on `q`.
    calc
      E.H sp
          = E.H (groupFirstTwo sp hsum) + (sp.1 0 + sp.1 1) * E.H qBin := by
            simp [hsplit_rec, hqBin, hnorm_split]
      _ = (E.H p + p.1 0 * E.H qGroup) + (p.1 0 * (q.1 0 + q.1 1)) * E.H qBin := by
            simp [hgroup_split, ih', hsum_eq]
      _ = E.H p + p.1 0 * E.H q := by
            -- use `hq_rec : H q = H qGroup + (q0+q1) * H qBin`
            -- and distribute `p0`.
            nlinarith [hq_rec]

/-! ### Two-way Split (splitBoth)

A two-way split refines BOTH outcomes of a binary distribution. Given:
- `p : ProbVec 2` - a binary distribution (p₀, p₁)
- `q₁ : ProbVec m` - refinement for the first outcome
- `q₂ : ProbVec k` - refinement for the second outcome

The result is a distribution on `Fin (m + k)` where:
- First `m` outcomes have probability `p₀ * q₁ᵢ`
- Last `k` outcomes have probability `p₁ * q₂ⱼ`
-/

/-- Two-way split: refine both outcomes of a binary distribution.

Given a binary distribution p = (p₀, p₁) and two distributions q1 on m outcomes
and q2 on k outcomes, construct a distribution on m + k outcomes where:
- First m outcomes have probability p₀ * q1ᵢ
- Last k outcomes have probability p₁ * q2ⱼ

The sum equals 1 because: p₀·∑q1 + p₁·∑q2 = p₀·1 + p₁·1 = p₀ + p₁ = 1.
-/
noncomputable def splitBoth {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k) :
    ProbVec (m + k) := by
  classical
  refine ⟨fun i => if h : i.1 < m then p.1 0 * q1.1 ⟨i.1, h⟩
            else p.1 1 * q2.1 ⟨i.1 - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩,
          ?nonneg, ?sum_one⟩
  case nonneg =>
    intro i
    by_cases h : i.1 < m <;> simp [h] <;> apply mul_nonneg
    · exact p.nonneg 0
    · exact q1.nonneg _
    · exact p.nonneg 1
    · exact q2.nonneg _
  case sum_one =>
    -- The key: ∑ᵢ (if i<m then p₀·q1ᵢ else p₁·q2_{i-m}) = p₀·∑q1 + p₁·∑q2 = p₀ + p₁ = 1
    -- Use Fin.sum_univ_add to split the sum into Fin m and Fin k parts
    rw [Fin.sum_univ_add]
    -- For the first sum (i : Fin m), castAdd k i has val < m, so condition is true
    have h1 : ∑ i : Fin m, (if h : (Fin.castAdd k i).1 < m
        then p.1 0 * q1.1 ⟨(Fin.castAdd k i).1, h⟩
        else p.1 1 * q2.1 ⟨(Fin.castAdd k i).1 - m,
          Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) (Fin.castAdd k i).isLt⟩) =
        p.1 0 * ∑ i : Fin m, q1.1 i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      -- (Fin.castAdd k i).1 = i.1 < m
      have hi : (Fin.castAdd k i).1 < m := i.isLt
      rw [dif_pos hi]
      -- congr closes the goal since (Fin.castAdd k i).1 = i.1
      congr
    -- For the second sum (j : Fin k), natAdd m j has val = m + j ≥ m, so condition is false
    have h2 : ∑ j : Fin k, (if h : (Fin.natAdd m j).1 < m
        then p.1 0 * q1.1 ⟨(Fin.natAdd m j).1, h⟩
        else p.1 1 * q2.1 ⟨(Fin.natAdd m j).1 - m,
          Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) (Fin.natAdd m j).isLt⟩) =
        p.1 1 * ∑ j : Fin k, q2.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      -- (Fin.natAdd m j).1 = m + j.1 ≥ m
      have hj : ¬(Fin.natAdd m j).1 < m := by
        simp only [Fin.natAdd, Nat.not_lt]
        omega
      rw [dif_neg hj]
      -- ⟨(m + j.1) - m, ...⟩ = ⟨j.1, j.isLt⟩ = j
      simp only [Fin.natAdd, Nat.add_sub_cancel_left, Fin.eta]
    rw [h1, h2, q1.sum_eq_one, q2.sum_eq_one, mul_one, mul_one]
    -- Now we have p.1 0 + p.1 1 = 1
    have hp := p.sum_eq_one
    simp only [Fin.sum_univ_two] at hp
    exact hp

/-- Value of splitBoth at an index in the first block. -/
theorem splitBoth_left {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k)
    (i : Fin m) : (splitBoth p q1 q2).1 ⟨i.1, by omega⟩ = p.1 0 * q1.1 i := by
  classical
  -- Unfold and simplify the `if`; `simp` also identifies `⟨i.1, _⟩` with `i`.
  simp [splitBoth, i.isLt]

/-- Value of splitBoth at an index in the second block. -/
theorem splitBoth_right {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k)
    (j : Fin k) : (splitBoth p q1 q2).1 ⟨m + j.1, by omega⟩ = p.1 1 * q2.1 j := by
  classical
  have hj : ¬(m + j.1 < m) := by omega
  simp [splitBoth, hj, Fin.eta]

/-- splitBoth with two uniform distributions gives uniform distribution. -/
theorem splitBoth_uniform_eq_uniform {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    splitBoth (binaryDist ((m : ℝ) / (m + k))
        (div_nonneg (Nat.cast_nonneg m) (by positivity))
        (div_le_one_of_le₀ (by simp) (by positivity)))
      (uniformDist m hm) (uniformDist k hk) =
    uniformDist (m + k) (Nat.add_pos_left hm k) := by
  -- Show component-wise equality: each component equals 1/(m+k)
  apply Subtype.ext
  funext i
  simp only [uniformDist]
  -- Unfold splitBoth directly
  -- Split into two cases: i < m (first block) and i ≥ m (second block)
  by_cases hi : i.1 < m
  · -- Case 1: i is in the first block
    -- LHS = (m/(m+k)) * (1/m) = 1/(m+k) = RHS
    simp [splitBoth, hi, binaryDist]
    -- Goal: (m/(m+k)) * (1/m) = 1/(m+k)
    -- Use norm_cast to normalize ℕ → ℝ coercions before field arithmetic
    norm_cast
    field
  · -- Case 2: i is in the second block
    -- LHS = (1 - m/(m+k)) * (1/k) = 1/(m+k) = RHS
    simp [splitBoth, hi, binaryDist]
    -- Goal: (1 - m/(m+k)) * (1/k) = 1/(m+k)
    -- First show 1 - m/(m+k) = k/(m+k), then the rest follows like case 1
    have hmk : (↑m + ↑k : ℝ) ≠ 0 := by norm_cast; omega
    have hk : (↑k : ℝ) ≠ 0 := by norm_cast; omega
    have h1 : (1 : ℝ) - ↑m / (↑m + ↑k) = ↑k / (↑m + ↑k) := by
      field_simp [hmk]
      ring
    rw [h1]
    field_simp [hmk, hk]
    -- `field_simp` closes the goal.

/-! ### F Infrastructure: Binary Distributions and Uniform Entropy

Moved from later in the file (originally lines 1457-1750) to avoid forward references.
These definitions and theorems are needed by `faddeev_splitBoth_uniform` below.
-/

private theorem one_div_le_one_of_posNat {m : ℕ} (hm : 0 < m) : (1 : ℝ) / m ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast (Nat.succ_le_iff.2 hm)
  simpa [one_div] using (inv_le_one_of_one_le₀ hm1)

private noncomputable def binaryOneDiv (m : ℕ) (hm : 0 < m) : ProbVec 2 :=
  binaryDist ((1 : ℝ) / m) (by positivity) (one_div_le_one_of_posNat hm)

@[simp] private theorem binaryOneDiv_apply_zero (m : ℕ) (hm : 0 < m) :
    (binaryOneDiv m hm).1 0 = (1 : ℝ) / m := by
  simp [binaryOneDiv, binaryDist]

@[simp] private theorem binaryOneDiv_apply_one (m : ℕ) (hm : 0 < m) :
    (binaryOneDiv m hm).1 1 = 1 - (1 : ℝ) / m := by
  simp [binaryOneDiv, binaryDist]

@[simp] private theorem binaryOneDiv_congr (m : ℕ) (hm hm' : 0 < m) :
    binaryOneDiv m hm = binaryOneDiv m hm' := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [binaryOneDiv, binaryDist]

private theorem one_sub_one_div_mul_uniform (m : ℕ) (hm : 1 < m) :
    (1 - (1 : ℝ) / m) * ((1 : ℝ) / (m - 1)) = (1 : ℝ) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hm))
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hm))
  have hm1le : 1 ≤ m := Nat.succ_le_iff.2 (Nat.lt_trans Nat.zero_lt_one hm)
  rw [one_sub_div (a := (1 : ℝ)) (b := (m : ℝ)) hm0]
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub hm1le).symm
  have hm1' : (↑m - 1 : ℝ) ≠ 0 := by
    simpa [hcast] using hm1
  field_simp [hm0, hm1', hcast]

private theorem one_div_mul_one_div (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((1 : ℝ) / m) * ((1 : ℝ) / n) = (1 : ℝ) / (m * n) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hm0, hn0]

private theorem one_sub_one_div_mul_uniform_mul (m n : ℕ) (hm : 1 < m) (hn : 0 < n) :
    (1 - (1 : ℝ) / m) * ((1 : ℝ) / ((m - 1) * n)) = (1 : ℝ) / (m * n) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hm))
  have hm1le : 1 ≤ m := Nat.succ_le_iff.2 (Nat.lt_trans Nat.zero_lt_one hm)
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hm))
  have hm1' : (↑m - 1 : ℝ) ≠ 0 := by
    have hcast : ((m - 1 : ℕ) : ℝ) = (↑m - 1 : ℝ) := by
      simpa using (Nat.cast_sub hm1le)
    simpa [hcast] using hm1
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hmn0 : ((↑m - 1) * (↑n) : ℝ) ≠ 0 := mul_ne_zero hm1' hn0
  rw [one_sub_div (a := (1 : ℝ)) (b := (m : ℝ)) hm0]
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub hm1le).symm
  field_simp [hm0, hmn0, hcast]

private noncomputable def F (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  E.H (uniformDist n hn)

@[simp] private theorem uniformDist_congr (n : ℕ) (hn hn' : 0 < n) :
    uniformDist n hn = uniformDist n hn' := by
  apply Subtype.ext
  funext i
  rfl

private theorem H_cast (E : FaddeevEntropy) {n n' : ℕ} (h : n = n') (p : ProbVec n) :
    E.H (cast (congrArg ProbVec h) p) = E.H p := by
  cases h
  rfl

private theorem cast_apply_probVec {n n' : ℕ} (h : n = n') (p : ProbVec n) (i : Fin n') :
    (cast (congrArg ProbVec h) p).1 i = p.1 (i.cast h.symm) := by
  cases h
  rfl

private theorem cast_uniformDist {n n' : ℕ} (hn : 0 < n) (h : n = n') :
    cast (congrArg ProbVec h) (uniformDist n hn) = uniformDist n' (by simpa [h] using hn) := by
  cases h
  simp

private theorem splitFirst_cast_right {n m m' : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) (h : m = m') :
    cast (congrArg ProbVec (congrArg (fun t => n + t) h)) (splitFirst (n := n) (m := m) p q) =
      splitFirst (n := n) (m := m') p (cast (congrArg ProbVec h) q) := by
  cases h
  rfl

private theorem F_congr (E : FaddeevEntropy) {n : ℕ} (hn hn' : 0 < n) :
    F E n hn = F E n hn' := by
  unfold F
  exact congrArg E.H (uniformDist_congr n hn hn')

/-! ### Recursion for `F` coming from splitting `(1/m, (m-1)/m)` -/

private theorem uniformDist_eq_split_second (m : ℕ) (hm0 : 0 < m) (hm : 1 < m) :
    splitFirst (n := 1) (m := m - 1)
        (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
        (uniformDist (m - 1) (Nat.sub_pos_of_lt hm))
      =
    uniformDist (1 + (m - 1)) (by
      simp [Nat.one_add]) := by
  classical
  have hlen : 1 + (m - 1) = m := by
    simpa [Nat.one_add] using (Nat.succ_pred_eq_of_pos hm0)
  -- Extensionality over coordinates.
  apply Subtype.ext
  funext i
  have hi_le : (i : ℕ) ≤ m - 1 := by
    have : (i : ℕ) < (m - 1).succ := by
      simpa [Nat.one_add] using i.isLt
    exact Nat.le_of_lt_succ this
  rcases lt_or_eq_of_le hi_le with hi_lt | hi_eq
  · -- split block: value is `(1 - 1/m) * (1/(m-1)) = 1/m`
    let j : Fin (m - 1) := ⟨i.1, hi_lt⟩
    have hj : i = (Fin.castAdd 1 j).cast (Nat.add_comm (m - 1) 1) := by
      ext
      simp [j]
    have hu :
        (uniformDist (1 + (m - 1)) (by
          simp [Nat.one_add])).1 i = (1 : ℝ) / m := by
      simp [uniformDist, hlen]
    -- Evaluate the split distribution at `i`.
    have hsplit :
        (splitFirst (n := 1) (m := m - 1)
              (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
              (uniformDist (m - 1) (Nat.sub_pos_of_lt hm))).1 i = (1 : ℝ) / m := by
      -- Use the coordinate formula for the split block and close with the arithmetic lemma.
      have harith :
          ((1 : ℝ) - ((m : ℝ)⁻¹)) * ((m - 1 : ℕ) : ℝ)⁻¹ = (m : ℝ)⁻¹ := by
        have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
          have hm1le : 1 ≤ m := Nat.succ_le_iff.2 (Nat.lt_trans Nat.zero_lt_one hm)
          simpa using (Nat.cast_sub hm1le).symm
        simpa [one_div, hcast] using (one_sub_one_div_mul_uniform (m := m) hm)
      simpa [hj, splitFirst_castAdd, permute_apply, binaryOneDiv, binaryDist, splitFirst, uniformDist, one_div]
        using harith
    simpa [hu] using hsplit
  · -- tail index: value is `1/m`
    have hi :
        i = (Fin.natAdd (m - 1) (0 : Fin 1)).cast (Nat.add_comm (m - 1) 1) := by
      ext
      simp [hi_eq]
    have hu :
        (uniformDist (1 + (m - 1)) (by
          simp [Nat.one_add])).1 i = (1 : ℝ) / m := by
      simp [uniformDist, hlen]
    have hsplit :
        (splitFirst (n := 1) (m := m - 1)
              (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
              (uniformDist (m - 1) (Nat.sub_pos_of_lt hm))).1 i = (1 : ℝ) / m := by
      -- This is the tail index, so `splitFirst` returns the original `p₁` term.
      -- Use the `natAdd` evaluation lemma, then compute the swapped binary coordinate.
      rw [hi]
      -- `splitFirst_natAdd` gives `p.1 (0 : Fin 1).succ = p.1 1` at this tail index.
      -- We then compute the swapped binary coordinate (so `p.1 1 = (binaryOneDiv m hm0).1 0 = 1/m`).
      have :=
        splitFirst_natAdd
          (p := permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
          (q := uniformDist (m - 1) (Nat.sub_pos_of_lt hm))
          (n := 1) (m := m - 1) (i := (0 : Fin 1))
      -- `simp` is safer than `simpa` here: we want controlled rewriting, not deep normalization of indices.
      -- The goal is just the value of the swapped binary distribution at index `1`.
      simpa [permute_apply, binaryOneDiv, binaryDist, one_div] using this
    simpa [hu] using hsplit

private theorem F_succ_eq (E : FaddeevEntropy) (m : ℕ) (hm : 1 < m) :
    F E m (Nat.lt_trans Nat.zero_lt_one hm)
      =
    E.H (binaryOneDiv m (Nat.lt_trans Nat.zero_lt_one hm))
      + (1 - (1 : ℝ) / m) * F E (m - 1) (Nat.sub_pos_of_lt hm) := by
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  have hm2 : 2 ≤ m := Nat.succ_le_iff.2 hm
  rcases lt_or_eq_of_le hm2 with hm3 | rfl
  · -- `2 < m`, so `m-1 ≥ 2` and the splitting lemma applies
    -- rewrite `F m` using the explicit split representation of `uniformDist m`
    have hF :
        F E m hm0 =
          E.H
              (splitFirst (n := 1) (m := m - 1)
                (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
                (uniformDist (m - 1) (Nat.sub_pos_of_lt hm))) := by
      -- Reduce away the bookkeeping casts by splitting on `m` (so that `m-1` is definitional).
      cases m with
      | zero => cases hm0
      | succ m =>
        -- `uniformDist_eq_split_second` lives in arity `1+m`; transport `uniformDist (m+1)` across
        -- `Nat.one_add` so the types match.
        have hpos : 0 < 1 + m := by
          simp [Nat.one_add]
        have hm0' : 0 < 1 + m := by
          simp [Nat.one_add]
        have hNat : Nat.succ m = 1 + m := (Nat.one_add m).symm
        have hSplit :
            E.H (uniformDist (1 + m) hpos) =
              E.H
                (splitFirst (n := 1) (m := Nat.succ m - 1)
                  (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv (Nat.succ m) hm0))
                  (uniformDist (Nat.succ m - 1) (Nat.sub_pos_of_lt hm))) := by
          simpa using (congrArg E.H (uniformDist_eq_split_second (m := Nat.succ m) hm0 hm)).symm

        have hCastUD :
            cast (congrArg ProbVec hNat) (uniformDist (Nat.succ m) hm0) = uniformDist (1 + m) hm0' := by
          simpa [hm0'] using (cast_uniformDist (hn := hm0) (h := hNat))
        have hCastE : E.H (uniformDist (Nat.succ m) hm0) = E.H (uniformDist (1 + m) hm0') := by
          have h1 :
              E.H (cast (congrArg ProbVec hNat) (uniformDist (Nat.succ m) hm0)) =
                E.H (uniformDist (1 + m) hm0') := congrArg E.H hCastUD
          have h2 :
              E.H (cast (congrArg ProbVec hNat) (uniformDist (Nat.succ m) hm0)) =
                E.H (uniformDist (Nat.succ m) hm0) := H_cast (E := E) (h := hNat) (p := uniformDist (Nat.succ m) hm0)
          exact h2.symm.trans h1

        have hProof : E.H (uniformDist (1 + m) hm0') = E.H (uniformDist (1 + m) hpos) := by
          exact congrArg E.H (uniformDist_congr (n := 1 + m) hm0' hpos)

        have : E.H (uniformDist (Nat.succ m) hm0) =
            E.H
              (splitFirst (n := 1) (m := Nat.succ m - 1)
                (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv (Nat.succ m) hm0))
                (uniformDist (Nat.succ m - 1) (Nat.sub_pos_of_lt hm))) := by
          exact hCastE.trans (hProof.trans hSplit)
        simpa [F] using this
    have hp0 :
        0 <
          (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)).1 0 := by
      -- first entry of the swapped binary is `1 - 1/m`
      have hm' : (1 : ℝ) < m := by
        exact_mod_cast hm
      have hdiv : (1 : ℝ) / m < 1 := by
        simpa using (one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := (m : ℝ)) (by norm_num) hm')
      -- `0 < 1 - (1/m)`
      have : 0 < (1 : ℝ) - (1 : ℝ) / m := sub_pos.mpr hdiv
      simpa [permute_apply, binaryOneDiv_apply_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- apply the splitting lemma (Lemma 5) in the head-positive form, rewriting the arity as `((m-1)-2)+2`
    have hsplit :
        E.H
            (splitFirst (n := 1) (m := m - 1)
              (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
              (uniformDist (m - 1) (Nat.sub_pos_of_lt hm)))
          =
        E.H (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
          +
          (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)).1 0
            * E.H (uniformDist (m - 1) (Nat.sub_pos_of_lt hm)) := by
      -- Make `m - 1 = (m - 3) + 2` definitional by destructing `m = k+3`.
      cases m with
      | zero => cases hm0
      | succ m1 =>
        cases m1 with
        | zero =>
          -- `m = 1` contradicts `2 < m`.
          cases ((by decide : ¬ (2 < 1)) hm3)
        | succ m2 =>
          cases m2 with
          | zero =>
            -- `m = 2` contradicts `2 < m`.
            cases ((by decide : ¬ (2 < 2)) hm3)
          | succ k =>
            -- `m = k+3`, so `m-3 = k` and `m-1 = k+2` are definitional.
            simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              faddeev_splitFirst_headPos (E := E) (n := 1) (m := k)
                (p := permute (Equiv.swap (0 : Fin 2) 1)
                  (binaryOneDiv (Nat.succ (Nat.succ (Nat.succ k))) hm0))
                (q := uniformDist (Nat.succ (Nat.succ k)) (Nat.sub_pos_of_lt hm))
                (hp0 := hp0)
                (hq := by
                  simp [uniformDist_apply] ; positivity)
    have hsym :
        E.H (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)) =
          E.H (binaryOneDiv m hm0) := by
      simpa using (E.symmetry (binaryOneDiv m hm0) (Equiv.swap (0 : Fin 2) 1))
    have hp0val :
        (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)).1 0 = 1 - (1 : ℝ) / m := by
      simp [permute_apply, binaryOneDiv_apply_one]
    -- combine
    calc
      F E m hm0
          = E.H
              (splitFirst (n := 1) (m := m - 1)
                (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0))
                (uniformDist (m - 1) (Nat.sub_pos_of_lt hm))) := hF
      _ = E.H (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)) +
            (permute (Equiv.swap (0 : Fin 2) 1) (binaryOneDiv m hm0)).1 0 *
              E.H (uniformDist (m - 1) (Nat.sub_pos_of_lt hm)) := hsplit
      _ = E.H (binaryOneDiv m hm0) + (1 - (1 : ℝ) / m) * F E (m - 1) (Nat.sub_pos_of_lt hm) := by
            -- rewrite the binary term by symmetry, then substitute the explicit coefficient.
            -- Finally unfold `F` in the tail term.
            simp [F, hsym]
  · -- `m = 2`, the statement reduces to normalization and `F(1)=0`
    have hF2 : F E 2 (by decide : 0 < (2 : ℕ)) = 1 := by
      simp [F, faddeev_F2_eq_one]
    have hF1 : F E 1 (by decide : 0 < (1 : ℕ)) = 0 := by
      simp [F, faddeev_F1_eq_zero]
    -- `binaryOneDiv 2` is `binaryUniform`
    have hbin : E.H (binaryOneDiv 2 (by decide : 0 < (2 : ℕ))) = 1 := by
      -- `binaryOneDiv 2` has `p = 1/2`
      have : binaryOneDiv 2 (by decide : 0 < (2 : ℕ)) = binaryUniform := by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp [binaryOneDiv, binaryUniform, binaryDist]
      simpa [this] using (E.normalization : E.H binaryUniform = 1)
    -- finish
    -- (1 - 1/2) * F(1) = 0
    nlinarith [hF2, hF1, hbin]

/-! ### splitBoth: Strong Additivity for a Two-Way Split -/

/-- **Entropy formula for `splitBoth`** (head-positive form).

This is the "strong additivity" / chain rule specialized to a two-way refinement:
refine the first outcome of a binary distribution by `q1`, and the second outcome by `q2`.

The proof is by reducing `splitBoth` to two applications of `splitFirst` plus symmetry:
1. swap the binary outcomes of `p` and split the (now-head) probability `p₁` by `q2`;
2. rotate so that `p₀` becomes the head again;
3. split the head by `q1`.
-/
private theorem faddeev_splitBoth_headPos (E : FaddeevEntropy) {m k : ℕ}
    (p : ProbVec 2) (q1 : ProbVec (m + 2)) (q2 : ProbVec (k + 2))
    (hp0 : 0 < p.1 0) (hp1 : 0 < p.1 1)
    (hq1 : 0 < q1.1 0 + q1.1 1) (hq2 : 0 < q2.1 0 + q2.1 1) :
    E.H (splitBoth p q1 q2) = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2 := by
  classical
  -- Step 1: split the second probability `p₁` by swapping the binary outcomes.
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let pSwap : ProbVec 2 := permute σ p
  have hpSwap0 : 0 < pSwap.1 0 := by
    simpa [pSwap, permute_apply, σ] using hp1
  have hpSwapH : E.H pSwap = E.H p := by
    simpa [pSwap] using E.symmetry p σ
  have hpSwap0_val : pSwap.1 0 = p.1 1 := by
    simp [pSwap, permute_apply, σ]
  have hpSwap1_val : pSwap.1 1 = p.1 0 := by
    simp [pSwap, permute_apply, σ]

  -- r2 : (p₁·q2₀, ..., p₁·q2_{k+1}, p₀)
  set r2 : ProbVec (1 + (k + 2)) := splitFirst (n := 1) (m := k + 2) pSwap q2 with hr2
  have hHr2 : E.H r2 = E.H p + p.1 1 * E.H q2 := by
    have h :=
      faddeev_splitFirst_headPos (E := E) (n := 1) (m := k)
        (p := pSwap) (q := q2) (hp0 := hpSwap0) (hq := hq2)
    -- rewrite `H pSwap` and `pSwap.1 0`
    simpa [hr2, hpSwapH, hpSwap0_val] using h

  -- Step 2: rotate so that the tail `p₀` becomes the head again.
  have hlen : 1 + (k + 2) = k + 3 := by omega
  set r2c : ProbVec (k + 3) := cast (congrArg ProbVec hlen) r2 with hr2c
  let rot : Equiv.Perm (Fin (k + 3)) := finRotate (k + 3)
  set pBase : ProbVec (k + 3) := permute rot r2c with hpBase

  have hpBaseH : E.H pBase = E.H r2 := by
    calc
      E.H pBase = E.H r2c := by
        simpa [hpBase] using (E.symmetry r2c rot)
      _ = E.H r2 := by
        simpa [r2c] using (H_cast E hlen r2)

  -- Identify the head and tail coordinates of `pBase`.
  have hpBase0 : pBase.1 0 = p.1 0 := by
    have hrot_last : rot (Fin.last (k + 2)) = (0 : Fin (k + 3)) := by
      dsimp [rot]
      exact finRotate_last (n := k + 2)
    have hrot_inv0 : rot⁻¹ (0 : Fin (k + 3)) = Fin.last (k + 2) := by
      -- Apply `rot⁻¹` to `rot (last) = 0`.
      simpa using congrArg (fun x => rot⁻¹ x) hrot_last
    have hr2_last : r2.1 ((Fin.last (k + 2)).cast hlen.symm) = p.1 0 := by
      have ht :
          r2.1 ((Fin.natAdd (k + 2) (0 : Fin 1)).cast (Nat.add_comm (k + 2) 1)) = pSwap.1 1 := by
        simpa [hr2] using
          (splitFirst_natAdd (p := pSwap) (q := q2) (n := 1) (m := k + 2) (i := (0 : Fin 1)))
      have hidx :
          ((Fin.last (k + 2)).cast hlen.symm) =
            ((Fin.natAdd (k + 2) (0 : Fin 1)).cast (Nat.add_comm (k + 2) 1)) := by
        ext
        simp
      simpa [hidx, hpSwap1_val] using ht
    calc
      pBase.1 0 = r2c.1 (rot⁻¹ 0) := by
        simp [hpBase, permute_apply]
      _ = r2c.1 (Fin.last (k + 2)) := by
        simp [hrot_inv0]
      _ = r2.1 ((Fin.last (k + 2)).cast hlen.symm) := by
        simpa [r2c] using (cast_apply_probVec hlen r2 (Fin.last (k + 2)))
      _ = p.1 0 := hr2_last

  have hpBase_succ (j : Fin (k + 2)) :
      pBase.1 (Fin.succ j) = p.1 1 * q2.1 j := by
    have hrot : rot (Fin.castSucc j) = Fin.succ j := by
      dsimp [rot]
      exact finRotate_of_lt (n := k + 2) (k := j.1) (h := j.isLt)
    have hrot_inv : rot⁻¹ (Fin.succ j) = Fin.castSucc j := by
      simpa using (congrArg (fun x => rot⁻¹ x) hrot).symm
    have hr2_split :
        r2.1 ((Fin.castAdd 1 j).cast (Nat.add_comm (k + 2) 1)) = pSwap.1 0 * q2.1 j := by
      simp [hr2, splitFirst_castAdd]
    have hidx :
        ((Fin.castSucc j).cast hlen.symm) = ((Fin.castAdd 1 j).cast (Nat.add_comm (k + 2) 1)) := by
      ext
      simp
    calc
      pBase.1 (Fin.succ j) = r2c.1 (rot⁻¹ (Fin.succ j)) := by
        simp [hpBase, permute_apply]
      _ = r2c.1 (Fin.castSucc j) := by
        simp [hrot_inv]
      _ = r2.1 ((Fin.castSucc j).cast hlen.symm) := by
        simpa [r2c] using (cast_apply_probVec hlen r2 (Fin.castSucc j))
      _ = pSwap.1 0 * q2.1 j := by
        simpa [hidx] using hr2_split
      _ = p.1 1 * q2.1 j := by
        simp [hpSwap0_val]

  have hpBase0_pos : 0 < pBase.1 0 := by
    simpa [hpBase0] using hp0

  -- Step 3: split the head `p₀` by `q1`.
  have hsplit3 :
      E.H (splitFirst (n := k + 2) (m := m + 2) pBase q1)
        = E.H pBase + pBase.1 0 * E.H q1 := by
    simpa using
      faddeev_splitFirst_headPos (E := E) (n := k + 2) (m := m)
        (p := pBase) (q := q1) (hp0 := hpBase0_pos) (hq := hq1)

  -- `splitBoth p q1 q2` is (up to a harmless cast) `splitFirst pBase q1`.
  have hlen3 : (k + 2) + (m + 2) = (m + 2) + (k + 2) := Nat.add_comm (k + 2) (m + 2)
  have hsb :
      cast (congrArg ProbVec hlen3) (splitFirst (n := k + 2) (m := m + 2) pBase q1)
        = splitBoth p q1 q2 := by
    apply Subtype.ext
    funext i
    have hcast :
        (cast (congrArg ProbVec hlen3) (splitFirst (n := k + 2) (m := m + 2) pBase q1)).1 i
          = (splitFirst (n := k + 2) (m := m + 2) pBase q1).1 (i.cast hlen3.symm) := by
      simpa using cast_apply_probVec hlen3 (splitFirst (n := k + 2) (m := m + 2) pBase q1) i
    by_cases hi : i.1 < m + 2
    ·
      let iSplit : Fin (m + 2) := ⟨i.1, hi⟩
      have hidx :
          (i.cast hlen3.symm) =
            ((Fin.castAdd (k + 2) iSplit).cast (Nat.add_comm (m + 2) (k + 2))) := by
        ext
        simp [iSplit]
      have hval :
          (splitFirst (n := k + 2) (m := m + 2) pBase q1).1 (i.cast hlen3.symm)
            = pBase.1 0 * q1.1 iSplit := by
        simpa [hidx] using
          (splitFirst_castAdd (p := pBase) (q := q1) (n := k + 2) (m := m + 2) (i := iSplit))
      calc
        (cast (congrArg ProbVec hlen3) (splitFirst (n := k + 2) (m := m + 2) pBase q1)).1 i
            = pBase.1 0 * q1.1 iSplit := by
              simp [hcast, hval]
        _ = p.1 0 * q1.1 iSplit := by
              simp [hpBase0]
        _ = (splitBoth p q1 q2).1 i := by
              simp [splitBoth, hi, iSplit]
    ·
      have hle : m + 2 ≤ i.1 := Nat.not_lt.mp hi
      let iTail : Fin (k + 2) :=
        ⟨i.1 - (m + 2), Nat.sub_lt_left_of_lt_add hle i.isLt⟩
      have hidx :
          (i.cast hlen3.symm) =
            ((Fin.natAdd (m + 2) iTail).cast (Nat.add_comm (m + 2) (k + 2))) := by
        ext
        have hsum : (m + 2) + (i.1 - (m + 2)) = i.1 := by
          have h' : (i.1 - (m + 2)) + (m + 2) = i.1 := Nat.sub_add_cancel hle
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
        simp [iTail, hsum]
      have hval :
          (splitFirst (n := k + 2) (m := m + 2) pBase q1).1 (i.cast hlen3.symm)
            = pBase.1 (Fin.succ iTail) := by
        simpa [hidx] using
          (splitFirst_natAdd (p := pBase) (q := q1) (n := k + 2) (m := m + 2) (i := iTail))
      calc
        (cast (congrArg ProbVec hlen3) (splitFirst (n := k + 2) (m := m + 2) pBase q1)).1 i
            = pBase.1 (Fin.succ iTail) := by
              simp [hcast, hval]
        _ = p.1 1 * q2.1 iTail := by
              simpa using hpBase_succ iTail
        _ = (splitBoth p q1 q2).1 i := by
              simp [splitBoth, hi, iTail]

  have hHsb :
      E.H (splitBoth p q1 q2) = E.H (splitFirst (n := k + 2) (m := m + 2) pBase q1) := by
    have hcastH :
        E.H (cast (congrArg ProbVec hlen3) (splitFirst (n := k + 2) (m := m + 2) pBase q1))
          = E.H (splitFirst (n := k + 2) (m := m + 2) pBase q1) := by
      simpa using
        H_cast E hlen3 (splitFirst (n := k + 2) (m := m + 2) pBase q1)
    calc
      E.H (splitBoth p q1 q2)
          = E.H (cast (congrArg ProbVec hlen3)
              (splitFirst (n := k + 2) (m := m + 2) pBase q1)) := by
            exact congrArg E.H hsb.symm
      _ = E.H (splitFirst (n := k + 2) (m := m + 2) pBase q1) := hcastH

  have hHpBase : E.H pBase = E.H p + p.1 1 * E.H q2 := by
    calc
      E.H pBase = E.H r2 := hpBaseH
      _ = E.H p + p.1 1 * E.H q2 := hHr2

  -- Assemble.
  calc
    E.H (splitBoth p q1 q2)
        = E.H (splitFirst (n := k + 2) (m := m + 2) pBase q1) := hHsb
    _ = E.H pBase + pBase.1 0 * E.H q1 := hsplit3
    _ = (E.H p + p.1 1 * E.H q2) + p.1 0 * E.H q1 := by
          simp [hHpBase, hpBase0]
    _ = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2 := by ring

/-! ### The main multiplicativity lemma `F(m*n) = F(m) + F(n)` -/

/-- **Special case: Entropy splitting for uniform distributions.**

For uniform distributions, the splitBoth chain rule takes the form:
H(uniform(m+k)) = H(binaryDist(m/(m+k))) + (m/(m+k))·H(uniform(m)) + (k/(m+k))·H(uniform(k))

This is precisely what's needed to prove ηE_rat_eq_ηSh. -/
theorem faddeev_splitBoth_uniform (E : FaddeevEntropy) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    let p := binaryDist ((m : ℝ) / (m + k))
        (div_nonneg (Nat.cast_nonneg m) (by positivity))
        (div_le_one_of_le₀ (by simp) (by positivity))
    E.H (uniformDist (m + k) (Nat.add_pos_left hm k)) =
      E.H p + ((m : ℝ) / (m + k)) * E.H (uniformDist m hm) +
             ((k : ℝ) / (m + k)) * E.H (uniformDist k hk) := by
  intro p
  -- Use the fact that uniform(m+k) = splitBoth(p, uniform(m), uniform(k))
  have hsb := splitBoth_uniform_eq_uniform hm hk
  rw [← hsb]
  -- The p₁ component of binaryDist(m/(m+k)) is 1 - m/(m+k) = k/(m+k)
  have hp1 : p.1 1 = (k : ℝ) / (m + k) := by
    show (1 : ℝ) - ↑m / (↑m + ↑k) = ↑k / (↑m + ↑k)
    have hmk : (↑m + ↑k : ℝ) ≠ 0 := by norm_cast; omega
    field_simp [hmk]
    ring
  -- Now we need to show the chain rule for splitBoth with these specific distributions
  -- Handle cases based on m and k
  by_cases hm2 : m = 1
  · -- m = 1: uniformDist 1 has H = 0 (from faddeev_F1_eq_zero)
    subst hm2
    simp only [Nat.cast_one, one_div]
    -- uniformDist 1 has entropy 0
    have hU1 : E.H (uniformDist 1 hm) = 0 := by
      have hcongr : uniformDist 1 hm = uniformDist 1 (by norm_num : 0 < 1) := by
        apply Subtype.ext; funext i; rfl
      rw [hcongr]
      exact faddeev_F1_eq_zero E
    rw [hU1, mul_zero, add_zero]
    -- Goal: E.H (splitBoth p (uniformDist 1) (uniformDist k)) = E.H p + p.1 1 * E.H (uniformDist k)

    -- After subst m=1, p = binaryDist ((1:ℝ)/(1+k)) ...
    -- Simplify notation: 1/x = x⁻¹ after simp
    simp only [Nat.cast_one, one_div] at hsb hp1 ⊢

    -- Now hsb : splitBoth p (uniformDist 1 hm) (uniformDist k hk) = uniformDist (1 + k) ...
    rw [hsb]

    -- Goal: E.H (uniformDist (1 + k)) = E.H p + p.1 1 * E.H (uniformDist k)
    -- Use F_succ_eq: After subst m=1, both binaryOneDiv (1+k) and p are binaryDist ((1+k)⁻¹)
    -- with different proof parameters, equal by proof irrelevance

    -- Need 1 < 1 + k to apply F_succ_eq
    have h_lt : 1 < 1 + k := Nat.lt_add_of_pos_right hk
    have h_pos : 0 < 1 + k := Nat.add_pos_left Nat.zero_lt_one k

    -- After simp, p has the form binaryDist ((1+k)⁻¹) ... which equals binaryOneDiv (1+k)
    -- Show p = binaryOneDiv (1 + k) by Subtype.ext
    have hp_eq : p = binaryOneDiv (1 + k) h_pos := by
      apply Subtype.ext
      funext i
      fin_cases i
      · -- i = 0: show p.1 0 = (1+k)⁻¹
        simp only [p, binaryOneDiv, binaryDist]
        norm_num
      · -- i = 1: show p.1 1 = 1 - (1+k)⁻¹
        simp only [p, binaryOneDiv, binaryDist]
        norm_num

    -- Apply F_succ_eq which gives: F E (1+k) = E.H (binaryOneDiv (1+k)) + (1 - (1+k)⁻¹) * F E ((1+k)-1)
    have hF := F_succ_eq E (1 + k) h_lt
    unfold F at hF

    -- First, show the arithmetic equality: (1 + k) - 1 = k
    have h_k_simp : 1 + k - 1 = k := by omega

    -- Show E.H (uniformDist (1+k-1) ...) = E.H (uniformDist k hk)
    -- Use the existing H_cast and cast_uniformDist lemmas
    have h_unif_eq : E.H (uniformDist (1 + k - 1) (Nat.sub_pos_of_lt h_lt)) = E.H (uniformDist k hk) := by
      rw [← H_cast E h_k_simp (uniformDist (1 + k - 1) (Nat.sub_pos_of_lt h_lt))]
      congr 1
      rw [cast_uniformDist (Nat.sub_pos_of_lt h_lt) h_k_simp]

    -- Rewrite in hF
    rw [h_unif_eq] at hF

    -- Unify witnesses for uniformDist (1 + k) on LHS
    have h_unif_lhs : uniformDist (1 + k) (Nat.lt_trans Nat.zero_lt_one h_lt) = uniformDist (1 + k) h_pos := by
      apply Subtype.ext; funext i; rfl

    -- Unify witnesses for binaryOneDiv (1 + k)
    have hbinary_congr : binaryOneDiv (1 + k) (Nat.lt_trans Nat.zero_lt_one h_lt) = binaryOneDiv (1 + k) h_pos := by
      apply Subtype.ext; funext i; rfl

    -- Rewrite both in hF
    rw [h_unif_lhs, hbinary_congr] at hF

    -- Now show that p = binaryOneDiv (1 + k) h_pos and the coefficient matches
    -- After rewrites, hF has: E.H (uniformDist (1+k) h_pos) = E.H (binaryOneDiv (1+k) h_pos) + (1 - (1+k)⁻¹) * E.H (uniformDist k hk)
    -- Goal is: E.H (uniformDist (1 + k)) = E.H p + p.1 1 * E.H (uniformDist k hk)
    -- Rewrite p to binaryOneDiv in the goal
    rw [hp_eq]
    -- After this rewrite, (binaryOneDiv (1 + k) h_pos).1 1 simplifies to k / (1 + k)
    -- Goal has k / (1 + k), hF has 1 - 1 / (1 + k). Show these are equal.
    -- Proof: k / (1 + k) = ((1+k) - 1) / (1+k) = 1 - 1/(1+k)
    have h_coeff : (k : ℝ) / (1 + k) = 1 - 1 / ↑(1 + k) := by
      have hknat : (k : ℝ) = ((1 + k) : ℝ) - 1 := by
        ring
      rw [hknat, sub_div, one_div]
      simp [← hknat]
      -- Goal: (1 + k) / (1 + k) = 1
      have hpos : (0 : ℝ) < 1 + k := by positivity
      exact div_self (ne_of_gt hpos)
    -- Convert the coefficient in hF to match the goal
    rw [← h_coeff] at hF
    exact hF
  · by_cases hk2 : k = 1
    · -- k = 1: uniformDist 1 has H = 0 (from faddeev_F1_eq_zero)
      subst hk2
      have hU1 : E.H (uniformDist 1 hk) = 0 := by
        have hcongr : uniformDist 1 hk = uniformDist 1 (by norm_num : 0 < 1) := by
          apply Subtype.ext; funext i; rfl
        rw [hcongr]
        exact faddeev_F1_eq_zero E
      -- Use F_succ_eq and symmetry
      -- After k=1 substitution: p = binaryDist(m/(m+1)) has components (m/(m+1), 1/(m+1))
      -- But binaryOneDiv(m+1) has components (1/(m+1), m/(m+1)) - they're swapped!
      -- Use symmetry: E.H(p) = E.H(permute (swap 0 1) p) = E.H(binaryOneDiv(m+1))

      rw [hU1, mul_zero, add_zero]
      simp only [Nat.cast_one, one_div] at hsb hp1 ⊢
      rw [hsb]

      -- Goal: E.H (uniformDist (m + 1)) = E.H p + (m/(m+1)) * E.H (uniformDist m)
      -- Similar to m=1 case but with m and k swapped

      have h_lt : 1 < m + 1 := Nat.lt_add_of_pos_left hm
      have h_pos : 0 < m + 1 := Nat.add_pos_left hm 1

      -- Show that permute (swap 0 1) p = binaryOneDiv (m + 1)
      -- p has components (m/(m+1), 1/(m+1))
      -- binaryOneDiv(m+1) has components (1/(m+1), m/(m+1))
      -- After swapping, permute p has components (1/(m+1), m/(m+1))
      have hp_swap : permute (Equiv.swap (0 : Fin 2) 1) p = binaryOneDiv (m + 1) h_pos := by
        apply Subtype.ext
        funext i
        fin_cases i
        · -- i = 0: (permute p).1 0 = p.1 ((swap 0 1) 0) = p.1 1 = 1 - m/(m+1) = 1/(m+1)
          rw [permute_apply]
          simp [Equiv.swap_apply_left, p, binaryDist, binaryOneDiv, Matrix.cons_val_one]
          -- Goal: 1 - m/(m+1) = (m+1)⁻¹
          have hpos : (0 : ℝ) < m + 1 := by positivity
          field_simp [ne_of_gt hpos]
          ring
        · -- i = 1: (permute p).1 1 = p.1 ((swap 0 1) 1) = p.1 0 = m/(m+1) = 1 - 1/(m+1)
          rw [permute_apply]
          simp [Equiv.swap_apply_right, p, binaryDist, binaryOneDiv, Matrix.cons_val_zero]
          -- Goal: m/(m+1) = 1 - (m+1)⁻¹
          have hpos : (0 : ℝ) < m + 1 := by positivity
          field_simp [ne_of_gt hpos]
          ring

      -- Use symmetry: E.H(p) = E.H(permute ... p)
      have hp_sym : E.H p = E.H (permute (Equiv.swap (0 : Fin 2) 1) p) := (E.symmetry p (Equiv.swap 0 1)).symm
      rw [hp_sym, hp_swap]

      -- Now use F_succ_eq as in the m=1 case
      have hF := F_succ_eq E (m + 1) h_lt
      unfold F at hF

      have h_m_simp : m + 1 - 1 = m := by omega
      have h_unif_eq : E.H (uniformDist (m + 1 - 1) (Nat.sub_pos_of_lt h_lt)) = E.H (uniformDist m hm) := by
        rw [← H_cast E h_m_simp (uniformDist (m + 1 - 1) (Nat.sub_pos_of_lt h_lt))]
        simp

      rw [h_unif_eq] at hF

      have h_unif_lhs : uniformDist (m + 1) (Nat.lt_trans Nat.zero_lt_one h_lt) = uniformDist (m + 1) h_pos := by
        apply Subtype.ext; funext i; rfl

      have hbinary_congr : binaryOneDiv (m + 1) (Nat.lt_trans Nat.zero_lt_one h_lt) = binaryOneDiv (m + 1) h_pos := by
        apply Subtype.ext; funext i; rfl

      rw [h_unif_lhs, hbinary_congr] at hF

      -- Show coefficient: m/(m+1) = 1 - 1/(m+1)
      have h_coeff : (m : ℝ) / (m + 1) = 1 - 1 / ↑(m + 1) := by
        have hmnat : (m : ℝ) = ((m + 1) : ℝ) - 1 := by
          ring
        rw [hmnat, sub_div, one_div]
        simp [← hmnat]
        have hpos : (0 : ℝ) < m + 1 := by positivity
        exact div_self (ne_of_gt hpos)

      rw [← h_coeff] at hF
      exact hF
    · -- m ≥ 2 and k ≥ 2: Requires faddeev_splitBoth (defined below)
      -- Theorem order issue: faddeev_splitBoth is defined later in the file
      -- Would follow from applying faddeev_splitBoth to uniform distributions
      have hm_ge2 : 2 ≤ m := by omega
      have hk_ge2 : 2 ≤ k := by omega
      obtain ⟨m', rfl : m = m' + 2⟩ := Nat.exists_eq_add_of_le' hm_ge2
      obtain ⟨k', rfl : k = k' + 2⟩ := Nat.exists_eq_add_of_le' hk_ge2

      have hp0_pos : 0 < p.1 0 := by
        simp [p, binaryDist]
        have hm' : (0 : ℝ) < (m' + 2 : ℝ) := by positivity
        have hmk : (0 : ℝ) < (m' + 2 + (k' + 2) : ℝ) := by positivity
        exact div_pos hm' hmk

      have hp1_pos : 0 < p.1 1 := by
        rw [hp1]
        have hk' : 0 < k' + 2 := by omega
        have hmk : 0 < m' + 2 + (k' + 2) := by omega
        exact div_pos (by exact_mod_cast hk') (by exact_mod_cast hmk)

      have hq1_pos :
          0 < (uniformDist (m' + 2) hm).1 0 + (uniformDist (m' + 2) hm).1 1 := by
        simp [uniformDist]
        positivity

      have hq2_pos :
          0 < (uniformDist (k' + 2) hk).1 0 + (uniformDist (k' + 2) hk).1 1 := by
        simp [uniformDist]
        positivity

      have hsplit :
          E.H (splitBoth p (uniformDist (m' + 2) hm) (uniformDist (k' + 2) hk)) =
            E.H p + p.1 0 * E.H (uniformDist (m' + 2) hm) +
              p.1 1 * E.H (uniformDist (k' + 2) hk) := by
        simpa using
          faddeev_splitBoth_headPos (E := E) (m := m') (k := k')
            (p := p) (q1 := uniformDist (m' + 2) hm) (q2 := uniformDist (k' + 2) hk)
            (hp0 := hp0_pos) (hp1 := hp1_pos) (hq1 := hq1_pos) (hq2 := hq2_pos)

      have hp0_val : p.1 0 = (m' + 2 : ℝ) / (m' + 2 + (k' + 2)) := by
        simp [p, binaryDist]

      -- Convert the coefficients `p.1 0`, `p.1 1` to the explicit fractions in the statement.
      -- Use rewriting instead of `simp` to avoid heartbeats in this large file.
      have hsplit' := hsplit
      rw [hp0_val, hp1] at hsplit'
      simpa [p] using hsplit'

/-- **Binary entropy formula**: For 0 < m < n, the binary entropy η(m/n) can be expressed
    in terms of F values via the splitting lemma.

    η(m/n) = F(n) - (m/n)·F(m) - ((n-m)/n)·F(n-m)

    This is the key formula connecting binary entropy to uniform entropy (F values). -/
theorem faddeev_binary_entropy_formula (E : FaddeevEntropy) (m n : ℕ)
    (hm_pos : 0 < m) (hn_pos : 0 < n) (hm_lt : m < n) :
    E.H (binaryDist ((m : ℝ) / n)
      (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
      (div_le_one_of_le₀ (by exact_mod_cast (le_of_lt hm_lt)) (Nat.cast_nonneg n))) =
    F E n hn_pos - (m / n) * F E m hm_pos - ((n - m) / n) * F E (n - m) (Nat.sub_pos_of_lt hm_lt) := by
  -- Use faddeev_splitBoth_uniform with m and k = n - m
  have hk_pos : 0 < n - m := Nat.sub_pos_of_lt hm_lt
  have h_add : m + (n - m) = n := Nat.add_sub_cancel' (le_of_lt hm_lt)

  unfold F

  -- Apply faddeev_splitBoth_uniform with k = n - m
  -- This gives: E.H(uniform(m+(n-m))) = E.H(p) + fractions * E.H(uniforms)
  have h_split := faddeev_splitBoth_uniform E hm_pos hk_pos

  -- Unfold the let binding in h_split
  simp only [] at h_split

  -- Use H_cast to show E.H (uniformDist (m + (n-m))) = E.H (uniformDist n)
  have h_unif_eq : E.H (uniformDist (m + (n - m)) (Nat.add_pos_left hm_pos (n - m))) =
                   E.H (uniformDist n hn_pos) := by
    rw [← H_cast E h_add (uniformDist (m + (n - m)) (Nat.add_pos_left hm_pos (n - m)))]
    congr 1
    rw [cast_uniformDist (Nat.add_pos_left hm_pos (n - m)) h_add]

  -- Establish the key real number equality upfront in the exact shape occurring in `h_split`.
  have h_denom : (m : ℝ) + (n - m : ℕ) = n := by
    have h_cast_add : ((m + (n - m) : ℕ) : ℝ) = (m : ℝ) + (n - m : ℕ) :=
      Nat.cast_add m (n - m)
    have h_addR : ((m + (n - m) : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast h_add
    exact h_cast_add.symm.trans h_addR

  -- Show the fractions simplify using h_denom
  have h_m_frac : (m : ℝ) / ((m : ℝ) + (n - m : ℕ)) = m / n := by
    rw [h_denom]
  have h_nm_frac : ((n - m : ℕ) : ℝ) / ((m : ℝ) + (n - m : ℕ)) = ((n - m : ℕ) : ℝ) / n := by
    rw [h_denom]

  -- h_split gives: E.H(uniformDist(m+(n-m))) = E.H(p) + (m/(m+(n-m)))*E.H(uniform m) + ...
  -- We want: E.H(binaryDist(m/n)) = F(n) - (m/n)*F(m) - ((n-m)/n)*F((n-m))
  -- which is: goal = E.H(uniformDist n) - (m/n)*E.H(uniform m) - ((n-m)/n)*E.H(uniform (n-m))

  -- Work directly from h_split using rewrites
  -- Rewrite uniformDist using h_unif_eq
  rw [h_unif_eq] at h_split

  -- h_split now has form:
  -- E.H(uniformDist n) = E.H(binaryDist (m/(m+(n-m))) ...) + (m/n)*E.H(uniform m) + ((n-m)/n)*E.H(uniform (n-m))
  -- The binaryDist with value m/(m+(n-m)) = m/n equals the target binaryDist by proof irrelevance

  -- Show the binaryDist in h_split equals our target binaryDist
  have hp_eq : (binaryDist ((m : ℝ) / ((m : ℝ) + (n - m : ℕ)))
        (div_nonneg (Nat.cast_nonneg m)
          (add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg (n - m))))
        (div_le_one_of_le₀
          (by
            exact le_add_of_nonneg_right (Nat.cast_nonneg (n - m)))
          (add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg (n - m))))) =
      (binaryDist ((m : ℝ) / n)
        (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
        (div_le_one_of_le₀ (Nat.cast_le.mpr (le_of_lt hm_lt)) (Nat.cast_nonneg n))) := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [binaryDist, h_denom]
    · simp [binaryDist, h_denom]

  rw [hp_eq] at h_split
  -- Now rewrite the (non-dependent) coefficient fractions; doing this *after* `hp_eq` avoids rewriting
  -- inside the dependent proof fields of `binaryDist`.
  rw [h_m_frac, h_nm_frac] at h_split
  -- The goal uses the real subtraction form `(n - m) / n = (↑n - ↑m) / ↑n`.
  have hm_le : m ≤ n := le_of_lt hm_lt
  have h_cast_sub : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
    exact (Nat.cast_sub hm_le : ((n - m : ℕ) : ℝ) = (n : ℝ) - m)
  rw [h_cast_sub] at h_split
  -- Align the proof argument of `uniformDist (n - m)` with the one in the goal.
  have h_unif_sub :
      E.H (uniformDist (n - m) hk_pos) =
        E.H (uniformDist (n - m) (Nat.sub_pos_of_lt hm_lt)) := by
    exact
      congrArg E.H
        (uniformDist_congr (n := n - m) (hn := hk_pos) (hn' := Nat.sub_pos_of_lt hm_lt))
  rw [h_unif_sub] at h_split
  linarith [h_split]

/-- **Entropy formula for splitBoth**: H(splitBoth p q₁ q₂) = H(p) + p₀·H(q₁) + p₁·H(q₂)

This is the "generalized strong additivity" that follows from repeated application of recursivity.

**Proof sketch:**
We express splitBoth in terms of splitFirst operations and use faddeev_splitFirst_headPos.
The key observation is that splitBoth p q1 q2 can be constructed by:
1. Split the first outcome of p according to q1, giving intermediate distribution of size m+1
2. Split the last outcome (which is p₁) according to q2
Using symmetry (permutation invariance) allows us to handle step 2 via splitFirst. -/
-- Base case: m = 2, k = 2
private theorem faddeev_splitBoth_2_2 (E : FaddeevEntropy)
    (p : ProbVec 2) (q1 q2 : ProbVec 2)
    (hp0 : 0 < p.1 0) :
    E.H (splitBoth p q1 q2) = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2 := by
  -- splitBoth p q1 q2 = (p₀q1₀, p₀q1₁, p₁q2₀, p₁q2₁) : ProbVec 4
  set sb := splitBoth p q1 q2 with hsb

  -- Step 1: Compute the first two probabilities of sb
  have hsb0 : sb.1 0 = p.1 0 * q1.1 0 := splitBoth_left p q1 q2 0
  have hsb1 : sb.1 1 = p.1 0 * q1.1 1 := splitBoth_left p q1 q2 1

  -- Step 2: Sum of first two = p₀
  have hsum01 : sb.1 0 + sb.1 1 = p.1 0 := by
    rw [hsb0, hsb1, ← mul_add]
    have hq1_sum : q1.1 0 + q1.1 1 = 1 := by simpa [Fin.sum_univ_two] using q1.sum_eq_one
    rw [hq1_sum, mul_one]

  have hsum_pos : 0 < sb.1 0 + sb.1 1 := by rw [hsum01]; exact hp0

  -- Step 3: The normalized binary of (sb.1 0, sb.1 1) equals q1
  have hnorm : normalizeBinary (sb.1 0) (sb.1 1) (sb.nonneg 0) (sb.nonneg 1) hsum_pos = q1 := by
    apply Subtype.ext
    funext i
    have hp0ne : p.1 0 ≠ 0 := ne_of_gt hp0
    have hq1_sum : q1.1 0 + q1.1 1 = 1 := by simpa [Fin.sum_univ_two] using q1.sum_eq_one
    -- After rewriting with hsb0, hsb1, the denominator becomes p₀*(q1₀+q1₁) = p₀*1 = p₀
    have hden : sb.1 0 + sb.1 1 = p.1 0 := hsum01
    fin_cases i
    · -- Goal: sb.1 0 / (sb.1 0 + sb.1 1) = q1.1 0
      simp only [normalizeBinary]
      rw [hden, hsb0]
      -- (p₀*q1₀) / p₀ = q1₀
      exact mul_div_cancel_left₀ (q1.1 0) hp0ne
    · -- Goal: sb.1 1 / (sb.1 0 + sb.1 1) = q1.1 1
      simp only [normalizeBinary]
      rw [hden, hsb1]
      -- (p₀*q1₁) / p₀ = q1₁
      exact mul_div_cancel_left₀ (q1.1 1) hp0ne

  -- Step 4: Apply recursivity to group first two outcomes
  have hrec1 := E.recursivity (n := 2) sb hsum_pos
  rw [hnorm, hsum01] at hrec1
  -- hrec1 : E.H sb = E.H (groupFirstTwo sb hsum_pos) + p.1 0 * E.H q1

  -- Step 5: g1 := groupFirstTwo sb hsum_pos is a ternary distribution (p₀, p₁*q2₀, p₁*q2₁)
  set g1 := groupFirstTwo sb hsum_pos with hg1

  -- Compute the entries of g1
  -- g1.1 i = if i.1 = 0 then sb.1 0 + sb.1 1 else sb.1 ⟨i.1 + 1, _⟩
  have hg1_0 : g1.1 0 = p.1 0 := by
    change (if (0 : Fin 3).1 = 0 then sb.1 0 + sb.1 1
            else sb.1 ⟨(0 : Fin 3).1 + 1, Nat.succ_lt_succ (0 : Fin 3).isLt⟩) = p.1 0
    simp only [Fin.val_zero, ↓reduceIte]
    exact hsum01
  have hg1_1 : g1.1 1 = p.1 1 * q2.1 0 := by
    change (if (1 : Fin 3).1 = 0 then sb.1 0 + sb.1 1
            else sb.1 ⟨(1 : Fin 3).1 + 1, Nat.succ_lt_succ (1 : Fin 3).isLt⟩) = p.1 1 * q2.1 0
    simp
    exact splitBoth_right p q1 q2 0
  have hg1_2 : g1.1 2 = p.1 1 * q2.1 1 := by
    change (if (2 : Fin 3).1 = 0 then sb.1 0 + sb.1 1
            else sb.1 ⟨(2 : Fin 3).1 + 1, Nat.succ_lt_succ (2 : Fin 3).isLt⟩) = p.1 1 * q2.1 1
    have h2ne0 : (2 : Fin 3).1 ≠ 0 := by decide
    simp only [h2ne0, ↓reduceIte]
    exact splitBoth_right p q1 q2 1

  -- Step 6: Handle two cases: p.1 1 > 0 or p.1 1 = 0
  by_cases hp1_pos : 0 < p.1 1
  · -- Case: p.1 1 > 0. Use symmetry and second recursivity.
    -- Define cyclic permutation σ : Fin 3 → Fin 3 sending (0,1,2) → (2,0,1)
    -- so that σ⁻¹ sends (0,1,2) → (1,2,0)
    let σ : Equiv.Perm (Fin 3) := Equiv.mk
      (fun i => match i with | 0 => 2 | 1 => 0 | 2 => 1)
      (fun i => match i with | 0 => 1 | 1 => 2 | 2 => 0)
      (fun i => by fin_cases i <;> rfl)
      (fun i => by fin_cases i <;> rfl)

    -- permute σ g1 = (p₁*q2₀, p₁*q2₁, p₀)
    -- σ⁻¹(0) = 1, σ⁻¹(1) = 2, σ⁻¹(2) = 0
    have hσinv0 : σ⁻¹ (0 : Fin 3) = 1 := rfl
    have hσinv1 : σ⁻¹ (1 : Fin 3) = 2 := rfl
    have hσinv2 : σ⁻¹ (2 : Fin 3) = 0 := rfl
    have hperm0 : (permute σ g1).1 0 = p.1 1 * q2.1 0 := by
      simp only [permute_apply, hσinv0]; exact hg1_1
    have hperm1 : (permute σ g1).1 1 = p.1 1 * q2.1 1 := by
      simp only [permute_apply, hσinv1]; exact hg1_2
    have hperm2 : (permute σ g1).1 2 = p.1 0 := by
      simp only [permute_apply, hσinv2]; exact hg1_0

    -- Sum of first two in permuted distribution = p₁
    have hq2_sum : q2.1 0 + q2.1 1 = 1 := by simpa [Fin.sum_univ_two] using q2.sum_eq_one
    have hperm_sum01 : (permute σ g1).1 0 + (permute σ g1).1 1 = p.1 1 := by
      rw [hperm0, hperm1, ← mul_add, hq2_sum, mul_one]
    have hperm_sum_pos : 0 < (permute σ g1).1 0 + (permute σ g1).1 1 := by
      rw [hperm_sum01]; exact hp1_pos

    -- By symmetry: E.H g1 = E.H (permute σ g1)
    have hsym : E.H g1 = E.H (permute σ g1) := (E.symmetry g1 σ).symm

    -- Apply recursivity to permute σ g1
    have hrec2 := E.recursivity (n := 1) (permute σ g1) hperm_sum_pos

    -- The normalized binary of first two = q2
    have hp1ne : p.1 1 ≠ 0 := ne_of_gt hp1_pos
    have hnorm2 : normalizeBinary ((permute σ g1).1 0) ((permute σ g1).1 1)
        ((permute σ g1).nonneg 0) ((permute σ g1).nonneg 1) hperm_sum_pos = q2 := by
      apply Subtype.ext
      funext i
      have hden : (permute σ g1).1 0 + (permute σ g1).1 1 = p.1 1 := hperm_sum01
      fin_cases i
      · simp only [normalizeBinary]
        rw [hden, hperm0]
        exact mul_div_cancel_left₀ (q2.1 0) hp1ne
      · simp only [normalizeBinary]
        rw [hden, hperm1]
        exact mul_div_cancel_left₀ (q2.1 1) hp1ne

    rw [hnorm2, hperm_sum01] at hrec2
    -- hrec2 : E.H (permute σ g1) = E.H (groupFirstTwo (permute σ g1) _) + p.1 1 * E.H q2

    -- groupFirstTwo (permute σ g1) = (p₁, p₀), which equals permute (swap 0 1) p
    have hg2 : groupFirstTwo (permute σ g1) hperm_sum_pos = permute (Equiv.swap (0 : Fin 2) 1) p := by
      apply Subtype.ext
      funext i
      fin_cases i
      · -- i = 0: grouped sum = p₁.
        have : (g1.1 (σ⁻¹ (0 : Fin 3)) + g1.1 (σ⁻¹ (1 : Fin 3)) : ℝ) = p.1 1 := by
          rw [hσinv0, hσinv1, hg1_1, hg1_2, ← mul_add, hq2_sum, mul_one]
        simpa [groupFirstTwo, permute_apply, Equiv.swap_apply_left] using this
      · -- i = 1: remaining element = p₀.
        have : (g1.1 (σ⁻¹ (2 : Fin 3)) : ℝ) = p.1 0 := by
          rw [hσinv2, hg1_0]
        simpa [groupFirstTwo, permute_apply, Equiv.swap_apply_right] using this

    -- By symmetry: E.H (permute (swap 0 1) p) = E.H p
    have hsym2 : E.H (permute (Equiv.swap (0 : Fin 2) 1) p) = E.H p := E.symmetry p _

    -- Combine everything
    rw [hg2, hsym2] at hrec2
    rw [hsym, hrec2] at hrec1
    -- hrec1 : E.H sb = (E.H p + p.1 1 * E.H q2) + p.1 0 * E.H q1
    linarith

  · -- Case: p.1 1 = 0. Then p = (1, 0) and g1 = (1, 0, 0).
    have hp1_zero : p.1 1 = 0 := le_antisymm (not_lt.mp hp1_pos) (p.nonneg 1)
    have hp0_one : p.1 0 = 1 := by
      have hsum := p.sum_eq_one
      simp [Fin.sum_univ_two] at hsum
      linarith

    -- p = binaryDist 1 (1, 0)
    have hp_eq : p = binaryDist 1 (by norm_num) (by norm_num) := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [hp0_one, binaryDist]
      · simp [hp1_zero, binaryDist]

    -- H(p) = H(1, 0) = 0 by faddeev_H_one_zero
    have hp_H_zero : E.H p = 0 := by
      rw [hp_eq]
      exact faddeev_H_one_zero E

    -- g1 = (1, 0, 0): Apply recursivity to get H(g1) = H(1, 0) + 1 * H(1, 0) = 0
    have hg1_sum01 : g1.1 0 + g1.1 1 = 1 := by
      rw [hg1_0, hg1_1, hp0_one, hp1_zero]
      ring
    have hg1_sum01_pos : 0 < g1.1 0 + g1.1 1 := by rw [hg1_sum01]; norm_num
    have hrec_g1 := E.recursivity (n := 1) g1 hg1_sum01_pos

    -- normalizeBinary (1, 0) = (1, 0)
    have hnorm_g1 : normalizeBinary (g1.1 0) (g1.1 1) (g1.nonneg 0) (g1.nonneg 1) hg1_sum01_pos =
        binaryDist 1 (by norm_num) (by norm_num) := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [normalizeBinary, binaryDist, hg1_0, hg1_1, hp0_one, hp1_zero]
      · simp [normalizeBinary, binaryDist, hg1_0, hg1_1, hp0_one, hp1_zero]

    -- groupFirstTwo g1 = (1, 0)
    have hgroup_g1 : groupFirstTwo g1 hg1_sum01_pos = binaryDist 1 (by norm_num) (by norm_num) := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [groupFirstTwo, hg1_sum01, binaryDist]
      · simp [groupFirstTwo]
        -- Goal: g1.1 ⟨2, _⟩ = (binaryDist 1 _ _).1 1
        calc g1.1 ⟨2, _⟩ = p.1 1 * q2.1 1 := hg1_2
          _ = 0 * q2.1 1 := by rw [hp1_zero]
          _ = 0 := by ring
          _ = (binaryDist 1 (by norm_num) (by norm_num)).1 1 := by simp [binaryDist]

    -- hrec_g1 : E.H g1 = E.H (groupFirstTwo g1 _) + (g1.1 0 + g1.1 1) * E.H (normalizeBinary ...)
    -- We know both groupFirstTwo and normalizeBinary equal binaryDist 1, and H(1,0) = 0
    have hg1_H_zero : E.H g1 = 0 := by
      have hbd := faddeev_H_one_zero E
      -- Use congrArg to handle the binaryDist proof term differences
      have h1 : E.H (groupFirstTwo g1 hg1_sum01_pos) = 0 := by rw [hgroup_g1]; exact hbd
      have h2 : E.H (normalizeBinary (g1.1 0) (g1.1 1) (g1.nonneg 0) (g1.nonneg 1) hg1_sum01_pos) = 0 := by
        rw [hnorm_g1]; exact hbd
      calc E.H g1 = E.H (groupFirstTwo g1 hg1_sum01_pos) +
                    (g1.1 0 + g1.1 1) * E.H (normalizeBinary (g1.1 0) (g1.1 1) (g1.nonneg 0) (g1.nonneg 1) hg1_sum01_pos) := hrec_g1
        _ = 0 + (g1.1 0 + g1.1 1) * 0 := by rw [h1, h2]
        _ = 0 := by ring

    -- p.1 1 * E.H q2 = 0
    have h_right : p.1 1 * E.H q2 = 0 := by rw [hp1_zero]; ring

    -- From hrec1: E.H sb = E.H g1 + p.1 0 * E.H q1 = 0 + 1 * E.H q1 = E.H q1
    rw [hg1_H_zero, hp0_one] at hrec1
    simp at hrec1
    -- Goal: E.H sb = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2
    rw [hp_H_zero, hp0_one, h_right]
    simp
    exact hrec1

theorem faddeev_splitBoth (E : FaddeevEntropy) {m k : ℕ}
    (p : ProbVec 2) (q1 : ProbVec (m + 2)) (q2 : ProbVec (k + 2))
    (hp0 : 0 < p.1 0) (hp1 : 0 < p.1 1)
    (hq1 : 0 < q1.1 0 + q1.1 1) (hq2 : 0 < q2.1 0 + q2.1 1) :
    E.H (splitBoth p q1 q2) = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2 := by
  simpa using
    faddeev_splitBoth_headPos (E := E) (m := m) (k := k)
      (p := p) (q1 := q1) (q2 := q2) (hp0 := hp0) (hp1 := hp1) (hq1 := hq1) (hq2 := hq2)

/-- For n = 1, the point mass equals the uniform distribution -/
theorem pointMass_eq_uniformDist_one : pointMass (0 : Fin 1) = uniformDist 1 (by norm_num) := by
  apply Subtype.ext
  funext i
  fin_cases i
  simp [pointMass, uniformDist]

/-- For a Faddeev entropy, H(point mass) = 0.
    Proof structure:
    - For n = 1: pointMass 0 = uniformDist 1, so H = F(1) = 0
    - For n = 2: pointMass 0 = (1, 0), use faddeev_H_one_zero
    - For n ≥ 3: By recursivity, H(pointMass 0 on n) = H(pointMass 0 on n-1) + H(1, 0)
                 By induction, this reduces to (n-1) * H(1, 0) = 0
    - For general i: By symmetry, H(pointMass i) = H(pointMass 0) -/
theorem faddeev_pointMass_eq_zero (E : FaddeevEntropy) {n : ℕ} (i : Fin n) :
    E.H (pointMass i) = 0 := by
  classical
  -- First prove the `i=0` case for all `n≥2`.
  have h_pointMass0_ge2 : ∀ m : ℕ, E.H (pointMass (0 : Fin (m + 2))) = 0 := by
    intro m
    induction m with
    | zero =>
      -- `Fin 2`: point mass is (1,0).
      have hpm : pointMass (0 : Fin 2) = binaryDist 1 (by norm_num) (by norm_num) := by
        apply Subtype.ext
        funext j
        fin_cases j <;> simp [pointMass, binaryDist]
      simpa [hpm.symm] using (faddeev_H_one_zero E)
    | succ k ih =>
      -- `Fin (k+3)` reduces to `Fin (k+2)` via recursivity, since H(1,0)=0.
      set p : ProbVec (k + 3) := pointMass (0 : Fin (k + 3)) with hp
      have hp_sum01 : 0 < p.1 0 + p.1 1 := by
        simp [hp, pointMass]
      have hrec := E.recursivity (n := k + 1) p hp_sum01
      have hp_sum01_val : p.1 0 + p.1 1 = (1 : ℝ) := by
        simp [hp, pointMass]
      have hnorm :
          normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) hp_sum01 =
            binaryDist 1 (by norm_num) (by norm_num) := by
        apply Subtype.ext
        funext j
        fin_cases j <;> simp [hp, pointMass, normalizeBinary, binaryDist]
      have hgroup :
          groupFirstTwo p hp_sum01 = pointMass (0 : Fin (k + 2)) := by
        apply Subtype.ext
        funext j
        by_cases hj : j.val = 0
        · have : j = 0 := by ext; simpa using hj
          subst this
          simp [groupFirstTwo, hp, pointMass]
        · have hne :
            (⟨j.val + 1, by omega⟩ : Fin (k + 3)) ≠ (0 : Fin (k + 3)) := by
            intro h
            have := congrArg Fin.val h
            simp at this
          simp [groupFirstTwo, hp, pointMass]
      have hH10 : E.H (binaryDist 1 (by norm_num) (by norm_num)) = 0 :=
        faddeev_H_one_zero E
      -- Simplify the recursivity equation: H(p) = H(pointMass0) + 1 * 0.
      have : E.H p = E.H (pointMass (0 : Fin (k + 2))) := by
        have := hrec
        simp [hp_sum01_val, hnorm, hH10, hgroup] at this
        exact this
      -- Apply IH.
      simpa [hp] using this.trans ih
  -- Now handle the arity cases and use symmetry to move the point mass to `i`.
  cases n with
  | zero =>
    exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero =>
      -- `Fin 1`: point mass is uniform_1.
      have hi0 : i = 0 := by ext; simp
      subst hi0
      rw [pointMass_eq_uniformDist_one]
      exact faddeev_F1_eq_zero E
    | succ m =>
      -- `Fin (m+2)`: reduce `pointMass i` to `pointMass 0` via a swap.
      let σ : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 i
      have hperm : permute σ (pointMass (0 : Fin (m + 2))) = pointMass i := by
        apply Subtype.ext
        funext j
        -- `permute σ` moves the unique `1` at index 0 to index `i`.
        by_cases hj : j = i
        · subst hj
          simp [permute_apply, pointMass, σ, Equiv.swap_inv, Equiv.swap_apply_right]
        · have hj' : σ⁻¹ j ≠ (0 : Fin (m + 2)) := by
            intro h0
            have : j = σ 0 := by simpa using congrArg σ h0
            -- `σ 0 = i` for `swap 0 i`.
            have : j = i := by simpa [σ] using this
            exact hj this
          -- Do not unfold `σ` further; use `hj'` directly to simplify the `if`.
          simp [permute_apply, pointMass, hj, hj']
      -- Use symmetry to rewrite `H(pointMass i) = H(pointMass 0)`.
      have hsymm : E.H (pointMass i) = E.H (pointMass (0 : Fin (m + 2))) := by
        have := E.symmetry (pointMass (0 : Fin (m + 2))) σ
        -- `this : H (permute σ pointMass0) = H pointMass0`.
        -- Rewrite the permuted term to `pointMass i`.
        simpa [hperm] using this
      -- Conclude using the `i=0` lemma.
      calc
        E.H (pointMass i) = E.H (pointMass (0 : Fin (m + 2))) := hsymm
        _ = 0 := h_pointMass0_ge2 m

/-- The swap permutation (0 ↔ 2) on Fin 3 -/
def swap02 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- Helper: ternaryDist (1/2) (1/4) (1/4) -/
noncomputable def ternary_half_quarter_quarter : ProbVec 3 :=
  ternaryDist (1/2) (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Helper: ternaryDist (1/4) (1/4) (1/2) -/
noncomputable def ternary_quarter_quarter_half : ProbVec 3 :=
  ternaryDist (1/4) (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Permuting (1/2, 1/4, 1/4) by swap02 gives (1/4, 1/4, 1/2) -/
theorem permute_swap02_ternary :
    permute swap02 ternary_half_quarter_quarter = ternary_quarter_quarter_half := by
  apply Subtype.ext
  funext i
  simp only [permute_apply, swap02, ternary_half_quarter_quarter,
    ternary_quarter_quarter_half, ternaryDist]
  fin_cases i
  · -- i = 0: swap02⁻¹(0) = 2, so we get p[2] = 1/4
    show (![1/2, 1/4, 1/4] : Fin 3 → ℝ) ((Equiv.swap 0 2)⁻¹ 0) =
         (![1/4, 1/4, 1/2] : Fin 3 → ℝ) 0
    simp only [Equiv.swap_inv, Equiv.swap_apply_left]
    -- Goal: ![1/2, 1/4, 1/4] 2 = ![1/4, 1/4, 1/2] 0
    -- Both sides equal 1/4
    rfl
  · -- i = 1: swap02⁻¹(1) = 1 (unchanged)
    show (![1/2, 1/4, 1/4] : Fin 3 → ℝ) ((Equiv.swap 0 2)⁻¹ 1) =
         (![1/4, 1/4, 1/2] : Fin 3 → ℝ) 1
    have h1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
    simp only [Equiv.swap_inv, h1]
    -- Goal: ![1/2, 1/4, 1/4] 1 = ![1/4, 1/4, 1/2] 1
    -- Both sides equal 1/4
    rfl
  · -- i = 2: swap02⁻¹(2) = 0, so we get p[0] = 1/2
    show (![1/2, 1/4, 1/4] : Fin 3 → ℝ) ((Equiv.swap 0 2)⁻¹ 2) =
         (![1/4, 1/4, 1/2] : Fin 3 → ℝ) 2
    simp only [Equiv.swap_inv, Equiv.swap_apply_right]
    -- Goal: ![1/2, 1/4, 1/4] 0 = ![1/4, 1/4, 1/2] 2
    -- Both sides equal 1/2
    rfl

/-- H(1/4, 1/4, 1/2) = 3/2 for any Faddeev entropy.
    Proof: Apply recursivity to group (1/4, 1/4) → 1/2
    H(1/4, 1/4, 1/2) = H(1/2, 1/2) + (1/2) * H(1/2, 1/2) = 1 + 1/2 = 3/2 -/
theorem faddeev_ternary_quarter_quarter_half (E : FaddeevEntropy) :
    E.H ternary_quarter_quarter_half = 3/2 := by
  set p := ternary_quarter_quarter_half with hp
  -- Apply recursivity
  have h_sum : 0 < p.1 0 + p.1 1 := by
    simp only [hp, ternary_quarter_quarter_half, ternaryDist,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h_rec := E.recursivity p h_sum
  -- p.1 0 + p.1 1 = 1/4 + 1/4 = 1/2
  have h_sum_val : p.1 0 + p.1 1 = 1/2 := by
    simp only [hp, ternary_quarter_quarter_half, ternaryDist,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  -- normalizeBinary gives (1/2, 1/2) = binaryUniform
  have h_norm : normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h_sum = binaryUniform := by
    apply Subtype.ext
    funext i
    simp only [hp, ternary_quarter_quarter_half, ternaryDist,
      normalizeBinary, binaryUniform, binaryDist,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases i <;> norm_num
  -- groupFirstTwo gives (1/2, 1/2) = binaryUniform
  have h_group : groupFirstTwo p h_sum = binaryUniform := by
    apply Subtype.ext
    funext i
    fin_cases i
    · -- i = 0: grouped has 1/4 + 1/4 = 1/2
      simp [groupFirstTwo, hp, ternary_quarter_quarter_half, ternaryDist,
        binaryUniform, binaryDist]
      norm_num
    · -- i = 1: grouped has p[2] = 1/2
      -- groupFirstTwo at i=1 gives p.1 ⟨1+1, _⟩ = p.1 2 = 1/2
      simp [groupFirstTwo]
      -- Now we need p.1 ⟨2, _⟩ = 1/2
      simp [hp, ternary_quarter_quarter_half, ternaryDist, binaryUniform, binaryDist]
      norm_num
  -- Now compute
  rw [h_norm, h_group] at h_rec
  rw [h_rec, h_sum_val, E.normalization]
  ring

/-- Concrete case: F(4) = 2 = F(2) + F(2).
    This demonstrates the pairing technique used in multiplicativity. -/
theorem faddeev_F4_eq_2 (E : FaddeevEntropy) :
    E.H (uniformDist 4 (by norm_num : 0 < 4)) = 2 := by
  -- Apply recursivity to uniform_4 = (1/4, 1/4, 1/4, 1/4)
  set u4 := uniformDist 4 (by norm_num : 0 < 4) with hu4
  have h_sum : 0 < u4.1 0 + u4.1 1 := by
    simp only [hu4, uniformDist_apply]
    norm_num
  have h_rec := E.recursivity u4 h_sum
  -- u4.1 0 + u4.1 1 = 1/4 + 1/4 = 1/2
  have h_sum_val : u4.1 0 + u4.1 1 = 1/2 := by
    simp only [hu4, uniformDist_apply]
    norm_num
  -- normalizeBinary gives (1/2, 1/2) = binaryUniform
  have h_norm : normalizeBinary (u4.1 0) (u4.1 1) (u4.nonneg 0) (u4.nonneg 1) h_sum = binaryUniform := by
    apply Subtype.ext
    funext i
    simp [hu4, uniformDist_apply, normalizeBinary, binaryUniform, binaryDist]
    fin_cases i <;> norm_num
  -- groupFirstTwo gives ternary (1/2, 1/4, 1/4)
  have h_group : groupFirstTwo u4 h_sum = ternary_half_quarter_quarter := by
    apply Subtype.ext
    funext i
    fin_cases i
    · -- i = 0: 1/4 + 1/4 = 1/2
      simp [groupFirstTwo, hu4, uniformDist_apply, ternary_half_quarter_quarter, ternaryDist]
      norm_num
    · -- i = 1: u4[2] = 1/4
      -- groupFirstTwo at i=1 gives u4.1 ⟨2, _⟩ = 1/4
      simp [groupFirstTwo, ternary_half_quarter_quarter, ternaryDist,
        hu4, uniformDist_apply]
    · -- i = 2: u4[3] = 1/4
      -- groupFirstTwo at i=2 gives u4.1 ⟨3, _⟩ = 1/4
      simp [groupFirstTwo, ternary_half_quarter_quarter, ternaryDist,
        hu4, uniformDist_apply]
  rw [h_norm, h_group, h_sum_val] at h_rec
  -- h_rec: E.H u4 = E.H ternary_half_quarter_quarter + (1/2) * 1
  rw [E.normalization] at h_rec
  -- By symmetry: E.H ternary_half_quarter_quarter = E.H ternary_quarter_quarter_half
  have h_sym : E.H ternary_half_quarter_quarter = E.H ternary_quarter_quarter_half := by
    rw [← permute_swap02_ternary]
    exact (E.symmetry ternary_half_quarter_quarter swap02).symm
  rw [h_sym, faddeev_ternary_quarter_quarter_half] at h_rec
  linarith

/-
## Faddeev 1956: multiplicativity on uniforms

The original paper defines `F(n) := H(1/n, …, 1/n)` and proves `F(mn) = F(m) + F(n)`.
We follow the paper’s proof pattern, but package it as a Lean lemma for later use.
-/

section UniformMultiplicativity

open scoped Topology

set_option maxHeartbeats 1000000 in
theorem faddeev_F_mul (E : FaddeevEntropy) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    F E (m * n) (Nat.mul_pos hm hn) = F E m hm + F E n hn := by
  classical
  -- reduce to `n ≥ 2` (the `n=1` case is trivial)
  cases n with
  | zero => cases hn
  | succ n =>
    cases n with
    | zero =>
      -- `n = 1`
      have hn1 : 0 < (1 : ℕ) := by decide
      have hmul : F E (m * 1) (Nat.mul_pos hm hn1) = F E m hm := by
        have hmMul : 0 < m := by
          simpa [Nat.mul_one] using (Nat.mul_pos hm hn1)
        have h₁ : F E (m * 1) (Nat.mul_pos hm hn1) = F E m hmMul := by
          simp
        have h₂ : F E m hmMul = F E m hm :=
          F_congr (E := E) (hn := hmMul) (hn' := hm)
        exact h₁.trans h₂
      have hF1 : F E 1 hn1 = 0 := by
        simp [F, faddeev_F1_eq_zero]
      -- `F(m*1) = F(m) + F(1)`
      simp [hF1]
    | succ n =>
      -- now `n ≥ 2`
      have hn2 : 1 < n.succ.succ := by omega
      -- induct on `m`
      cases m with
      | zero => cases hm
      | succ m =>
        induction m with
        | zero =>
          -- `m = 1`
          have hm1 : 0 < (1 : ℕ) := by decide
          have hF1 : F E 1 hm1 = 0 := by
            simp [F, faddeev_F1_eq_zero]
          have hmul :
              F E (1 * n.succ.succ) (Nat.mul_pos hm1 (Nat.succ_pos _)) =
                F E (n.succ.succ) (Nat.succ_pos _) := by
            have hnMul : 0 < n.succ.succ := Nat.succ_pos _
            have hnMul' : 0 < 1 * n.succ.succ := Nat.mul_pos hm1 hnMul
            have hnMul'' : 0 < n.succ.succ := by simp
            have h₁ : F E (1 * n.succ.succ) hnMul' = F E (n.succ.succ) hnMul'' := by
              simp
            have h₂ : F E (n.succ.succ) hnMul'' = F E (n.succ.succ) hnMul :=
              F_congr (E := E) (hn := hnMul'') (hn' := hnMul)
            exact h₁.trans h₂
          have hF1' : F E 1 hm = 0 := by
            -- align the proof argument for `F E 1`
            have hcong : F E 1 hm = F E 1 hm1 :=
              F_congr (E := E) (hn := hm) (hn' := hm1)
            calc
              F E 1 hm = F E 1 hm1 := hcong
              _ = 0 := hF1
          simp [hF1']
        | succ m ih =>
          -- `m = m+2`
          have hm2 : 1 < m.succ.succ := by omega
          have hmpos : 0 < m.succ.succ := Nat.lt_trans Nat.zero_lt_one hm2
          have hm1pos : 0 < m.succ := Nat.succ_pos _
          have hnpos : 0 < n.succ.succ := Nat.succ_pos _
          -- use the two-step identity for `F((m+2)*n)` and cancel the binary term using `F_succ_eq`
          -- First, express `F((m+2)*n)` by splitting the binary distribution and then the tail mass.
          -- This is exactly the same calculation as `F_succ_eq`, but with `n` outcomes in the first split.
          have hmul :
              F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hmpos hnpos)
                =
              E.H (binaryOneDiv (m.succ.succ) hmpos)
                + ((1 : ℝ) / m.succ.succ) * F E (n.succ.succ) hnpos
                + (1 - (1 : ℝ) / m.succ.succ) *
                    F E ((m.succ.succ - 1) * n.succ.succ)
                      (Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos) := by
            -- Construct the twice-refined distribution explicitly.
            have hm0 : 0 < m.succ.succ := hmpos
            have hn0 : 0 < n.succ.succ := Nat.succ_pos _
            set p : ProbVec 2 := binaryOneDiv (m.succ.succ) hm0
            set qn : ProbVec (n.succ.succ) := uniformDist (n.succ.succ) hn0 with hqn
            -- first split: split `1/m` into `n` equal parts
            have hp0 : 0 < p.1 0 := by
              simp [p, binaryOneDiv_apply_zero] ; positivity
            have hqsum :
                0 <
                  qn.1 ⟨0, hn0⟩ + qn.1 ⟨1, by omega⟩ := by
              simp [hqn, uniformDist_apply] ; positivity
            have hsplit1 :
                E.H (splitFirst (n := 1) (m := n.succ.succ) p qn)
                  =
                E.H p + p.1 0 * E.H qn := by
              have hmain :=
                faddeev_splitFirst_headPos (E := E) (n := 1) (m := n)
                  (p := p)
                  (q := (by
                    simpa using (uniformDist (n + 2) (by omega : 0 < n + 2))))
                  (hp0 := hp0)
                  (hq := by
                    simp [uniformDist_apply] ; positivity)
              -- `n + 2 = n.succ.succ`
              simpa [hqn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmain
            -- second split: bring the tail mass `(m+1)/ (m+2)` to the head and split into `(m+1)*n` equal parts
            have htailpos : 0 < (m.succ.succ - 1) * n.succ.succ := by
              have : 0 < m.succ.succ - 1 := by omega
              exact Nat.mul_pos this hn0
            set qmn : ProbVec ((m.succ.succ - 1) * n.succ.succ) := uniformDist _ htailpos with hqmn_def
            -- Compute `H` via the two splitting steps:
            have hF : F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hm0 hn0) =
                E.H p + ((1 : ℝ) / m.succ.succ) * E.H (uniformDist (n.succ.succ) hn0)
                  + (1 - (1 : ℝ) / m.succ.succ) * E.H (uniformDist ((m.succ.succ - 1) * n.succ.succ) htailpos) := by
              classical
              -- Notation
              let M : ℕ := m.succ.succ
              let N : ℕ := n.succ.succ
              let K : ℕ := (M - 1) * N

              have hmM : 1 < M := by
                exact hm2
              have hmM0 : 0 < M := by
                exact hm0
              have hnN0 : 0 < N := by
                exact hn0
              have hkK0 : 0 < K := by
                exact htailpos
              have hkK2 : 2 ≤ K := by
                have : 2 ≤ N := by
                  -- `N = n+2`
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
                -- `K = (M-1) * N` with `N ≥ 2`
                have hM1 : 1 ≤ M - 1 := by
                  have : 2 ≤ M := by omega
                  exact Nat.sub_le_sub_right this 1
                have hKN : 2 ≤ (M - 1) * N := by
                  -- `(M-1) ≥ 1` and `N ≥ 2`
                  have : 1 * 2 ≤ (M - 1) * N := Nat.mul_le_mul hM1 this
                  simpa using this
                simpa [K] using hKN
              have hNK0 : 0 < N + K := by
                simpa [Nat.add_comm] using (Nat.add_pos_left hkK0 N)

              have hMN : N + K = M * N := by
                -- `N + (M-1)*N = M*N`
                calc
                  N + K = K + N := by ac_rfl
                  _ = (M - 1) * N + 1 * N := by simp [K]
                  _ = ((M - 1) + 1) * N := by
                    exact (Nat.add_mul (M - 1) 1 N).symm
                  _ = M * N := by
                    have hm1le : 1 ≤ M := Nat.succ_le_of_lt hmM0
                    simp [Nat.sub_add_cancel hm1le]

              -- Step 1: rewrite `F(M*N)` as entropy of `uniformDist (N+K)` via casting.
              have hMul0 : 0 < M * N := Nat.mul_pos hmM0 hnN0
              have hMul0' : 0 < M * N := by
                exact lt_of_lt_of_eq hNK0 hMN
              have hunif :
                  uniformDist (M * N) hMul0' = uniformDist (M * N) hMul0 := by
                exact uniformDist_congr (n := M * N) hMul0' hMul0
              have hcastU :
                  cast (congrArg ProbVec hMN) (uniformDist (N + K) hNK0) =
                    uniformDist (M * N) hMul0 := by
                have hcastU' :=
                  (cast_uniformDist (hn := hNK0) (h := hMN) : _)
                -- align the proof argument on `uniformDist (M*N)`
                simpa [hunif] using hcastU'
              have hF_cast :
                  E.H (uniformDist (M * N) hMul0) = E.H (uniformDist (N + K) hNK0) := by
                have hHcast :
                    E.H (cast (congrArg ProbVec hMN) (uniformDist (N + K) hNK0))
                      = E.H (uniformDist (N + K) hNK0) :=
                  H_cast (E := E) (n := N + K) (n' := M * N) hMN (uniformDist (N + K) hNK0)
                -- `cast _ (uniformDist (N+K)) = uniformDist (M*N)` from `hcastU`
                exact (hHcast.symm.trans (congrArg E.H hcastU)).symm

              -- Step 2: build the twice-split distribution and show it is uniform.
              -- First split: split `1/M` into `N` equal parts (already used for `hsplit1`).
              set r1 : ProbVec (1 + N) := splitFirst (n := 1) (m := N) p qn
              have hr1H : E.H r1 = E.H p + p.1 0 * E.H qn := by
                -- `hsplit1` is exactly this statement, but with the previous `set` names.
                simpa [r1] using hsplit1

              -- Cast `r1` to arity `N+1`, so we can swap the tail to the head.
              have h1N : 1 + N = N + 1 := Nat.one_add N
              set r1' : ProbVec (N + 1) := cast (congrArg ProbVec h1N) r1
              -- The tail index (the untouched outcome) is the last coordinate.
              let tail : Fin (N + 1) := Fin.last N
              let σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap (0 : Fin (N + 1)) tail
              set p2 : ProbVec (N + 1) := permute σ r1'

              have hp2H : E.H p2 = E.H r1' := by
                -- symmetry under permutations
                simpa [p2] using E.symmetry r1' σ
              have hr1' : E.H r1' = E.H r1 := by
                -- remove the cast on `H`
                simpa [r1'] using (H_cast (E := E) (n := 1 + N) (n' := N + 1) h1N r1)

              -- Second split: split the head mass of `p2` into `K` equal parts.
              set r2 : ProbVec (N + K) := splitFirst (n := N) (m := K) p2 qmn

              have hp0val : p.1 0 = (1 : ℝ) / M := by
                simp [p, M, binaryOneDiv_apply_zero]
              have hp1val : p.1 1 = 1 - (1 : ℝ) / M := by
                simp [p, M, binaryOneDiv_apply_one]

              have hr1_tail : r1.1 ⟨N, by omega⟩ = 1 - (1 : ℝ) / M := by
                -- the tail is the untouched `p₁`
                have hidx :
                    ((Fin.natAdd N (0 : Fin 1)).cast (Nat.add_comm N 1)) =
                      (⟨N, by omega⟩ : Fin (1 + N)) := by
                  ext
                  simp [N, Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
                have : r1.1 ⟨N, by omega⟩ = p.1 1 := by
                  have :=
                    (splitFirst_natAdd (p := p) (q := qn) (n := 1) (m := N) (i := (0 : Fin 1)))
                  -- unfold `r1` and rewrite the index
                  simpa [r1, hidx] using this
                simpa [hp1val] using this

              have hp2_0 : p2.1 0 = 1 - (1 : ℝ) / M := by
                -- swapping brings the tail to index `0`
                have ht : σ 0 = tail := by simp [σ, Equiv.swap_apply_left]
                have : p2.1 0 = r1'.1 tail := by
                  simp [p2, permute_apply, σ, Equiv.swap_apply_left]
                have hr1'_tail : r1'.1 tail = 1 - (1 : ℝ) / M := by
                  -- evaluate the casted distribution at the tail index
                  have hcast :=
                    cast_apply_probVec (h := h1N) (p := r1) (i := tail)
                  have htailcast : tail.cast h1N.symm = (⟨N, by omega⟩ : Fin (1 + N)) := by
                    ext
                    simp [tail, N, Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
                  -- unfold `r1'`
                  simpa [r1', htailcast, hr1_tail] using hcast
                exact this.trans hr1'_tail

              -- Allow numerals `0`,`1` as `Fin _` indices by providing `NeZero`.
              letI : NeZero ((m.succ.succ - 1) * n.succ.succ) := ⟨Nat.ne_of_gt htailpos⟩
              have hqmn : 0 < qmn.1 0 + qmn.1 1 := by
                simp [hqmn_def, uniformDist_apply] ; positivity

              have hsplit2 : E.H r2 = E.H p2 + p2.1 0 * E.H qmn := by
                -- `faddeev_splitFirst_headPos` expects an arity of the form `m+2`; rewrite `K` as `(K-2)+2`.
                have hK : (K - 2) + 2 = K := Nat.sub_add_cancel hkK2
                let qmnCast : ProbVec ((K - 2) + 2) := cast (congrArg ProbVec hK.symm) qmn
                have qmnCast_pos : 0 < qmnCast.1 0 + qmnCast.1 1 := by
                  have hkposR : (0 : ℝ) < K := by exact_mod_cast hkK0
                  have h0 : qmnCast.1 (0 : Fin ((K - 2) + 2)) = (1 : ℝ) / K := by
                    dsimp [qmnCast]
                    have hcast0 :=
                      cast_apply_probVec (h := hK.symm) (p := qmn) (i := (0 : Fin ((K - 2) + 2)))
                    calc
                      (cast (congrArg ProbVec hK.symm) qmn).1 (0 : Fin ((K - 2) + 2))
                          = qmn.1 ((0 : Fin ((K - 2) + 2)).cast hK) := hcast0
                      _ = (1 : ℝ) / K := by
                        dsimp [K, M, N]
                        simp [hqmn_def, uniformDist_apply]
                  have h1 : qmnCast.1 (1 : Fin ((K - 2) + 2)) = (1 : ℝ) / K := by
                    dsimp [qmnCast]
                    have hcast1 :=
                      cast_apply_probVec (h := hK.symm) (p := qmn) (i := (1 : Fin ((K - 2) + 2)))
                    calc
                      (cast (congrArg ProbVec hK.symm) qmn).1 (1 : Fin ((K - 2) + 2))
                          = qmn.1 ((1 : Fin ((K - 2) + 2)).cast hK) := hcast1
                      _ = (1 : ℝ) / K := by
                        dsimp [K, M, N]
                        simp [hqmn_def, uniformDist_apply]
                  have hdiv : 0 < (1 : ℝ) / K := by
                    -- Use `hkposR : 0 < (K:ℝ)`.
                    positivity
                  nlinarith [h0, h1, hdiv]
                have hp2pos : 0 < p2.1 0 := by
                  -- `1 - 1/M > 0` since `M > 1`
                  have hMposR : (0 : ℝ) < M := by exact_mod_cast hmM0
                  have hdiv : (1 : ℝ) / M < 1 := (div_lt_one hMposR).2 (by exact_mod_cast hmM)
                  have : 0 < 1 - (1 : ℝ) / M := by linarith
                  simpa [hp2_0] using this
                have hmain :=
                  faddeev_splitFirst_headPos (E := E) (n := N) (m := K - 2)
                    (p := p2) (q := qmnCast) (hp0 := hp2pos) (hq := qmnCast_pos)
                -- Transport the statement back to `r2 = splitFirst p2 qmn` and `qmn`.
                have hqCast : E.H qmnCast = E.H qmn := by
                  -- `qmnCast` is a cast of `qmn`.
                  simpa [qmnCast] using (H_cast (E := E) (h := hK.symm) (p := qmn))
                have hr2Cast : E.H (splitFirst p2 qmnCast) = E.H r2 := by
                  -- `splitFirst` respects casts in the refinement arity.
                  have hsplit :
                      cast (congrArg ProbVec (congrArg (fun t => N + t) hK.symm)) r2 =
                        splitFirst p2 qmnCast := by
                    simpa [r2, qmnCast] using
                      (splitFirst_cast_right (p := p2) (q := qmn) (n := N) (m := K)
                        (m' := (K - 2) + 2) (h := hK.symm))
                  have hH := congrArg E.H hsplit
                  -- Drop the cast on the left-hand side.
                  calc
                    E.H (splitFirst p2 qmnCast) = E.H (cast (congrArg ProbVec (congrArg (fun t => N + t) hK.symm)) r2) := by
                      simpa using hH.symm
                    _ = E.H r2 := by
                      simpa using (H_cast (E := E) (h := congrArg (fun t => N + t) hK.symm) (p := r2))
                -- Rewrite `hmain` using the cast-transport lemmas.
                calc
                  E.H r2 = E.H (splitFirst p2 qmnCast) := by simpa using hr2Cast.symm
                  _ = E.H p2 + p2.1 0 * E.H qmnCast := hmain
                  _ = E.H p2 + p2.1 0 * E.H qmn := by simp [hqCast]

              -- Show `r2` is the uniform distribution on `N+K`.
              have hr2 : r2 = uniformDist (N + K) hNK0 := by
                apply Subtype.ext
                funext i
                -- compare the index to the split block size `K`
                have hi_le : (i : ℕ) ≤ N + K - 1 := Nat.le_of_lt_succ i.isLt
                by_cases hi : (i : ℕ) < K
                ·
                  -- split block
                  let j : Fin K := ⟨i.1, hi⟩
                  have hj :
                      i = (Fin.castAdd N j).cast (Nat.add_comm K N) := by
                    ext
                    simp [j]
                  have hval :
                      r2.1 i = (1 : ℝ) / (M * N) := by
                    have hcoeff :
                        (1 - (1 : ℝ) / M) * ((1 : ℝ) / K) = (1 : ℝ) / (M * N) := by
                      -- Avoid `simp` rewriting `↑(M-1)` into `↑M - 1`; just unfold `K`.
                      dsimp [K]
                      have hM1le : (1 : ℕ) ≤ M :=
                        Nat.succ_le_iff.2 (Nat.lt_trans Nat.zero_lt_one hmM)
                      -- Normalize the cast on `((M-1)*N)` so the goal matches the lemma's simp-normal form.
                      simpa [Nat.cast_mul, Nat.cast_sub hM1le] using
                        (one_sub_one_div_mul_uniform_mul (m := M) (n := N) hmM hnN0)
                    -- Evaluate splitFirst on the split block coordinate, and rewrite explicitly.
                    have hsplit :=
                      splitFirst_castAdd (p := p2) (q := qmn) (n := N) (m := K) (i := j)
                    have hstep : r2.1 i = p2.1 0 * qmn.1 j := by
                      simpa [r2, hj] using hsplit
                    have hq : qmn.1 j = (1 : ℝ) / K := by
                      -- `qmn` is uniform on `K = (M-1)*N`.
                      dsimp [K, M, N]
                      simp [hqmn_def, uniformDist_apply]
                    calc
                      r2.1 i = p2.1 0 * qmn.1 j := hstep
                      _ = (1 - (1 : ℝ) / M) * ((1 : ℝ) / K) := by
                            simp [hp2_0, hq]
                      _ = (1 : ℝ) / (M * N) := hcoeff
                  -- uniformDist coordinate
                  have hu :
                      (uniformDist (N + K) hNK0).1 i = (1 : ℝ) / (M * N) := by
                    -- use `N+K = M*N`
                    simp [uniformDist, hMN]
                  simp [hval, hu]
                ·
                  -- tail block: index corresponds to one of the original `N` split pieces
                  have hiK : K ≤ (i : ℕ) := Nat.le_of_not_gt hi
                  let jNat : ℕ := i.1 - K
                  have hjNat : jNat < N := by
                    -- since `i < N+K`
                    have : i.1 < N + K := i.isLt
                    -- `i.1 - K < N`
                    omega
                  let j : Fin N := ⟨jNat, hjNat⟩
                  have hj :
                      i = (Fin.natAdd K j).cast (Nat.add_comm K N) := by
                    ext
                    have : K + j.1 = i.1 := by
                      calc
                        K + j.1 = K + (i.1 - K) := by simp [j, jNat]
                        _ = (i.1 - K) + K := by ac_rfl
                        _ = i.1 := Nat.sub_add_cancel hiK
                    simp [j, this]
                  have hval :
                      r2.1 i = (1 : ℝ) / (M * N) := by
                    -- tail block uses `p2` at successor indices
                    have := splitFirst_natAdd (p := p2) (q := qmn) (n := N) (m := K) (i := j)
                    -- `p2` on nonzero indices is always a split piece value, i.e. `1/(M*N)`
                    have hsplitPiece : p2.1 j.succ = (1 : ℝ) / (M * N) := by
                      -- `p2` is `r1'` with a swap of `0` and `tail`.
                      by_cases htail' : j.succ = tail
                      ·
                        -- the swapped point: `σ⁻¹ j.succ = 0`
                        have hσ : σ⁻¹ j.succ = (0 : Fin (N + 1)) := by
                          -- for swaps, `σ⁻¹ = σ`
                          simp [σ, htail']
                        -- compute `r1'.1 0` from `r1`
                        have hr1'_0 : r1'.1 0 = (1 : ℝ) / (M * N) := by
                          have hcast :=
                            cast_apply_probVec (h := h1N) (p := r1) (i := (0 : Fin (N + 1)))
                          have h0cast : (0 : Fin (N + 1)).cast h1N.symm = (0 : Fin (1 + N)) := by
                            ext
                            simp
                          have hr1_0 :
                              r1.1 (0 : Fin (1 + N)) = p.1 0 * qn.1 (0 : Fin N) := by
                            have hidx :
                                ((Fin.castAdd 1 (0 : Fin N)).cast (Nat.add_comm N 1)) =
                                  (0 : Fin (1 + N)) := by
                              ext
                              simp
                            simpa [r1, hidx] using
                              (splitFirst_castAdd (p := p) (q := qn) (n := 1) (m := N) (i := (0 : Fin N)))
                          have hqn0 : qn.1 (0 : Fin N) = (1 : ℝ) / N := by
                            -- Avoid `simp` expanding `↑(Nat.succ ...)` into `↑n + 1` and leaving
                            -- cast-goals like `↑n + 1 + 1 = ↑N` unsolved.
                            dsimp [N]
                            simp [hqn, uniformDist_apply]
                          have hmul :
                              p.1 0 * ((1 : ℝ) / N) = (1 : ℝ) / (M * N) := by
                            simpa [hp0val] using
                              (one_div_mul_one_div (m := M) (n := N) hmM0 hnN0)
                          have : r1.1 (0 : Fin (1 + N)) = (1 : ℝ) / (M * N) := by
                            -- Avoid `simp` normalizing into inverse-products and missing `hmul`.
                            rw [hr1_0, hqn0]
                            exact hmul
                          -- unfold `r1'`
                          simpa [r1', h0cast, this] using hcast
                        -- finish: `p2.1 j.succ = r1'.1 0`
                        -- `simp` sometimes normalizes `1/(M*N)` into a reversed inverse product; do this explicitly.
                        calc
                          p2.1 j.succ = r1'.1 (σ⁻¹ j.succ) := by
                            simp [p2, permute_apply]
                          _ = r1'.1 0 := by simp [hσ]
                          _ = (1 : ℝ) / (M * N) := hr1'_0
                      ·
                        -- the fixed points: `σ⁻¹ j.succ = j.succ`
                        have hσ : σ⁻¹ j.succ = j.succ := by
                          have hne0 : j.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero j
                          simp [σ, htail', hne0, Equiv.swap_apply_of_ne_of_ne]
                        -- show `r1'.1 j.succ` is a split piece, hence `1/(M*N)`
                        have hr1'_succ : r1'.1 j.succ = (1 : ℝ) / (M * N) := by
                          have hjle : (j.succ : Fin (N + 1)).1 ≤ N := Nat.le_of_lt_succ j.succ.isLt
                          have hjne : (j.succ : Fin (N + 1)).1 ≠ N := by
                            intro hEq
                            apply htail'
                            ext
                            simpa [tail, hEq]
                          have hjlt : (j.succ : Fin (N + 1)).1 < N := Nat.lt_of_le_of_ne hjle hjne
                          let iSplit : Fin N := ⟨j.succ.1, hjlt⟩
                          have hcast :=
                            cast_apply_probVec (h := h1N) (p := r1) (i := j.succ)
                          have hidx :
                              (j.succ).cast h1N.symm =
                                (Fin.castAdd 1 iSplit).cast (Nat.add_comm N 1) := by
                            ext
                            simp [iSplit]
                          have hr1_split :
                              r1.1 ((j.succ).cast h1N.symm) = p.1 0 * qn.1 iSplit := by
                            simpa [r1, hidx] using
                              (splitFirst_castAdd (p := p) (q := qn) (n := 1) (m := N) (i := iSplit))
                          have hqn_val : qn.1 iSplit = (1 : ℝ) / N := by
                            -- Avoid `simp` expanding `↑(Nat.succ ...)` into `↑n + 1` and leaving
                            -- cast-goals like `↑n + 1 + 1 = ↑N` unsolved.
                            dsimp [N]
                            simp [hqn, uniformDist_apply]
                          have hmul :
                              p.1 0 * ((1 : ℝ) / N) = (1 : ℝ) / (M * N) := by
                            simpa [hp0val] using
                              (one_div_mul_one_div (m := M) (n := N) hmM0 hnN0)
                          have : r1.1 ((j.succ).cast h1N.symm) = (1 : ℝ) / (M * N) := by
                            -- Avoid `simp` creating cast-goals like `((n:ℝ)+1+1)=↑N`.
                            -- Rewrite directly to the `hmul` hypothesis.
                            rw [hr1_split, hqn_val]
                            exact hmul
                          -- unfold `r1'`
                          have hcast' :
                              r1'.1 j.succ = r1.1 ((j.succ).cast h1N.symm) := by
                            simpa [r1'] using hcast
                          exact hcast'.trans this
                        simp [p2, permute_apply, hσ, hr1'_succ]
                    -- finish tail-block value
                    simpa [r2, hj, hsplitPiece] using this
                  have hu :
                      (uniformDist (N + K) hNK0).1 i = (1 : ℝ) / (M * N) := by
                    simp [uniformDist, hMN]
                  simp [hval, hu]

              -- Combine everything: `H` of a uniform is `H` of the twice-split distribution.
              have hHr2 : E.H (uniformDist (N + K) hNK0) =
                  (E.H p + ((1 : ℝ) / M) * E.H qn) + (1 - (1 : ℝ) / M) * E.H qmn := by
                -- rewrite `E.H (uniformDist (N+K))` via `r2`, and expand using both splitting steps.
                have hr2H' : E.H (uniformDist (N + K) hNK0) = E.H r2 := by
                  simp [hr2]
                have hp2H' : E.H p2 = E.H r1 := by
                  -- `p2` is a permutation of `r1'`, and `r1'` is a cast of `r1`
                  calc
                    E.H p2 = E.H r1' := hp2H
                    _ = E.H r1 := hr1'
                -- expand `E.H r2` and `E.H r1`
                calc
                  E.H (uniformDist (N + K) hNK0)
                      = E.H r2 := hr2H'
                  _ = E.H p2 + p2.1 0 * E.H qmn := hsplit2
                  _ = (E.H r1) + (1 - (1 : ℝ) / M) * E.H qmn := by
                        simp [hp2H', hp2_0]
                  _ = (E.H p + ((1 : ℝ) / M) * E.H qn) + (1 - (1 : ℝ) / M) * E.H qmn := by
                        -- unfold `r1` and use `hsplit1`
                        have : E.H r1 = E.H p + ((1 : ℝ) / M) * E.H qn := by
                          simpa [hp0val, mul_assoc] using hr1H
                        simp [this, add_left_comm, add_comm]

              -- Finally, transport back to `F(M*N)`.
              have hF' :
                  F E (M * N) hMul0 =
                    E.H p + ((1 : ℝ) / M) * E.H qn + (1 - (1 : ℝ) / M) * E.H qmn := by
                -- `F` on a uniform is `E.H` of that uniform
                simpa [F, hHr2, add_assoc, add_left_comm, add_comm, mul_assoc] using
                  congrArg (fun t => t) (hF_cast.trans hHr2)

              -- rewrite all abbreviations back to the goal statement
              have hF'' := hF'
              -- unfold the `set`-definitions of the uniform distributions
              rw [hqn] at hF''
              rw [hqmn_def] at hF''
              simpa [F, M, N, K, hp0val] using hF''
            -- finish
            -- Rewrite the goal to match `hF`, adjusting only proof arguments.
            have hN :
                F E (n.succ.succ) hnpos = F E (n.succ.succ) hn0 := by
              exact F_congr (E := E) (hn := hnpos) (hn' := hn0)
            have htailposGoal : 0 < (m.succ.succ - 1) * n.succ.succ :=
                Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos
            have htailF :
                F E ((m.succ.succ - 1) * n.succ.succ) htailposGoal =
                  F E ((m.succ.succ - 1) * n.succ.succ) htailpos := by
              exact F_congr (E := E) (hn := htailposGoal) (hn' := htailpos)
            have hLhs :
                F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hmpos hnpos) =
                  F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hm0 hn0) := by
              exact
                F_congr (E := E)
                  (hn := Nat.mul_pos hmpos hnpos)
                  (hn' := Nat.mul_pos hm0 hn0)
            have hpH : E.H (binaryOneDiv (m.succ.succ) hmpos) = E.H p := by
              have hb :=
                binaryOneDiv_congr (m := m.succ.succ) (hm := hmpos) (hm' := hm0)
              have hbH := congrArg E.H hb
              simp [p, hbH]
            rw [hLhs, hpH, hN, htailF]
            -- Unfold `F` (definitionally) so the statement matches `hF`.
            dsimp [F] at hF ⊢
            exact hF

          -- Now cancel the binary term using `F_succ_eq` and apply IH to the `(m+1)*n` term.
          have hrec := F_succ_eq (E := E) (m := m.succ.succ) hm2
          have ih' :
              F E (m.succ * n.succ.succ) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) =
                F E m.succ (Nat.succ_pos _) + F E (n.succ.succ) (Nat.succ_pos _) := by
            simpa using ih
          -- `m.succ.succ - 1 = m.succ`
          have hsub :
              F E ((m.succ.succ - 1) * n.succ.succ) (Nat.mul_pos (Nat.sub_pos_of_lt hm2) (Nat.succ_pos _)) =
                F E m.succ (Nat.succ_pos _) + F E (n.succ.succ) (Nat.succ_pos _) := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih'
          -- eliminate the binary term and conclude
          have hmPred : 0 < m.succ := Nat.succ_pos _
          have hmPred' : 0 < m.succ := by
            exact hmPred
          have htail : F E (m.succ.succ - 1) (Nat.sub_pos_of_lt hm2) = F E m.succ hmPred := by
            -- `(m.succ.succ - 1) = m.succ` definitionally, only the proof argument differs.
            exact F_congr (E := E) (hn := hmPred') (hn' := hmPred)
          have hrec' :
              F E m.succ.succ hmpos =
                E.H (binaryOneDiv m.succ.succ hmpos) + (1 - (1 : ℝ) / m.succ.succ) * F E m.succ hmPred := by
            simpa [htail] using hrec

          -- Abbreviate the coefficients, so `ring` can work syntactically.
          set a : ℝ := (1 : ℝ) / m.succ.succ
          set b : ℝ := 1 - (1 : ℝ) / m.succ.succ
          have hab : a + b = 1 := by
            simp [a, b, sub_eq_add_neg, add_left_comm, add_comm]

          -- Main algebraic simplification.
          have hmain :
              F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hmpos hnpos) =
                (E.H (binaryOneDiv m.succ.succ hmpos) + b * F E m.succ hmPred) + F E (n.succ.succ) hnpos := by
            calc
              F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hmpos hnpos)
                  =
                E.H (binaryOneDiv m.succ.succ hmpos) + a * F E (n.succ.succ) hnpos +
                  b * F E ((m.succ.succ - 1) * n.succ.succ) (Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos) := by
                    simpa [a, b, hnpos] using hmul
              _ =
                E.H (binaryOneDiv m.succ.succ hmpos) + a * F E (n.succ.succ) hnpos +
                  b * (F E m.succ hmPred + F E (n.succ.succ) hnpos) := by
                    -- Avoid `simp` turning `b * _ = b * _` into a disjunction via `mul_eq_mul_left_iff`.
                    have hsub' :
                        F E ((m.succ.succ - 1) * n.succ.succ) (Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos) =
                          F E m.succ hmPred + F E (n.succ.succ) hnpos := by
                      -- Transport the `n`-proof and the `m.succ`-proof so `hsub` applies.
                      have hN :
                          F E (n.succ.succ) hnpos = F E (n.succ.succ) (Nat.succ_pos _) := by
                        exact F_congr (E := E) (hn := hnpos) (hn' := Nat.succ_pos _)
                      have hM :
                          F E m.succ hmPred = F E m.succ (Nat.succ_pos _) := by
                        exact F_congr (E := E) (hn := hmPred) (hn' := Nat.succ_pos _)
                      have hTail :
                          F E ((m.succ.succ - 1) * n.succ.succ) (Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos) =
                            F E ((m.succ.succ - 1) * n.succ.succ)
                              (Nat.mul_pos (Nat.sub_pos_of_lt hm2) (Nat.succ_pos _)) := by
                        exact
                          F_congr (E := E)
                            (hn := Nat.mul_pos (Nat.sub_pos_of_lt hm2) hnpos)
                            (hn' := Nat.mul_pos (Nat.sub_pos_of_lt hm2) (Nat.succ_pos _))
                      -- Rewrite the goal to match `hsub` exactly.
                      rw [hTail, hM, hN]
                      exact hsub
                    simpa using
                      congrArg
                        (fun t =>
                          E.H (binaryOneDiv m.succ.succ hmpos) +
                            a * F E (n.succ.succ) hnpos + b * t)
                        hsub'
              _ =
                (E.H (binaryOneDiv m.succ.succ hmpos) + b * F E m.succ hmPred) + (a + b) * F E (n.succ.succ) hnpos := by
                    -- Fold large terms so `ring` doesn't duplicate them.
                    set X : ℝ := F E (n.succ.succ) hnpos with hX
                    set Y : ℝ := F E m.succ hmPred with hY
                    set Z : ℝ := E.H (binaryOneDiv m.succ.succ hmpos) with hZ
                    ring
              _ = (E.H (binaryOneDiv m.succ.succ hmpos) + b * F E m.succ hmPred) + F E (n.succ.succ) hnpos := by
                    rw [hab]
                    simp

          -- Convert the bracketed term to `F E (m+2)` using `hrec'`, and finish.
          have hrec'' :
              E.H (binaryOneDiv m.succ.succ hmpos) + b * F E m.succ hmPred = F E m.succ.succ hmpos := by
            simpa [b] using hrec'.symm
          have hfinal :
              F E (m.succ.succ * n.succ.succ) (Nat.mul_pos hmpos hnpos) =
                F E m.succ.succ hmpos + F E (n.succ.succ) hnpos := by
            have h := hmain
            rw [hrec''] at h
            exact h
          exact hfinal

end UniformMultiplicativity

/-! ## Power Laws from Multiplicativity -/

section PowerLaws

/-- F(n^k) = k * F(n) for any Faddeev entropy.
    This follows by induction from the multiplicativity `faddeev_F_mul`. -/
theorem faddeev_F_pow (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    E.H (uniformDist (n ^ k) (by positivity : 0 < n ^ k)) = (k : ℝ) * E.H (uniformDist n hn) := by
  induction k with
  | zero =>
    -- n^0 = 1, F(1) = 0 = 0 * F(n)
    simp only [Nat.cast_zero, zero_mul]
    exact faddeev_F1_eq_zero E
  | succ k ih =>
    -- n^(k+1) = n^k * n
    have hkpos : 0 < n ^ k := by positivity
    have hmulpos : 0 < n ^ k * n := Nat.mul_pos hkpos hn
    have hmul : n ^ (k + 1) = n ^ k * n := by ring
    -- Use faddeev_F_mul
    have hF := faddeev_F_mul E hkpos hn
    -- Need to show: F(n^(k+1)) = (k+1) * F(n)
    -- First, use the congruence lemma to handle proof term differences
    have hgoal :
        E.H (uniformDist (n ^ k * n) hmulpos) = ((k + 1 : ℕ) : ℝ) * E.H (uniformDist n hn) := by
      calc
        E.H (uniformDist (n ^ k * n) hmulpos)
            = E.H (uniformDist (n ^ k) hkpos) + E.H (uniformDist n hn) := hF
        _ = (k : ℝ) * E.H (uniformDist n hn) + E.H (uniformDist n hn) := by rw [ih]
        _ = ((k : ℝ) + 1) * E.H (uniformDist n hn) := by ring
        _ = ((k + 1 : ℕ) : ℝ) * E.H (uniformDist n hn) := by norm_cast
    -- Now transport along `hmul`
    have hcast : uniformDist (n ^ (k + 1)) (by positivity) = uniformDist (n ^ k * n) hmulpos := by
      congr 1  -- unifies n ^ (k + 1) with n ^ k * n by ring/rfl and proof terms by irrelevance
    rw [hcast]
    exact hgoal

/-- F(2^k) = k for any Faddeev entropy.
    This combines the power law with the normalization F(2) = 1. -/
theorem faddeev_F_pow2 (E : FaddeevEntropy) (k : ℕ) :
    E.H (uniformDist (2 ^ k) (by positivity : 0 < 2 ^ k)) = (k : ℝ) := by
  have h := faddeev_F_pow E (by norm_num : 0 < 2) k
  have hF2 := faddeev_F2_eq_one E
  -- F(2^k) = k * F(2) = k * 1 = k
  calc
    E.H (uniformDist (2 ^ k) (by positivity : 0 < 2 ^ k))
        = (k : ℝ) * E.H (uniformDist 2 (by norm_num : 0 < 2)) := h
    _ = (k : ℝ) * 1 := by rw [hF2]
    _ = (k : ℝ) := by ring

end PowerLaws

/-! ## Continuity-Based Uniqueness Proof

A key discovery: if F(3) ≠ log₂(3), then the binary entropy φ(1/n) = H(1/n, (n-1)/n)
diverges along the sequence n = 3^k + 1 as k → ∞, violating continuity at 0.

The mechanism:
- F(3^k) = k * F(3) by multiplicativity
- φ(1/(3^k+1)) = F(3^k+1) - 3^k/(3^k+1) * F(3^k)
- If F(3) = log₂(3) + ε for ε ≠ 0:
  - F(3^k) ≈ k * log₂(3) + k * ε (inflated/deflated by k*ε)
  - F(3^k+1) ≈ log₂(3^k+1) ≈ k * log₂(3) (normal growth)
  - φ(1/(3^k+1)) ≈ k*log₂(3) - k*log₂(3) - k*ε = -k*ε → ∓∞

Since continuity at 0 requires φ(1/n) → 0 as n → ∞, this forces F(3) = log₂(3).
-/

section ContinuityProof

/-- Binary entropy at 0: H(0, 1) = H(1, 0) = 0.
    This is the same as `faddeev_H_one_zero` with symmetry. -/
theorem binaryEntropy_at_zero (E : FaddeevEntropy) :
    E.H (binaryDist 0 (by norm_num) (by norm_num)) = 0 := by
  -- binaryDist 0 = (0, 1), which by symmetry is the same as (1, 0)
  have h_sym : binaryDist 0 (by norm_num) (by norm_num) =
      permute (Equiv.swap 0 1) (binaryDist 1 (by norm_num) (by norm_num)) := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [binaryDist, permute_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [h_sym, E.symmetry]
  exact faddeev_H_one_zero E

/-- The recursion formula for binary entropy:
    φ(1/n) = F(n) - (n-1)/n * F(n-1)

    This is derived from `F_succ_eq`. -/
theorem binary_entropy_recursion (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn)) =
    F E n (Nat.lt_trans Nat.zero_lt_one hn) -
      (1 - (1 : ℝ) / n) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by
  have hF := F_succ_eq E n hn
  -- F(n) = φ(1/n) + (1 - 1/n) * F(n-1)
  -- So φ(1/n) = F(n) - (1 - 1/n) * F(n-1)
  have h_binary_eq : binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn) =
      binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn) := rfl
  linarith [hF]

/-- For the sequence n_k = 3^k + 1, the position 1/n_k approaches 0. -/
theorem inv_three_pow_succ_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (3 ^ k + 1)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k : ℕ => (3 : ℝ) ^ k + 1) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_add
    · exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)
    · exact tendsto_const_nhds
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp h

/-- F(3^k) = k * F(3) by the power law. -/
theorem F_three_pow (E : FaddeevEntropy) (k : ℕ) :
    F E (3 ^ k) (by positivity : 0 < 3 ^ k) =
    (k : ℝ) * F E 3 (by norm_num : 0 < 3) :=
  faddeev_F_pow E (by norm_num : 0 < 3) k

/-! ### Faddeev's Lemma 7: Key Convergence Results

From the recursion η_n = F(n) - (n-1)/n · F(n-1), Faddeev derives:
1. η_n → 0 (from continuity of binary entropy at 0)
2. μ_n = F(n)/n → 0 (via Cesàro mean argument)
3. λ_n = F(n) - F(n-1) → 0 (combines 1 and 2)

These results are crucial for proving uniqueness. -/

/-- η_n = H(1/n, (n-1)/n) = F(n) - (n-1)/n · F(n-1).
    This is the binary entropy at probability 1/n. -/
noncomputable def η (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) : ℝ :=
  E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn))

/-- μ_n = F(n)/n, the normalized entropy of the uniform distribution. -/
noncomputable def μ (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  F E n hn / n

/-- λ_n = F(n) - F(n-1), the entropy increment. -/
noncomputable def entropyIncrement (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) : ℝ :=
  F E n (Nat.lt_trans Nat.zero_lt_one hn) - F E (n - 1) (Nat.sub_pos_of_lt hn)

/-- **Faddeev's Lemma 7, Part 1**: η_n → 0 as n → ∞.
    This follows from continuity of H(p, 1-p) at p = 0.

    Proof: η_n = H(1/n, (n-1)/n), and as n → ∞, 1/n → 0, so by
    continuity of binary entropy, H(1/n, (n-1)/n) → H(0, 1) = 0.

    See `binary_entropy_tendsto_zero` for an equivalent formulation. -/
theorem faddeev_eta_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => η E (n + 2) (by omega : 1 < n + 2))
      Filter.atTop (nhds 0) := by
  -- η E (n+2) = E.H (binaryOneDiv (n+2) _) by definition
  simp only [η]
  -- Define f : Set.Icc 0 1 → ℝ as the binary entropy function
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun p => E.H (binaryDist p.1 p.2.1 p.2.2)
  -- f is continuous by axiom F1
  have hf_cont : Continuous f := E.continuous_binary
  -- Define helper for 1/(n+2) ≤ 1
  have h_le_one : ∀ n : ℕ, (1 : ℝ) / (n + 2) ≤ 1 := fun n => by
    apply div_le_one_of_le₀
    · have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc (1 : ℝ) ≤ 2 := by norm_num
        _ ≤ n + 2 := by linarith
    · positivity
  -- Define the sequence in Set.Icc 0 1
  let seq : ℕ → Set.Icc (0 : ℝ) 1 := fun n =>
    ⟨(1 : ℝ) / (n + 2), by constructor; positivity; exact h_le_one n⟩
  -- seq(n) → 0 in Set.Icc 0 1
  have h_icc : Filter.Tendsto seq Filter.atTop (nhds ⟨0, by norm_num, by norm_num⟩) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- 1/(n+2) < ε when n > 1/ε - 2
    obtain ⟨N, hN⟩ := exists_nat_gt (1/ε - 2)
    use N
    intro n hn
    simp only [seq, Subtype.dist_eq, Real.dist_eq, sub_zero]
    have h_pos : (0 : ℝ) < n + 2 := by positivity
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (n + 2))]
    rw [div_lt_iff₀ h_pos]
    have hn_ge : (n : ℝ) ≥ N := Nat.cast_le.mpr hn
    calc ε * (n + 2) > ε * (1/ε - 2 + 2) := by nlinarith
      _ = ε * (1/ε) := by ring
      _ = 1 := mul_one_div_cancel hε.ne'
  -- By continuity, f(seq(n)) → f(0)
  have h_comp : Filter.Tendsto (f ∘ seq) Filter.atTop (nhds (f ⟨0, by norm_num, by norm_num⟩)) :=
    hf_cont.continuousAt.tendsto.comp h_icc
  -- f(0) = H(0, 1) = 0
  have hzero := binaryEntropy_at_zero E
  simp only [f] at h_comp hzero
  rw [← hzero]
  -- Show our goal equals f ∘ seq
  refine Filter.Tendsto.congr ?_ h_comp
  intro n
  simp only [Function.comp_apply, seq, binaryOneDiv]
  congr 1
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The key recursion: n·η_n = n·F(n) - (n-1)·F(n-1).
    Rearranging: n·F(n) = (n-1)·F(n-1) + n·η_n.

    Proof: From η_n = F(n) - (n-1)/n · F(n-1), multiply by n:
    n·η_n = n·F(n) - (n-1)·F(n-1). -/
theorem n_eta_eq (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    (n : ℝ) * η E n hn = (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) -
      ((n : ℝ) - 1) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by
  -- From the recursion formula: η_n = F(n) - (1 - 1/n) · F(n-1)
  -- Multiply by n: n · η_n = n · F(n) - (n-1) · F(n-1)
  simp only [η]
  have hrec := binary_entropy_recursion E n hn
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  -- η_n = F(n) - (1 - 1/n) · F(n-1)
  -- n · η_n = n · F(n) - n · (1 - 1/n) · F(n-1)
  --         = n · F(n) - (n - 1) · F(n-1)
  calc (n : ℝ) * E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn))
      = (n : ℝ) * (F E n (Nat.lt_trans Nat.zero_lt_one hn) -
          (1 - (1 : ℝ) / n) * F E (n - 1) (Nat.sub_pos_of_lt hn)) := by rw [hrec]
    _ = (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) -
          (n : ℝ) * (1 - (1 : ℝ) / n) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by ring
    _ = (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) -
          ((n : ℝ) - 1) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by
        congr 1
        field_simp

/-- **Telescoping recursion**: n·F(n) = (n-1)·F(n-1) + n·η_n for n ≥ 2.

    This is a rearrangement of n_eta_eq. -/
theorem nF_recursion (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) =
    ((n : ℝ) - 1) * F E (n - 1) (Nat.sub_pos_of_lt hn) + (n : ℝ) * η E n hn := by
  have h := n_eta_eq E n hn
  linarith

/-- Base case: 2·F(2) = 2·η_2.

    Since F(1) = 0, we have 2·F(2) = 1·F(1) + 2·η_2 = 2·η_2. -/
theorem nF_base (E : FaddeevEntropy) :
    (2 : ℝ) * F E 2 (by norm_num : 0 < 2) = (2 : ℝ) * η E 2 (by norm_num : 1 < 2) := by
  have h := nF_recursion E 2 (by norm_num : 1 < 2)
  have hF1 : F E 1 (by norm_num : 0 < 1) = 0 := faddeev_F1_eq_zero E
  -- h : 2 * F E 2 _ = (2 - 1) * F E (2 - 1) _ + 2 * η E 2 _
  -- Since 2 - 1 = 1 and F(1) = 0:
  have h2 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  have h3 : (2 : ℕ) - 1 = 1 := by norm_num
  simp only [h3] at h
  rw [h2] at h
  simp only [one_mul, hF1, zero_add] at h
  simpa using h

/-- Extended η function: returns 0 for k ≤ 1, otherwise η E k.
    This makes it easier to sum over intervals without proof obligations. -/
noncomputable def ηExt (E : FaddeevEntropy) (k : ℕ) : ℝ :=
  if hk : 1 < k then η E k hk else 0

/-- ηExt agrees with η when k > 1. -/
theorem ηExt_eq (E : FaddeevEntropy) (k : ℕ) (hk : 1 < k) :
    ηExt E k = η E k hk := by
  simp [ηExt, hk]

/-- **Telescoping sum identity**: n·F(n) = Σ_{k=2}^n k·ηExt(k) for n ≥ 2.

    Proof by strong induction using nF_recursion and nF_base. -/
theorem telescoping_nF_sum (E : FaddeevEntropy) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * F E n (Nat.lt_of_lt_of_le Nat.zero_lt_two hn) =
    ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * ηExt E k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · -- n = 2: base case
      subst hn2
      simp only [Finset.Icc_self, Finset.sum_singleton]
      have h2 : ηExt E 2 = η E 2 (by norm_num : 1 < 2) := ηExt_eq E 2 (by norm_num)
      rw [h2]
      exact nF_base E
    · -- n ≥ 3: use IH on n-1 and nF_recursion
      have hn_gt : 2 < n := Nat.lt_of_le_of_ne hn (Ne.symm hn2)
      have hn1 : 2 ≤ n - 1 := by omega
      have hn1_lt : n - 1 < n := by omega
      -- Split: Σ_{k=2}^n = Σ_{k=2}^{n-1} + n·ηExt(n)
      have hsplit : Finset.Icc 2 n = Finset.Icc 2 (n - 1) ∪ {n} := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        omega
      have hdisj : Disjoint (Finset.Icc 2 (n - 1)) {n} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton]
      -- Use IH: (n-1)·F(n-1) = Σ_{k=2}^{n-1} k·ηExt(k)
      have hih := ih (n - 1) hn1_lt hn1
      -- Use recursion: n·F(n) = (n-1)·F(n-1) + n·η_n
      have hrec := nF_recursion E n (by omega : 1 < n)
      -- Combine
      have h_cast : ((n : ℕ) : ℝ) - 1 = (n - 1 : ℕ) := by
        simp only [Nat.cast_sub (Nat.one_le_of_lt hn_gt), Nat.cast_one]
      rw [h_cast] at hrec
      -- Connect ηExt to η
      have hηExt : ηExt E n = η E n (by omega : 1 < n) :=
        ηExt_eq E n (by omega)
      -- hrec: n * F(n) = (n-1) * F(n-1) + n * η(n)
      -- The proof combines the telescoping identity with the induction hypothesis
      simp_rw [hrec, hηExt, hih]

/-- **Faddeev's Lemma 7, Part 2**: μ_n = F(n)/n → 0 as n → ∞.

    The proof uses a bound from the telescoping sum: |μ_n| ≤ Σ|η_k|/n.
    Since η_k → 0, the Cesàro-type argument shows the weighted average → 0.

    Key insight: From telescoping, (n+1)·F(n+1) = Σ_{k=2}^{n+1} k·η_k.
    We have |Σ k·η_k| ≤ (n+1)·Σ|η_k|, so |μ(n+1)| ≤ Σ|η_k|/(n+1) → 0.

    Mathematical proof is verified; Lean formalization requires careful handling
    of type coercions between ℕ and ℝ. -/
theorem faddeev_mu_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => μ E (n + 1) (Nat.succ_pos n))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get K such that |η(k+2)| < ε/2 for k ≥ K
  have hη := faddeev_eta_tendsto_zero E
  rw [Metric.tendsto_atTop] at hη
  obtain ⟨K, hK⟩ := hη (ε / 2) (by linarith)
  -- For k ≥ K + 2, |ηExt(k)| < ε/2
  have hη_bound : ∀ k : ℕ, K + 2 ≤ k → |ηExt E k| < ε / 2 := by
    intro k hk
    have hk1 : 1 < k := Nat.lt_of_lt_of_le (by omega : 1 < K + 2) hk
    have hk2 : 2 ≤ k := hk1
    rw [ηExt_eq E k hk1]
    specialize hK (k - 2) (by omega : K ≤ k - 2)
    simp only [Real.dist_eq, sub_zero] at hK
    have heq : (k - 2) + 2 = k := Nat.sub_add_cancel hk2
    simp only [heq, η] at hK
    exact hK
  -- Define M = sum of |ηExt(k)| for k in [2, K+1]
  let M : ℝ := ∑ k ∈ Finset.Icc 2 (K + 1), |ηExt E k|
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  -- Choose N large enough: N > max(K+1, 2M/ε)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * M / ε)
  let N := max N₁ (K + 2)
  use N
  intro n hn
  simp only [Real.dist_eq, sub_zero]
  -- We need: |μ(n+1)| < ε
  -- From telescoping: (n+1)·F(n+1) = Σ_{k=2}^{n+1} k·ηExt(k)
  have hn1_ge2 : 2 ≤ n + 1 := by omega
  have htele := telescoping_nF_sum E (n + 1) hn1_ge2
  have hn_ge_K2 : K + 2 ≤ n := Nat.le_trans (le_max_right N₁ (K + 2)) hn
  have hn1_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hn1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos
  have hn1_sq_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
  -- μ(n+1) = F(n+1)/(n+1) = Σ k·ηExt(k) / (n+1)²
  simp only [μ]
  have hF_eq : F E (n + 1) (Nat.succ_pos n) =
      (∑ k ∈ Finset.Icc 2 (n + 1), (k : ℝ) * ηExt E k) / ((n + 1 : ℕ) : ℝ) := by
    have h := htele
    field_simp [hn1_ne] at h ⊢
    linarith
  rw [hF_eq]
  rw [div_div]
  -- Transform |sum / denom| to |sum| / denom since denom > 0
  rw [abs_div, abs_of_pos hn1_sq_pos]
  -- Goal: |Σ k·ηExt(k)| / (n+1)² < ε
  -- Bound: |Σ k·ηExt(k)| ≤ (n+1) · Σ|ηExt(k)|
  have hsum_abs_bound : |∑ k ∈ Finset.Icc 2 (n + 1), (k : ℝ) * ηExt E k| ≤
      ((n + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k| := by
    calc |∑ k ∈ Finset.Icc 2 (n + 1), (k : ℝ) * ηExt E k|
        ≤ ∑ k ∈ Finset.Icc 2 (n + 1), |(k : ℝ) * ηExt E k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.Icc 2 (n + 1), (k : ℝ) * |ηExt E k| := by
          congr 1; ext k; rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ ∑ k ∈ Finset.Icc 2 (n + 1), ((n + 1 : ℕ) : ℝ) * |ηExt E k| := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          simp only [Finset.mem_Icc] at hk
          exact Nat.cast_le.mpr hk.2
      _ = ((n + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k| :=
          (Finset.mul_sum (Finset.Icc 2 (n + 1)) (fun k => |ηExt E k|) _).symm
  -- Split the sum: [2, K+1] ∪ [K+2, n+1]
  have hsplit : Finset.Icc 2 (n + 1) = Finset.Icc 2 (K + 1) ∪ Finset.Icc (K + 2) (n + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 2 (K + 1)) (Finset.Icc (K + 2) (n + 1)) := by
    simp only [Finset.disjoint_iff_ne, Finset.mem_Icc]; intro a ha b hb; omega
  have hsum_split : ∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k| =
      M + ∑ k ∈ Finset.Icc (K + 2) (n + 1), |ηExt E k| := by
    rw [hsplit, Finset.sum_union hdisj]
  -- Bound the second part: each term < ε/2, and there are at most n terms
  have hcard_bound : (Finset.Icc (K + 2) (n + 1)).card ≤ n := by
    simp only [Nat.card_Icc]
    omega
  have hsum2_bound : ∑ k ∈ Finset.Icc (K + 2) (n + 1), |ηExt E k| ≤ n * (ε / 2) := by
    calc ∑ k ∈ Finset.Icc (K + 2) (n + 1), |ηExt E k|
        ≤ ∑ _k ∈ Finset.Icc (K + 2) (n + 1), (ε / 2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk_ge : K + 2 ≤ k := by simp only [Finset.mem_Icc] at hk; exact hk.1
          exact le_of_lt (hη_bound k hk_ge)
      _ = (Finset.Icc (K + 2) (n + 1)).card * (ε / 2) := by simp [Finset.sum_const]
      _ ≤ n * (ε / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ ε / 2)
          exact Nat.cast_le.mpr hcard_bound
  -- Total sum bound
  have htotal_bound : ∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k| ≤ M + n * (ε / 2) := by
    rw [hsum_split]
    linarith [hsum2_bound]
  -- Now combine: |μ(n+1)| ≤ (M + n·ε/2) / (n+1)
  calc |∑ k ∈ Finset.Icc 2 (n + 1), (k : ℝ) * ηExt E k| / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
      ≤ (((n + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k|) /
          (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_right hsum_abs_bound; positivity
    _ = (∑ k ∈ Finset.Icc 2 (n + 1), |ηExt E k|) / ((n + 1 : ℕ) : ℝ) := by
        field_simp
    _ ≤ (M + n * (ε / 2)) / ((n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right htotal_bound; positivity
    _ = M / ((n + 1 : ℕ) : ℝ) + (n : ℝ) * (ε / 2) / ((n + 1 : ℕ) : ℝ) := by ring
    _ ≤ M / ((n + 1 : ℕ) : ℝ) + ε / 2 := by
        apply add_le_add_left
        have h1 : (n : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
          simp only [Nat.cast_add, Nat.cast_one]
          linarith
        calc (n : ℝ) * (ε / 2) / ((n + 1 : ℕ) : ℝ)
            = (n : ℝ) / ((n + 1 : ℕ) : ℝ) * (ε / 2) := by ring
          _ ≤ 1 * (ε / 2) := by apply mul_le_mul_of_nonneg_right h1 (by linarith)
          _ = ε / 2 := one_mul _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_right
        -- M / (n+1) < ε/2 because n ≥ N₁ > 2M/ε, so n+1 > 2M/ε
        have hn_ge_N1 : N₁ ≤ n := Nat.le_trans (le_max_left N₁ (K + 2)) hn
        have h2 : ((n + 1 : ℕ) : ℝ) > 2 * M / ε := by
          calc ((n + 1 : ℕ) : ℝ) > (n : ℝ) := by simp
            _ ≥ (N₁ : ℝ) := Nat.cast_le.mpr hn_ge_N1
            _ > 2 * M / ε := hN₁
        by_cases hM_zero : M = 0
        · simp [hM_zero]; linarith
        · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
          calc M / ((n + 1 : ℕ) : ℝ) < M / (2 * M / ε) := by
                apply div_lt_div_of_pos_left hM_pos _ h2
                apply div_pos (by linarith) hε
            _ = ε / 2 := by field_simp
    _ = ε := by ring

/-- Key algebraic identity: entropyIncrement(n) = η(n) - F(n-1)/n.

    From binary_entropy_recursion: η_n = F(n) - (1-1/n)·F(n-1)
    Rearranging: F(n) = η_n + (n-1)/n · F(n-1)
    So: λ_n = F(n) - F(n-1) = η_n - F(n-1)/n -/
theorem entropyIncrement_eq_eta_sub_mu (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    entropyIncrement E n hn = η E n hn - F E (n - 1) (Nat.sub_pos_of_lt hn) / n := by
  simp only [entropyIncrement, η]
  have hrec := binary_entropy_recursion E n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lt_trans Nat.zero_lt_one hn).ne'
  -- hrec: η = F(n) - (1 - 1/n) * F(n-1)
  -- So: F(n) = η + (1 - 1/n) * F(n-1)
  -- F(n) - F(n-1) = η + (1 - 1/n) * F(n-1) - F(n-1)
  --               = η + ((1 - 1/n) - 1) * F(n-1)
  --               = η - (1/n) * F(n-1)
  --               = η - F(n-1)/n
  have h : F E n (Nat.lt_trans Nat.zero_lt_one hn) - F E (n - 1) (Nat.sub_pos_of_lt hn) =
      E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn)) -
      F E (n - 1) (Nat.sub_pos_of_lt hn) / ↑n := by
    have := hrec
    field_simp [hn0] at this ⊢
    linarith
  exact h

/-- **Faddeev's Lemma 7, Part 3**: λ_n = F(n) - F(n-1) → 0 as n → ∞.

    This follows from the algebraic identity: λ_n = η_n - F(n-1)/n.
    Since η_n → 0 (Part 1) and μ_n = F(n)/n → 0 (Part 2), we have:
    - F(n-1)/n = μ_{n-1} · (n-1)/n → 0 · 1 = 0
    - Therefore λ_n = η_n - F(n-1)/n → 0 - 0 = 0

    The proof uses Filter.Tendsto arithmetic (subtraction and bounded multiplication). -/
theorem faddeev_lambda_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => entropyIncrement E (n + 2) (by omega : 1 < n + 2))
      Filter.atTop (nhds 0) := by
  have hη := faddeev_eta_tendsto_zero E
  have hμ := faddeev_mu_tendsto_zero E
  -- Direct ε-δ proof using η → 0 and μ → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get N₁ such that |η(n+2)| < ε/2 for n ≥ N₁
  rw [Metric.tendsto_atTop] at hη
  obtain ⟨N₁, hN₁⟩ := hη (ε / 2) (by linarith)
  -- Get N₂ such that |μ(n+1)| < ε/2 for n ≥ N₂
  rw [Metric.tendsto_atTop] at hμ
  obtain ⟨N₂, hN₂⟩ := hμ (ε / 2) (by linarith)
  use max N₁ N₂
  intro n hn
  simp only [Real.dist_eq, sub_zero]
  -- The term F(n+1)/(n+2) = μ(n+1) * (n+1)/(n+2) is bounded by |μ(n+1)|
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn2_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hfrac_le1 : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hn2_pos]
    exact Nat.cast_le.mpr (Nat.le_succ (n + 1))
  have hfrac_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  -- |entropyIncrement| ≤ |η| + |F(n+1)/(n+2)|
  -- We have |η| < ε/2 (by hN₁) and |F(n+1)/(n+2)| ≤ |μ(n+1)| < ε/2 (by hN₂)
  have hn_ge_N1 : N₁ ≤ n := Nat.le_trans (le_max_left N₁ N₂) hn
  have hn_ge_N2 : N₂ ≤ n := Nat.le_trans (le_max_right N₁ N₂) hn
  specialize hN₁ n hn_ge_N1
  specialize hN₂ n hn_ge_N2
  simp only [Real.dist_eq, sub_zero] at hN₁ hN₂
  -- |F(n+1)/(n+2)| = |μ(n+1)| * (n+1)/(n+2) ≤ |μ(n+1)|
  have hF_bound : |F E (n + 1) (Nat.succ_pos n) / ((n + 2 : ℕ) : ℝ)| < ε / 2 := by
    simp only [μ] at hN₂
    have h1 : F E (n + 1) (Nat.succ_pos n) / ((n + 2 : ℕ) : ℝ) =
        (F E (n + 1) (Nat.succ_pos n) / ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by
      field_simp
    rw [h1, abs_mul]
    calc |F E (n + 1) (Nat.succ_pos n) / ((n + 1 : ℕ) : ℝ)| *
            |((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)|
        ≤ |F E (n + 1) (Nat.succ_pos n) / ((n + 1 : ℕ) : ℝ)| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg hfrac_nonneg]; exact hfrac_le1
      _ = |F E (n + 1) (Nat.succ_pos n) / ((n + 1 : ℕ) : ℝ)| := mul_one _
      _ < ε / 2 := hN₂
  -- Use the proven identity: entropyIncrement(n+2) = η(n+2) - F(n+2-1)/(n+2)
  have h_ident := entropyIncrement_eq_eta_sub_mu E (n + 2) (by omega : 1 < n + 2)
  -- Note: n + 2 - 1 = n + 1
  have hn21 : n + 2 - 1 = n + 1 := by omega
  -- Bound |F(n+2-1)/(n+2)| using that it equals μ(n+1) * (n+1)/(n+2) ≤ μ(n+1)
  have hF_bound' : |F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / ((n + 2 : ℕ) : ℝ)| < ε / 2 := by
    have h1 : F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / ((n + 2 : ℕ) : ℝ) =
        (F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / (((n + 2 - 1 : ℕ) : ℕ) : ℝ)) *
        ((((n + 2 - 1 : ℕ) : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by
      simp only [hn21]; field_simp
    rw [h1, abs_mul]
    have hfrac' : (((n + 2 - 1 : ℕ) : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by simp only [hn21]
    rw [hfrac']
    calc |F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / (((n + 2 - 1 : ℕ) : ℕ) : ℝ)| *
            |((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)|
        ≤ |F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / (((n + 2 - 1 : ℕ) : ℕ) : ℝ)| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg hfrac_nonneg]; exact hfrac_le1
      _ = |F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / (((n + 2 - 1 : ℕ) : ℕ) : ℝ)| := mul_one _
      _ = |F E (n + 1) (Nat.succ_pos n) / ((n + 1 : ℕ) : ℝ)| := by simp only [hn21]
      _ < ε / 2 := by simp only [μ] at hN₂; exact hN₂
  -- Now use triangle inequality
  calc |entropyIncrement E (n + 2) (by omega : 1 < n + 2)|
      = |η E (n + 2) (by omega : 1 < n + 2) -
          F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / ((n + 2 : ℕ) : ℝ)| := by
        rw [h_ident]
    _ ≤ |η E (n + 2) (by omega : 1 < n + 2)| +
          |F E (n + 2 - 1) (Nat.sub_pos_of_lt (by omega : 1 < n + 2)) / ((n + 2 : ℕ) : ℝ)| :=
        abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hN₁ hF_bound'
    _ = ε := by ring

/-! ### Faddeev's Lemmas 8-9: Uniqueness WITHOUT Monotonicity

This is the correct approach to break the circular dependency!

**The Hinge Lemma**: If F satisfies multiplicativity (M) and the limit conditions (L7),
then F(n) = c·log(n) for a constant c.

**Strategy** (following Faddeev's original paper):
1. Define c_p := F(p)/log(p) for each prime p
2. **Lemma 8**: The set {c_p | p prime} has a maximum and a minimum
3. **Lemma 9**: All c_p are equal (to c_2)
4. Therefore F(n) = c·log(n), and by normalization F(2)=1, we get F(n)=log₂(n)
5. Monotonicity follows trivially since log is monotone

**Key Innovation**: Uses only λ_n → 0 (which we derived from continuity), NOT monotonicity.
This breaks the circle: we prove F = log₂ first, THEN get monotonicity for free.

**Lemma 8 Proof Sketch**:
Assume {c_p} has no maximum. Build increasing sequence p₁ < p₂ < ... with c_{p₁} < c_{p₂} < ...
For p_i - 1 = ∏ q_j^{α_j}, all q_j < p_i, so c_{q_j} < c_{p_i}.
Write exact identity: λ_{p_i} = c_{p_i}(log p_i - log(p_i-1)) + Σ_j α_j(c_{p_i} - c_{q_j})log q_j
Since 2 | (p_i - 1), the sum ≥ (c_{p_i} - c_2)log 2 > 0 (uniform lower bound).
But λ_{p_i} → 0 by Lemma 7, contradiction!

**Lemma 9 Proof Sketch**:
Similar argument on p^m - 1 shows c_{p_max} ≤ c_2 and c_{p_min} ≥ c_2.
Hence all c_p = c_2. -/

/-- The "slope coefficient" for a prime: c_p = F(p)/log(p).

    By multiplicativity, F is determined by its values on primes.
    Faddeev's strategy: prove all c_p are equal, hence F(n) = c·log(n). -/
noncomputable def c_prime (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : ℝ :=
  F E p (Nat.Prime.pos hp) / Real.log p

/-! ### Helper Lemmas for Faddeev's Argument -/

/-- For odd primes p > 2, we have 2 | (p - 1).
    This is crucial for the uniform lower bound in Lemma 8. -/
theorem prime_odd_pred_even {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) : Even (p - 1) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  use k
  omega

/-- For any n ≥ 2, log(n) > 0. -/
theorem log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n := by
  have h1 : 1 < n := Nat.one_lt_two.trans_le hn
  have : (1 : ℝ) < n := Nat.one_lt_cast.mpr h1
  exact Real.log_pos this

/-- c_p is well-defined: log(p) ≠ 0 for primes p. -/
theorem log_prime_ne_zero {p : ℕ} (hp : Nat.Prime p) : Real.log p ≠ 0 := by
  have : 0 < Real.log p := log_pos_of_two_le hp.two_le
  exact this.ne'

/-- Express F(p) in terms of c_p. -/
theorem F_prime_eq_c_times_log (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) :
    F E p (Nat.Prime.pos hp) = c_prime E p hp * Real.log p := by
  unfold c_prime
  field_simp [log_prime_ne_zero hp]

/-- c_2 = 1 follows from F(2) = 1 and log(2) > 0. -/
theorem c_prime_two (E : FaddeevEntropy) :
    c_prime E 2 Nat.prime_two = 1 / Real.log 2 := by
  unfold c_prime
  have hF2 := faddeev_F2_eq_one E
  simp [F, hF2]

/-- For primes p ≥ 3, c_p is positive if F(p) > 0. -/
theorem c_prime_pos_of_F_pos (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hFp : 0 < F E p (Nat.Prime.pos hp)) :
    0 < c_prime E p hp := by
  unfold c_prime
  have hlog_pos := log_pos_of_two_le hp.two_le
  exact div_pos hFp hlog_pos

/-- log 2 is positive and nonzero. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem log_two_ne_zero : Real.log 2 ≠ 0 := log_two_pos.ne'

/-- c_2 equals 1/log(2), which is well-defined and positive. -/
theorem c_prime_two_pos (E : FaddeevEntropy) : 0 < c_prime E 2 Nat.prime_two := by
  rw [c_prime_two]
  exact div_pos (by norm_num) log_two_pos

/-- If all c_p are equal to c_2, then F(n) = c_2 · log(n) for all n ≥ 1.

    This is the payoff of Lemma 9: once we know all c_p are equal,
    multiplicativity gives us F on all of ℕ. -/
theorem F_eq_c2_times_log_of_c_prime_const (E : FaddeevEntropy)
    (h_const : ∀ p : ℕ, ∀ hp : Nat.Prime p, c_prime E p hp = c_prime E 2 Nat.prime_two)
    {n : ℕ} (hn : 0 < n) :
    F E n hn = c_prime E 2 Nat.prime_two * Real.log n := by
  -- Proof by strong induction on n.
  -- Case n = 1: F(1) = 0 and log(1) = 0, so both sides equal 0.
  -- Case n > 1: Either n is prime (use hypothesis) or n = m * k (use multiplicativity + IH).
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · -- n = 1
      subst h1
      have hF1 : F E 1 (by norm_num : 0 < 1) = 0 := faddeev_F1_eq_zero E
      have hlog1 : Real.log 1 = 0 := Real.log_one
      simp [hF1, hlog1]
    · -- n > 1
      have h2 : 1 < n := by omega
      by_cases hprime : n.Prime
      · -- n is prime
        have hFp := F_prime_eq_c_times_log E hprime
        rw [hFp, h_const n hprime]
      · -- n is composite
        -- Get a nontrivial factorization using minFac
        set m := n.minFac with hm_def
        have hm_prime : m.Prime := Nat.minFac_prime (ne_of_gt h2)
        have hm_dvd : m ∣ n := n.minFac_dvd
        have hm_pos : 0 < m := hm_prime.pos
        have hm_lt : m < n := by
          have : m ≠ n := fun h => hprime (h ▸ hm_prime)
          exact Nat.lt_of_le_of_ne (Nat.le_of_dvd hn hm_dvd) this
        set k := n / m with hk_def
        have hdiv : m * k = n := by
          rw [mul_comm]
          exact Nat.div_mul_cancel hm_dvd
        have hk_pos : 0 < k := by
          by_contra h_not
          push_neg at h_not
          have : n = m * k := hdiv.symm
          simp [Nat.le_zero.mp h_not] at this
          omega
        have hk_lt : k < n := by
          -- k = n/m and m ≥ 2, so k ≤ n/2 < n
          have hm_ge_2 : 2 ≤ m := hm_prime.two_le
          have h_div_le : n / m ≤ n / 2 := Nat.div_le_div_left hm_ge_2 (by omega : 0 < 2)
          have h_div_lt : n / 2 < n := Nat.div_lt_self hn (by omega : 1 < 2)
          omega
        -- Apply IH to m and k
        have ihm := ih m hm_lt hm_pos
        have ihk := ih k hk_lt hk_pos
        -- Use multiplicativity: F(m*k) = F(m) + F(k) = c₂·log(m) + c₂·log(k) = c₂·log(m*k)
        have hmk_pos : 0 < m * k := Nat.mul_pos hm_pos hk_pos
        have hFmk := faddeev_F_mul E hm_pos hk_pos
        -- F(m*k) = F(m) + F(k) = c₂·log(m) + c₂·log(k) = c₂·(log(m) + log(k)) = c₂·log(m*k)
        have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
        have hk_real_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
        calc F E n hn = F E (m * k) (hdiv ▸ hn) := by
              congr 1
              exact hdiv.symm
          _ = F E (m * k) hmk_pos := by rfl
          _ = F E m hm_pos + F E k hk_pos := hFmk
          _ = c_prime E 2 Nat.prime_two * Real.log m +
              c_prime E 2 Nat.prime_two * Real.log k := by rw [ihm, ihk]
          _ = c_prime E 2 Nat.prime_two * (Real.log m + Real.log k) := by ring
          _ = c_prime E 2 Nat.prime_two * Real.log (m * k) := by
              rw [Real.log_mul hm_real_pos.ne' hk_real_pos.ne']
          _ = c_prime E 2 Nat.prime_two * Real.log n := by
              congr 1
              have hmk_eq_n : (m * k : ℝ) = (n : ℝ) := by
                rw [← Nat.cast_mul]
                exact congrArg Nat.cast hdiv
              rw [hmk_eq_n]

/-- F(2^a * m) = a + F(m) for any m > 0. This uses multiplicativity and F(2^a) = a. -/
theorem F_two_pow_mul (E : FaddeevEntropy) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    F E (2 ^ a * m) (by positivity : 0 < 2 ^ a * m) = a + F E m hm := by
  have h2a_pos : 0 < 2 ^ a := by positivity
  have hFmul := faddeev_F_mul E h2a_pos hm
  have hF2a := faddeev_F_pow2 E a
  -- F(2^a) = a by faddeev_F_pow2, need to handle proof term differences
  have hF2a' : F E (2 ^ a) h2a_pos = (a : ℝ) := by
    simp only [F] at hF2a ⊢
    convert hF2a using 2
  calc F E (2 ^ a * m) (by positivity)
      = F E (2 ^ a) h2a_pos + F E m hm := hFmul
    _ = (a : ℝ) + F E m hm := by rw [hF2a']

/-- For odd n > 0, if c ≥ c_q for all odd primes q | n, then F(n) ≤ c · log(n).
    Proof by strong induction using multiplicativity.

    This is the key technical lemma for lambda_prime_lower_bound.
    The proof uses strong induction: factor out the smallest prime q from n,
    write n = q^b * m, and apply IH to m. -/
theorem F_odd_upper_bound (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (h_odd : Odd n)
    (c : ℝ) (h_dom : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ n → Odd q → c_prime E q hq ≤ c) :
    F E n hn ≤ c * Real.log n := by
  -- Proof by strong induction on n.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · -- Base case: n = 1
      subst h1
      have hF1 : F E 1 (by norm_num : 0 < 1) = 0 := faddeev_F1_eq_zero E
      have hlog1 : Real.log 1 = 0 := Real.log_one
      simp [hF1, hlog1]
    · -- Inductive case: n > 1
      have h_gt_1 : 1 < n := by omega
      -- n is odd and n > 1, so minFac(n) is an odd prime
      set q := n.minFac with hq_def
      have hq_prime : q.Prime := Nat.minFac_prime (ne_of_gt h_gt_1)
      have hq_dvd : q ∣ n := n.minFac_dvd
      -- q is odd since n is odd and q | n
      have hq_odd : Odd q := by
        by_contra hq_not_odd
        rw [Nat.not_odd_iff_even] at hq_not_odd
        have hq_two : q = 2 := (Nat.Prime.eq_one_or_self_of_dvd hq_prime 2
          hq_not_odd.two_dvd).resolve_left (by omega) |>.symm
        rw [hq_two] at hq_dvd
        exact h_odd.not_two_dvd_nat hq_dvd
      -- Use Nat.exists_eq_pow_mul_and_not_dvd to factor n = q^k * m with q ∤ m
      obtain ⟨k, m, hq_not_dvd, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq_prime.ne_one
      have hm_pos : 0 < m := by
        by_contra hm_not_pos
        push_neg at hm_not_pos
        simp [Nat.le_zero.mp hm_not_pos] at hn_eq
        omega
      -- m is odd (since n = q^k * m is odd, q is odd, so q^k is odd, so m is odd)
      have hm_odd : Odd m := by
        rw [hn_eq] at h_odd
        exact (Nat.odd_mul.mp h_odd).2
      -- k ≥ 1 since q | n
      have hk_pos : 0 < k := by
        by_contra hk_zero
        push_neg at hk_zero
        have hk_eq : k = 0 := Nat.le_zero.mp hk_zero
        simp [hk_eq] at hn_eq
        rw [hn_eq] at hq_dvd
        exact hq_not_dvd hq_dvd
      -- m < n since m = n / q^k and q^k ≥ q ≥ 3
      have hm_lt_n : m < n := by
        have hqk_ge_q : q ^ k ≥ q := Nat.le_self_pow (ne_of_gt hk_pos) q
        have hq_ne_2 : q ≠ 2 := fun h => hq_odd.not_two_dvd_nat (h ▸ dvd_refl q)
        have hq_ge_2 := hq_prime.two_le
        have hq_ge_3 : q ≥ 3 := by omega
        have hqk_gt_1 : 1 < q ^ k := by
          have hq_pos : 0 < q := hq_prime.pos
          calc 1 < q := hq_prime.one_lt
            _ ≤ q ^ k := Nat.le_self_pow (ne_of_gt hk_pos) q
        calc m = n / q ^ k := by rw [hn_eq]; simp [Nat.mul_div_cancel_left _ (by positivity : 0 < q ^ k)]
          _ < n := Nat.div_lt_self hn hqk_gt_1
      -- All odd prime divisors of m also divide n, so they satisfy h_dom
      have h_dom_m : ∀ r : ℕ, ∀ hr : r.Prime, r ∣ m → Odd r → c_prime E r hr ≤ c := by
        intro r hr hr_dvd hr_odd
        have hr_dvd_n : r ∣ n := by
          rw [hn_eq]
          exact Dvd.dvd.mul_left hr_dvd (q ^ k)
        exact h_dom r hr hr_dvd_n hr_odd
      -- Apply IH to m
      have ihm := ih m hm_lt_n hm_pos hm_odd h_dom_m
      -- c_q ≤ c by h_dom
      have hcq_le : c_prime E q hq_prime ≤ c := h_dom q hq_prime hq_dvd hq_odd
      -- F(q) = c_q · log(q) ≤ c · log(q)
      have hFq := F_prime_eq_c_times_log E hq_prime
      have hFq_le : F E q hq_prime.pos ≤ c * Real.log q := by
        rw [hFq]
        have hlog_pos : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le : 1 ≤ (q : ℝ))
        exact mul_le_mul_of_nonneg_right hcq_le hlog_pos
      -- F(q^k) = k · F(q) by faddeev_F_pow
      have hFqk := faddeev_F_pow E hq_prime.pos k
      -- F(q^k) ≤ k · c · log(q) = c · log(q^k)
      have hq_pos : 0 < q := hq_prime.pos
      have hqk_pos : 0 < q ^ k := pow_pos hq_pos k
      have hFqk_le : F E (q ^ k) hqk_pos ≤ c * Real.log (q ^ k) := by
        have hFqk' : F E (q ^ k) hqk_pos = (k : ℝ) * F E q hq_prime.pos := by
          simp only [F] at hFqk ⊢
          convert hFqk using 2
        rw [hFqk']
        have h1 : (k : ℝ) * F E q hq_prime.pos ≤ (k : ℝ) * (c * Real.log q) := by
          apply mul_le_mul_of_nonneg_left hFq_le
          exact Nat.cast_nonneg k
        calc (k : ℝ) * F E q hq_prime.pos ≤ (k : ℝ) * (c * Real.log q) := h1
          _ = c * ((k : ℝ) * Real.log q) := by ring
          _ = c * Real.log (q ^ k) := by rw [Real.log_pow]
      -- F(n) = F(q^k · m) = F(q^k) + F(m) by multiplicativity
      have hFn := faddeev_F_mul E hqk_pos hm_pos
      have hn_eq' : q ^ k * m = n := hn_eq.symm
      have hqkm_pos : 0 < q ^ k * m := by positivity
      -- Final calculation
      have hlog_pos_m : 0 ≤ Real.log m :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm_pos.ne' : (1 : ℝ) ≤ m)
      have hlog_pos_qk : 0 ≤ Real.log (q ^ k) := Real.log_nonneg (by
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq_prime.one_lt.le
        exact one_le_pow₀ hq1)
      have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      have hqk_real_pos : (0 : ℝ) < (q : ℝ) ^ k := by
        rw [← Nat.cast_pow]
        exact Nat.cast_pos.mpr hqk_pos
      have hF_eq : F E n hn = F E (q ^ k * m) hqkm_pos := by
        simp_rw [hn_eq]
      calc F E n hn = F E (q ^ k * m) hqkm_pos := hF_eq
        _ = F E (q ^ k) hqk_pos + F E m hm_pos := hFn
        _ ≤ c * Real.log (q ^ k) + c * Real.log m := add_le_add hFqk_le ihm
        _ = c * (Real.log (q ^ k) + Real.log m) := by ring
        _ = c * Real.log (q ^ k * m) := by rw [Real.log_mul hqk_real_pos.ne' hm_real_pos.ne']
        _ = c * Real.log n := by
            have h : (q : ℝ) ^ k * (m : ℝ) = (n : ℝ) := by
              rw [← Nat.cast_pow, ← Nat.cast_mul, hn_eq']
            rw [h]

/-- **F_odd_lower_bound**: Symmetric to F_odd_upper_bound.
    If c ≤ c_prime E q hq for all odd primes q dividing n, then c * log(n) ≤ F(n).

    This is the key lemma for the symmetric argument in Step 4 of faddeev_c_prime_all_equal. -/
theorem F_odd_lower_bound (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (h_odd : Odd n)
    (c : ℝ) (h_dom : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ n → Odd q → c ≤ c_prime E q hq) :
    c * Real.log n ≤ F E n hn := by
  -- Proof by strong induction on n.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · -- Base case: n = 1
      subst h1
      have hF1 : F E 1 (by norm_num : 0 < 1) = 0 := faddeev_F1_eq_zero E
      have hlog1 : Real.log 1 = 0 := Real.log_one
      simp [hF1, hlog1]
    · -- Inductive case: n > 1
      have h_gt_1 : 1 < n := by omega
      set q := n.minFac with hq_def
      have hq_prime : q.Prime := Nat.minFac_prime (ne_of_gt h_gt_1)
      have hq_dvd : q ∣ n := n.minFac_dvd
      have hq_odd : Odd q := by
        by_contra hq_not_odd
        rw [Nat.not_odd_iff_even] at hq_not_odd
        have hq_two : q = 2 := (Nat.Prime.eq_one_or_self_of_dvd hq_prime 2
          hq_not_odd.two_dvd).resolve_left (by omega) |>.symm
        rw [hq_two] at hq_dvd
        exact h_odd.not_two_dvd_nat hq_dvd
      obtain ⟨k, m, hq_not_dvd, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq_prime.ne_one
      have hm_pos : 0 < m := by
        by_contra hm_not_pos; push_neg at hm_not_pos
        simp [Nat.le_zero.mp hm_not_pos] at hn_eq; omega
      have hm_odd : Odd m := by rw [hn_eq] at h_odd; exact (Nat.odd_mul.mp h_odd).2
      have hk_pos : 0 < k := by
        by_contra hk_zero; push_neg at hk_zero
        have hk_eq : k = 0 := Nat.le_zero.mp hk_zero
        simp [hk_eq] at hn_eq; rw [hn_eq] at hq_dvd; exact hq_not_dvd hq_dvd
      have hm_lt_n : m < n := by
        have hqk_ge_q : q ^ k ≥ q := Nat.le_self_pow (ne_of_gt hk_pos) q
        have hq_ge_3 : q ≥ 3 := by
          have hq_ne_2 : q ≠ 2 := fun h => hq_odd.not_two_dvd_nat (h ▸ dvd_refl q)
          have hq_ge_2 : q ≥ 2 := hq_prime.two_le
          omega
        have hqk_gt_1 : 1 < q ^ k := by
          calc 1 < q := hq_prime.one_lt
            _ ≤ q ^ k := Nat.le_self_pow (ne_of_gt hk_pos) q
        calc m = n / q ^ k := by rw [hn_eq]; simp [Nat.mul_div_cancel_left _ (by positivity : 0 < q ^ k)]
          _ < n := Nat.div_lt_self hn hqk_gt_1
      have h_dom_m : ∀ r : ℕ, ∀ hr : r.Prime, r ∣ m → Odd r → c ≤ c_prime E r hr := by
        intro r hr hr_dvd hr_odd
        have hr_dvd_n : r ∣ n := by rw [hn_eq]; exact Dvd.dvd.mul_left hr_dvd (q ^ k)
        exact h_dom r hr hr_dvd_n hr_odd
      have ihm := ih m hm_lt_n hm_pos hm_odd h_dom_m
      have hcq_ge : c ≤ c_prime E q hq_prime := h_dom q hq_prime hq_dvd hq_odd
      have hFq := F_prime_eq_c_times_log E hq_prime
      have hFq_ge : c * Real.log q ≤ F E q hq_prime.pos := by
        rw [hFq]
        have hlog_pos : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le : 1 ≤ (q : ℝ))
        exact mul_le_mul_of_nonneg_right hcq_ge hlog_pos
      have hFqk := faddeev_F_pow E hq_prime.pos k
      have hq_pos : 0 < q := hq_prime.pos
      have hqk_pos : 0 < q ^ k := pow_pos hq_pos k
      have hFqk_ge : c * Real.log (q ^ k) ≤ F E (q ^ k) hqk_pos := by
        have hFqk' : F E (q ^ k) hqk_pos = (k : ℝ) * F E q hq_prime.pos := by
          simp only [F] at hFqk ⊢; convert hFqk using 2
        rw [hFqk']
        have h1 : c * ((k : ℝ) * Real.log q) ≤ (k : ℝ) * F E q hq_prime.pos := by
          have : c * Real.log q ≤ F E q hq_prime.pos := hFq_ge
          calc c * ((k : ℝ) * Real.log q) = (k : ℝ) * (c * Real.log q) := by ring
            _ ≤ (k : ℝ) * F E q hq_prime.pos := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg k)
        calc c * Real.log (q ^ k) = c * ((k : ℝ) * Real.log q) := by rw [Real.log_pow]
          _ ≤ (k : ℝ) * F E q hq_prime.pos := h1
      have hFn := faddeev_F_mul E hqk_pos hm_pos
      have hn_eq' : q ^ k * m = n := hn_eq.symm
      have hqkm_pos : 0 < q ^ k * m := by positivity
      have hlog_pos_m : 0 ≤ Real.log m :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm_pos.ne' : (1 : ℝ) ≤ m)
      have hlog_pos_qk : 0 ≤ Real.log (q ^ k) := Real.log_nonneg (by
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq_prime.one_lt.le
        exact one_le_pow₀ hq1)
      have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      have hqk_real_pos : (0 : ℝ) < (q : ℝ) ^ k := by rw [← Nat.cast_pow]; exact Nat.cast_pos.mpr hqk_pos
      have hF_eq : F E n hn = F E (q ^ k * m) hqkm_pos := by simp_rw [hn_eq]
      calc c * Real.log n = c * Real.log (q ^ k * m) := by
              have h : (q : ℝ) ^ k * (m : ℝ) = (n : ℝ) := by rw [← Nat.cast_pow, ← Nat.cast_mul, hn_eq']
              rw [← h]
        _ = c * (Real.log (q ^ k) + Real.log m) := by rw [Real.log_mul hqk_real_pos.ne' hm_real_pos.ne']
        _ = c * Real.log (q ^ k) + c * Real.log m := by ring
        _ ≤ F E (q ^ k) hqk_pos + F E m hm_pos := add_le_add hFqk_ge ihm
        _ = F E (q ^ k * m) hqkm_pos := (hFn).symm
        _ = F E n hn := by rw [← hF_eq]

/-- For a prime p, λ_p = F(p) - F(p-1) relates to c_p via the factorization of p-1.
    Key identity: λ_p ≥ c_p · log(p/(p-1)) + (c_p - c_2) · log(2) when c_p ≥ c_q for all q | (p-1).

    The lower bound uses: 2 | (p-1) for odd primes p, so the sum includes q = 2.

    **Detailed Proof Sketch**:
    Write p - 1 = 2^a · m where m is odd and a ≥ 1 (since p is odd).
    Then F(p-1) = a + F(m) by `F_two_pow_mul`.

    Now, F(m) = Σ_{q | m, q odd prime} v_q(m) · F(q) by multiplicativity (since m is odd).

    The key rearrangement:
      λ_p = F(p) - F(p-1)
          = c_p · log(p) - a - F(m)
          = c_p · log(p) - a·c_2·log(2) - F(m)  (since F(2) = 1 = c_2·log(2))

    Wait, that's not right. Let me redo:
      F(2) = 1, and c_2 = F(2)/log(2) = 1/log(2).
      So a = a · 1 = a · F(2).

    The bound F(m) ≤ c_p · log(m) holds when c_p dominates all odd prime factors of m.
    For record-holder p, this is guaranteed since all q | m satisfy q | (p-1) and q < p.

    Therefore:
      λ_p = c_p·log(p) - a·F(2) - F(m)
          ≥ c_p·log(p) - a - c_p·log(m)  [using F(m) ≤ c_p·log(m)]
          = c_p·(log(p) - log(m)) - a
          = c_p·log(p/m) - a
          = c_p·log(2^a · (p/(p-1))) - a  [since p/m = p/(p-1 / 2^a) = 2^a·p/(p-1)]

    Hmm, this algebra is getting complicated. Let me use a different approach:

    λ_p = c_p·log(p) - a - Σ_{q | m} v_q(m)·c_q·log(q)
        = c_p·log(p) - a - Σ v_q(m)·c_p·log(q) + Σ v_q(m)·(c_p - c_q)·log(q)
        = c_p·(log(p) - log(m)) - a + Σ v_q(m)·(c_p - c_q)·log(q)
        = c_p·log(2^a · p/(p-1)) - a + Σ v_q(m)·(c_p - c_q)·log(q)

    Since 2^a · m = p - 1, we have p/(p-1) · 2^a = p/m, so:
      c_p·log(2^a) + c_p·log(p/(p-1)) - a + Σ(c_p - c_q)·log(q^{v_q})
    = a·c_p·log(2) + c_p·log(p/(p-1)) - a + Σ(c_p - c_q)·log(q^{v_q})
    = a·(c_p·log(2) - 1) + c_p·log(p/(p-1)) + Σ(c_p - c_q)·log(q^{v_q})
    = a·(c_p - c_2)·log(2) + c_p·log(p/(p-1)) + Σ(c_p - c_q)·log(q^{v_q})

    Since a ≥ 1, c_p ≥ c_2, log(p/(p-1)) > 0, and c_p ≥ c_q for all q | m:
      λ_p ≥ (c_p - c_2)·log(2)

    **Full formalization**: Requires expressing F(m) via prime factorization.
    For now, we state this as the key technical lemma. -/
theorem lambda_prime_lower_bound (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_dom : ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E q hq ≤ c_prime E p hp) :
    entropyIncrement E p hp.one_lt ≥ (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 := by
  -- λ_p = F(p) - F(p-1)
  unfold entropyIncrement
  have hp_pos : 0 < p := hp.pos
  have hp1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  -- F(p) = c_p · log(p)
  have hFp := F_prime_eq_c_times_log E hp
  -- For odd primes, 2 | (p-1)
  have h_even := prime_odd_pred_even hp hp2
  -- 2 divides p - 1
  have h2_dvd : 2 ∣ (p - 1) := Even.two_dvd h_even
  -- c_2 ≤ c_p by hypothesis (since 2 | (p-1))
  have hc2_le := h_dom 2 Nat.prime_two h2_dvd
  -- Write p - 1 = 2^a * m where m is odd and a ≥ 1 (since p is odd, p-1 is even)
  obtain ⟨a, m, h2_not_dvd, hp1_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hp1_pos.ne' 2 (by decide : (2 : ℕ) ≠ 1)
  have hm_pos : 0 < m := by
    by_contra hm_not_pos
    push_neg at hm_not_pos
    simp [Nat.le_zero.mp hm_not_pos] at hp1_eq
    omega
  -- m is odd since 2 ∤ m
  have hm_odd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2_not_dvd)
  -- a ≥ 1 since p - 1 is even (2 | p - 1)
  have ha_pos : 0 < a := by
    by_contra ha_zero
    push_neg at ha_zero
    have ha_eq : a = 0 := Nat.le_zero.mp ha_zero
    simp [ha_eq] at hp1_eq
    rw [hp1_eq] at h2_dvd
    exact h2_not_dvd h2_dvd
  -- F(p-1) = F(2^a * m) = a + F(m) by F_two_pow_mul
  have hFp1 := F_two_pow_mul E a hm_pos
  -- Convert to the form we need (matching proof terms)
  have h2am_pos : 0 < 2 ^ a * m := by positivity
  have hFp1' : F E (p - 1) hp1_pos = (a : ℝ) + F E m hm_pos := by
    have h_eq : p - 1 = 2 ^ a * m := hp1_eq
    -- F E (p - 1) hp1_pos = F E (2 ^ a * m) h2am_pos
    have h1 : F E (p - 1) hp1_pos = F E (2 ^ a * m) h2am_pos := by
      simp_rw [h_eq]
    rw [h1, hFp1]
  -- All odd prime divisors of m also divide p - 1, so they satisfy h_dom
  have h_dom_m : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m → Odd q → c_prime E q hq ≤ c_prime E p hp := by
    intro q hq hq_dvd hq_odd
    have hq_dvd_p1 : q ∣ (p - 1) := by
      rw [hp1_eq]
      exact Dvd.dvd.mul_left hq_dvd (2 ^ a)
    exact h_dom q hq hq_dvd_p1
  -- F(m) ≤ c_p · log(m) by F_odd_upper_bound
  have hFm_le := F_odd_upper_bound E hm_pos hm_odd (c_prime E p hp) h_dom_m
  -- Key algebraic manipulation:
  -- λ_p = F(p) - F(p-1)
  --     = c_p · log(p) - (a + F(m))
  --     ≥ c_p · log(p) - a - c_p · log(m)  [by hFm_le]
  --     = c_p · (log(p) - log(m)) - a
  --     = c_p · log(p/m) - a
  -- And: log(p/m) = log(p) + a · log(2) - log(p-1)
  have hp_real_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_pos
  have hp1_real_pos : (0 : ℝ) < p - 1 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  -- c_2 · log(2) = 1
  have hc2_log2 : c_prime E 2 Nat.prime_two * Real.log 2 = 1 := by
    have h := c_prime_two E
    rw [h]
    field_simp
  -- log(p/m) = log(p) + a · log(2) - log(p-1)
  have hlog_pm : Real.log (p / m) = Real.log p + a * Real.log 2 - Real.log (p - 1) := by
    have h_m_eq : (m : ℝ) = (p - 1 : ℝ) / (2 : ℝ) ^ a := by
      have h1 : (p - 1 : ℝ) = (2 : ℝ) ^ a * (m : ℝ) := by
        have hp1_eq' : (p - 1 : ℕ) = 2 ^ a * m := hp1_eq
        calc (p - 1 : ℝ) = ((p - 1 : ℕ) : ℝ) := by simp [Nat.cast_sub hp.one_lt.le]
          _ = ((2 ^ a * m : ℕ) : ℝ) := by rw [hp1_eq']
          _ = (2 : ℝ) ^ a * (m : ℝ) := by push_cast; ring
      field_simp at h1 ⊢
      linarith
    have h2a_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
    rw [h_m_eq, Real.log_div hp_real_pos.ne' (by positivity : ((p - 1 : ℝ) / (2 : ℝ) ^ a) ≠ 0)]
    rw [Real.log_div hp1_real_pos.ne' h2a_pos.ne', Real.log_pow]
    ring
  -- The main calculation
  set cp := c_prime E p hp with hcp_def
  set c2 := c_prime E 2 Nat.prime_two with hc2_def
  calc F E p hp_pos - F E (p - 1) hp1_pos
      = cp * Real.log p - ((a : ℝ) + F E m hm_pos) := by rw [hFp, hFp1', hcp_def]
    _ = cp * Real.log p - (a : ℝ) - F E m hm_pos := by ring
    _ ≥ cp * Real.log p - (a : ℝ) - cp * Real.log m := by linarith [hFm_le]
    _ = cp * (Real.log p - Real.log m) - (a : ℝ) := by ring
    _ = cp * Real.log (p / m) - (a : ℝ) := by
        rw [Real.log_div hp_real_pos.ne' hm_real_pos.ne']
    _ = cp * (Real.log p + (a : ℝ) * Real.log 2 - Real.log (p - 1)) - (a : ℝ) := by
        rw [hlog_pm]
    _ = cp * (Real.log p - Real.log (p - 1)) + (a : ℝ) * (cp * Real.log 2 - 1) := by ring
    _ = cp * (Real.log p - Real.log (p - 1)) + (a : ℝ) * (cp * Real.log 2 - c2 * Real.log 2) := by
        rw [← hc2_log2]
    _ = cp * (Real.log p - Real.log (p - 1)) + (a : ℝ) * (cp - c2) * Real.log 2 := by ring
    _ ≥ 0 + 1 * (cp - c2) * Real.log 2 := by
        apply add_le_add
        · apply mul_nonneg
          · -- cp ≥ c2 = 1/log(2) > 0
            have hc2_pos : 0 < c2 := by rw [hc2_def, c_prime_two E]; positivity
            linarith
          · rw [sub_nonneg]
            exact Real.log_le_log hp1_real_pos (by linarith : (p - 1 : ℝ) ≤ p)
        · apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right (Nat.one_le_cast.mpr ha_pos)
            rw [sub_nonneg]; exact hc2_le
          · exact le_of_lt log_two_pos
    _ = (cp - c2) * Real.log 2 := by ring
    _ = (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 := by rw [← hcp_def, ← hc2_def]

/-! ### Record-Holder Primes for Lemma 8

A "record-holder" prime is one where c_p strictly exceeds all c_q for smaller primes q.
Key property: for record-holders p ≠ 2, the domination hypothesis of `lambda_prime_lower_bound` holds.
If {c_p} has no maximum, there are infinitely many record-holders. -/

/-- A prime p is a "record-holder" if c_p > c_q for all primes q < p.
    For such primes, any prime divisor of p-1 satisfies the domination hypothesis. -/
def isRecordHolder (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, q < p → c_prime E q hq < c_prime E p hp

/-- 2 is always a record-holder (vacuously: no smaller primes). -/
theorem isRecordHolder_two (E : FaddeevEntropy) :
    isRecordHolder E 2 Nat.prime_two := by
  intro q hq hq_lt
  -- q < 2 and q is prime implies q < 2 ≤ q, contradiction
  exact absurd (hq.two_le) (not_le.mpr hq_lt)

/-- For a record-holder p ≠ 2, any prime q dividing p-1 satisfies c_q < c_p.
    This is the key property connecting record-holders to lambda_prime_lower_bound. -/
theorem recordHolder_dominates_divisors (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_rec : isRecordHolder E p hp) :
    ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E q hq ≤ c_prime E p hp := by
  intro q hq hq_dvd
  -- q divides p - 1, and p is prime with p ≠ 2, so p ≥ 3
  -- Thus p - 1 ≥ 2, and q | (p - 1) implies q ≤ p - 1 < p
  have hp_ge_3 : 3 ≤ p := by
    have h2le := hp.two_le
    omega
  have hp1_pos : 0 < p - 1 := by omega
  have hq_le_p1 : q ≤ p - 1 := Nat.le_of_dvd hp1_pos hq_dvd
  have hq_lt_p : q < p := by omega
  -- By record-holder property: c_q < c_p, hence c_q ≤ c_p
  exact le_of_lt (h_rec q hq hq_lt_p)

/-- If {c_p} has no maximum, then for any prime p, there exists a record-holder q > p.

    Proof sketch: Build sequence of record-holders r₁ = 2 < r₂ < r₃ < ... by well-ordering.
    Each rₙ is a record-holder (c_{rₙ} > c_q for all primes q < rₙ).
    Since {c_p} has no max, this sequence is infinite and unbounded.

    Key steps:
    1. For any record-holder r, if c_r were maximal, h_no_max would be violated.
       So there exists a prime q > r with c_q > c_r.
    2. Take r' = min{q : q > r, q.Prime, c_q > c_r}. This r' is a record-holder because:
       - For primes q < r: c_q < c_r (by r being a record-holder) < c_{r'}
       - For primes r ≤ q < r': c_q ≤ c_r (by minimality of r') < c_{r'}
    3. Starting from r₁ = 2 (a record-holder vacuously), iterate to build an infinite
       strictly increasing sequence of record-holders.
    4. Since rₙ₊₁ > rₙ for all n, we have rₙ → ∞, so eventually rₙ > p. -/
theorem exists_recordHolder_gt (E : FaddeevEntropy)
    (h_no_max : ∀ p : ℕ, ∀ hp : Nat.Prime p, ∃ q : ℕ, ∃ hq : Nat.Prime q, c_prime E p hp < c_prime E q hq)
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isRecordHolder E q hq := by
  -- Key helper: from any record-holder r, we can find a larger record-holder
  -- Strategy: use Nat.find to get the MINIMUM prime q > r with c_q > c_r
  -- That minimum is automatically a record-holder
  have next_recordHolder : ∀ r : ℕ, ∀ hr : Nat.Prime r, isRecordHolder E r hr →
      ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ isRecordHolder E r' hr' := by
    intro r hr h_rec
    -- By h_no_max, there exists q with c_q > c_r
    obtain ⟨q₀, hq₀_prime, hq₀_gt⟩ := h_no_max r hr
    -- First show q₀ > r (otherwise contradicts record-holder)
    have hq₀_gt_r : q₀ > r := by
      by_contra hq₀_le_r
      push_neg at hq₀_le_r
      have hq₀_lt_r_or_eq : q₀ < r ∨ q₀ = r := Nat.lt_or_eq_of_le hq₀_le_r
      cases hq₀_lt_r_or_eq with
      | inl hq₀_lt => exact absurd (h_rec q₀ hq₀_prime hq₀_lt) (not_lt.mpr (le_of_lt hq₀_gt))
      | inr hq₀_eq => subst hq₀_eq; exact lt_irrefl _ hq₀_gt
    -- Define predicate P(n) := n is prime ∧ n > r ∧ c_n > c_r
    -- Use Nat.find to get minimum such n
    let P := fun n => n.Prime ∧ r < n ∧ ∀ hn : n.Prime, c_prime E r hr < c_prime E n hn
    have hP_q₀ : P q₀ := ⟨hq₀_prime, hq₀_gt_r, fun _ => hq₀_gt⟩
    -- P is decidable (requires decidability of c_prime comparison - we'll use Classical)
    have hP_exists : ∃ n, P n := ⟨q₀, hP_q₀⟩
    -- Use Classical.choose to get a witness, then well-order argument
    -- For minimum, we'll use a different approach: among primes in [r+1, q₀], find one with max c
    -- Actually simpler: use strong induction on q₀ - r
    -- If q₀ is a record-holder, we're done
    -- If not, there's some prime q' < q₀ with c_q' ≥ c_q₀, but then c_q' > c_r,
    -- and we can recurse with q' instead of q₀
    -- Since q' < q₀, this terminates
    -- Use well-founded recursion on q₀ to find a record-holder in (r, q₀]
    -- If q₀ is a record-holder, we're done
    -- If not, there's some prime q' < q₀ with c_q' ≥ c_q₀ > c_r, and we recurse
    suffices h : ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ r' ≤ q₀ ∧ isRecordHolder E r' hr' by
      obtain ⟨r', hr', hr'_gt_r, _, hr'_rec⟩ := h
      exact ⟨r', hr', hr'_gt_r, hr'_rec⟩
    -- Use well-founded recursion on q₀
    exact Nat.lt_wfRel.wf.fix
      (C := fun q => ∀ (hq : q.Prime), c_prime E r hr < c_prime E q hq → r < q →
          ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ r' ≤ q ∧ isRecordHolder E r' hr')
      (fun q ih hq_prime hq_gt hq_gt_r => by
        by_cases hq_rec : isRecordHolder E q hq_prime
        · -- q is a record-holder, done
          exact ⟨q, hq_prime, hq_gt_r, le_refl q, hq_rec⟩
        · -- q is not a record-holder: ∃ prime q' < q with c_q' ≥ c_q
          unfold isRecordHolder at hq_rec
          push_neg at hq_rec
          obtain ⟨q', hq'_prime, hq'_lt_q, hq'_ge⟩ := hq_rec
          -- c_q' ≥ c_q > c_r, so c_q' > c_r
          have hq'_gt_cr : c_prime E r hr < c_prime E q' hq'_prime := lt_of_lt_of_le hq_gt hq'_ge
          -- q' > r (otherwise contradicts r being record-holder)
          have hq'_gt_r : r < q' := by
            by_contra hq'_le_r
            push_neg at hq'_le_r
            have hq'_lt_r_or_eq : q' < r ∨ q' = r := Nat.lt_or_eq_of_le hq'_le_r
            cases hq'_lt_r_or_eq with
            | inl hq'_lt => exact absurd (h_rec q' hq'_prime hq'_lt) (not_lt.mpr (le_of_lt hq'_gt_cr))
            | inr hq'_eq => subst hq'_eq; exact lt_irrefl _ hq'_gt_cr
          -- Recurse with q' < q
          obtain ⟨r', hr', hr'_gt_r, hr'_le_q', hr'_rec⟩ := ih q' hq'_lt_q hq'_prime hq'_gt_cr hq'_gt_r
          exact ⟨r', hr', hr'_gt_r, le_trans hr'_le_q' (le_of_lt hq'_lt_q), hr'_rec⟩)
      q₀ hq₀_prime hq₀_gt hq₀_gt_r
  -- Now iterate: starting from 2, apply next_recordHolder until we exceed p
  -- Use well-founded recursion on (p - current_prime)
  have h2_rec := isRecordHolder_two E
  -- Main iteration: find a record-holder > p
  -- Use strong induction: if we have record-holder r ≤ p, we can find r' > r
  -- Eventually r' > p since r' > r always
  suffices h : ∀ r : ℕ, ∀ hr : Nat.Prime r, r ≤ p → isRecordHolder E r hr →
      ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isRecordHolder E q hq by
    exact h 2 Nat.prime_two hp.two_le h2_rec
  intro r hr hr_le_p hr_rec
  -- Get next record-holder r' > r
  obtain ⟨r', hr', hr'_gt_r, hr'_rec⟩ := next_recordHolder r hr hr_rec
  by_cases hr'_gt_p : r' > p
  · exact ⟨r', hr', hr'_gt_p, hr'_rec⟩
  · -- r' ≤ p, but r' > r, so we made progress
    push_neg at hr'_gt_p
    -- Use strong induction on (p - r)
    have hp_sub_r_pos : p - r > 0 := Nat.sub_pos_of_lt (lt_of_lt_of_le hr'_gt_r hr'_gt_p)
    -- Actually we need to track that p - r' < p - r
    have hr'_closer : p - r' < p - r := by omega
    -- This is where we need termination. Use well-founded recursion on p - r
    -- For now, we observe that we can iterate at most p times
    -- Each iteration increases r by at least 1
    -- So after at most p iterations, we have r > p
    -- Formalize this with Nat.lt_wfRel
    exact Nat.lt_wfRel.wf.fix (C := fun d => ∀ r : ℕ, ∀ hr : Nat.Prime r,
        r ≤ p → p - r = d → isRecordHolder E r hr →
        ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isRecordHolder E q hq)
      (fun d ih r hr hr_le_p hd hr_rec => by
        obtain ⟨r', hr', hr'_gt_r, hr'_rec⟩ := next_recordHolder r hr hr_rec
        by_cases hr'_gt_p : r' > p
        · exact ⟨r', hr', hr'_gt_p, hr'_rec⟩
        · push_neg at hr'_gt_p
          have hd' : p - r' < d := by omega
          exact ih (p - r') hd' r' hr' hr'_gt_p rfl hr'_rec)
      (p - r) r hr hr_le_p rfl hr_rec


/-- **Faddeev's Lemma 8**: The set {c_p | p prime} has a maximum.

    Proof by contradiction:
    1. If no max exists, build sequence p₁ < p₂ < ... where c_{p_i} > c_q for all primes q < p_i
    2. For each p_i > 2: λ_{p_i} ≥ (c_{p_i} - c_2) · log(2) ≥ δ · log(2) > 0 (uniform bound)
    3. But λ_n → 0 (faddeev_lambda_tendsto_zero), contradiction!

    This proves {c_p} has a maximum WITHOUT using monotonicity of F! -/
theorem faddeev_c_prime_has_max (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E q hq ≤ c_prime E p hp := by
  -- Proof by contradiction using λ_n → 0
  by_contra h_no_max
  push_neg at h_no_max
  -- h_no_max: For each prime p, there exists prime q with c_q > c_p

  -- Key fact: λ_n → 0 as n → ∞
  have hlim := faddeev_lambda_tendsto_zero E

  -- Step 1: Get a prime p₁ with c_{p₁} > c_2
  obtain ⟨p₁, hp₁, hc₁⟩ := h_no_max 2 Nat.prime_two

  -- The uniform positive lower bound: δ = (c_{p₁} - c_2) · log(2) > 0
  set δ := (c_prime E p₁ hp₁ - c_prime E 2 Nat.prime_two) * Real.log 2 with hδ_def
  have hδ_pos : 0 < δ := by
    apply mul_pos
    · exact sub_pos.mpr hc₁
    · exact log_two_pos

  -- Step 2: By Tendsto definition, for ε = δ > 0, there exists N such that
  -- for all n ≥ N, |λ_{n+2}| < δ.
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim δ hδ_pos

  -- Step 3: Find a record-holder p₂ with p₂ > max(N + 2, p₁)
  -- Use exists_recordHolder_gt twice: once to get past p₁, once to get past N+2
  have hN2_pos : 0 < N + 2 := Nat.add_pos_right N (by omega)
  -- First, we need a prime > N + 2. Use p₁ if p₁ > N + 2, otherwise find a larger prime.
  -- Get a record-holder > max(p₁, N + 2)
  set M := max p₁ (N + 2) with hM_def
  -- Need a prime larger than M
  have hM_lt_prime := Nat.exists_infinite_primes (M + 1)
  obtain ⟨p_big, hp_big_ge, hp_big_prime⟩ := hM_lt_prime
  have hp_big_gt_N2 : p_big > N + 2 := by omega
  have hp_big_gt_p1 : p_big > p₁ := by omega
  -- Find a record-holder > p_big (which is > M > max(p₁, N+2))
  obtain ⟨p₂, hp₂, hp₂_gt_pbig, hp₂_rec⟩ := exists_recordHolder_gt E h_no_max p_big hp_big_prime
  have hp₂_gt_N2 : p₂ > N + 2 := by omega
  have hp₂_gt_p1 : p₂ > p₁ := by omega
  -- p₂ is a record-holder, so c_{p₂} > c_q for all primes q < p₂
  -- In particular, c_{p₂} > c_{p₁} > c_2
  have hc₂_gt_c1 : c_prime E p₁ hp₁ < c_prime E p₂ hp₂ := hp₂_rec p₁ hp₁ hp₂_gt_p1
  have hc₂_gt_c2 : c_prime E 2 Nat.prime_two < c_prime E p₂ hp₂ :=
    lt_trans hc₁ hc₂_gt_c1
  -- p₂ ≠ 2 since p₂ > p₁ ≥ 2 (p₁ is a prime > 2)
  have hp₂_ne_2 : p₂ ≠ 2 := by omega
  -- Step 4: Apply lambda_prime_lower_bound to p₂
  -- Need: p₂ is odd prime, and dominates all prime divisors of p₂ - 1
  have hp₂_dom := recordHolder_dominates_divisors E hp₂ hp₂_ne_2 hp₂_rec
  have hlambda_lower := lambda_prime_lower_bound E hp₂ hp₂_ne_2 hp₂_dom
  -- λ_{p₂} ≥ (c_{p₂} - c_2) · log(2) > (c_{p₁} - c_2) · log(2) = δ
  have hlambda_gt_delta : entropyIncrement E p₂ hp₂.one_lt > δ := by
    calc entropyIncrement E p₂ hp₂.one_lt
        ≥ (c_prime E p₂ hp₂ - c_prime E 2 Nat.prime_two) * Real.log 2 := hlambda_lower
      _ > (c_prime E p₁ hp₁ - c_prime E 2 Nat.prime_two) * Real.log 2 := by
          apply mul_lt_mul_of_pos_right _ log_two_pos
          exact sub_lt_sub_right hc₂_gt_c1 _
      _ = δ := by rfl
  -- Step 5: But |λ_{p₂}| < δ by hN
  have hp₂_sub_ge_N : p₂ - 2 ≥ N := by omega
  have hspec := hN (p₂ - 2) hp₂_sub_ge_N
  have hp₂_add : (p₂ - 2) + 2 = p₂ := by omega
  simp only [hp₂_add] at hspec
  -- hspec : dist (entropyIncrement E p₂ hp₂.one_lt) 0 < δ
  rw [Real.dist_eq, sub_zero] at hspec
  -- |λ_{p₂}| < δ, but λ_{p₂} > δ > 0, so λ_{p₂} ≥ δ, contradiction
  have habs : |entropyIncrement E p₂ hp₂.one_lt| = entropyIncrement E p₂ hp₂.one_lt := by
    apply abs_of_pos
    exact lt_of_lt_of_le hδ_pos (le_of_lt hlambda_gt_delta)
  rw [habs] at hspec
  exact absurd hlambda_gt_delta (not_lt.mpr (le_of_lt hspec))

/-! ### Symmetric Infrastructure for Minimum (Step 4) -/

/-- A prime p is a "downward record-holder" if c_p < c_q for all primes q < p.
    This is symmetric to isRecordHolder (which uses > instead of <). -/
def isDownwardRecordHolder (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, q < p → c_prime E q hq > c_prime E p hp

/-- For a downward record-holder p ≠ 2, any prime q dividing p-1 satisfies c_p ≤ c_q.
    Symmetric to recordHolder_dominates_divisors. -/
theorem downwardRecordHolder_dominated_by_divisors (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_rec : isDownwardRecordHolder E p hp) :
    ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E p hp ≤ c_prime E q hq := by
  intro q hq hq_dvd
  have hp_ge_3 : 3 ≤ p := by have h2le := hp.two_le; omega
  have hp1_pos : 0 < p - 1 := by omega
  have hq_le_p1 : q ≤ p - 1 := Nat.le_of_dvd hp1_pos hq_dvd
  have hq_lt_p : q < p := by omega
  exact le_of_lt (h_rec q hq hq_lt_p)

/-- If {c_p} has no minimum, then for any prime p, there exists a downward record-holder q > p.
    Symmetric to exists_recordHolder_gt. -/
theorem exists_downwardRecordHolder_gt (E : FaddeevEntropy)
    (h_no_min : ∀ p : ℕ, ∀ hp : Nat.Prime p, ∃ q : ℕ, ∃ hq : Nat.Prime q, c_prime E q hq < c_prime E p hp)
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isDownwardRecordHolder E q hq := by
  -- Key helper: from any downward record-holder r, we can find a larger downward record-holder
  have next_downwardRecordHolder : ∀ r : ℕ, ∀ hr : Nat.Prime r, isDownwardRecordHolder E r hr →
      ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ isDownwardRecordHolder E r' hr' := by
    intro r hr h_rec
    -- By h_no_min, there exists q with c_q < c_r
    obtain ⟨q₀, hq₀_prime, hq₀_c_lt⟩ := h_no_min r hr
    -- First show q₀ > r (otherwise contradicts downward record-holder)
    have hq₀_gt_r : q₀ > r := by
      by_contra hq₀_le_r
      push_neg at hq₀_le_r
      have hq₀_lt_r_or_eq : q₀ < r ∨ q₀ = r := Nat.lt_or_eq_of_le hq₀_le_r
      cases hq₀_lt_r_or_eq with
      | inl hq₀_lt_nat =>
        -- h_rec gives: q₀ < r → c_{q₀} > c_r
        -- But hq₀_c_lt says: c_{q₀} < c_r. Contradiction.
        exact absurd hq₀_c_lt (not_lt.mpr (le_of_lt (h_rec q₀ hq₀_prime hq₀_lt_nat)))
      | inr hq₀_eq => subst hq₀_eq; exact lt_irrefl _ hq₀_c_lt
    -- Use well-founded recursion to find a downward record-holder in (r, q₀]
    suffices h : ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ r' ≤ q₀ ∧ isDownwardRecordHolder E r' hr' by
      obtain ⟨r', hr', hr'_gt_r, _, hr'_rec⟩ := h
      exact ⟨r', hr', hr'_gt_r, hr'_rec⟩
    exact Nat.lt_wfRel.wf.fix
      (C := fun q => ∀ (hq : q.Prime), c_prime E q hq < c_prime E r hr → r < q →
          ∃ r' : ℕ, ∃ hr' : Nat.Prime r', r < r' ∧ r' ≤ q ∧ isDownwardRecordHolder E r' hr')
      (fun q ih hq_prime hq_lt hq_gt_r => by
        by_cases hq_rec : isDownwardRecordHolder E q hq_prime
        · exact ⟨q, hq_prime, hq_gt_r, le_refl q, hq_rec⟩
        · -- q is not a downward record-holder, so there exists s < q with c_s ≤ c_q
          unfold isDownwardRecordHolder at hq_rec
          push_neg at hq_rec
          obtain ⟨s, hs, hs_lt_q, hs_le⟩ := hq_rec
          -- s < q and c_s ≤ c_q < c_r
          have hs_lt_r : c_prime E s hs < c_prime E r hr := lt_of_le_of_lt hs_le hq_lt
          by_cases hs_gt_r : r < s
          · -- r < s < q, recurse with s
            have hs_lt_q' : s < q := hs_lt_q
            obtain ⟨r', hr', hr'_gt_r, hr'_le_s, hr'_rec⟩ := ih s hs_lt_q' hs hs_lt_r hs_gt_r
            exact ⟨r', hr', hr'_gt_r, le_trans hr'_le_s (le_of_lt hs_lt_q), hr'_rec⟩
          · -- s ≤ r, but we have c_s ≤ c_q < c_r
            -- If s = r, then c_r ≤ c_q < c_r, contradiction
            -- If s < r, then by downward record-holder of r: c_r < c_s, but c_s < c_r, contradiction
            push_neg at hs_gt_r
            have hs_lt_r_or_eq : s < r ∨ s = r := Nat.lt_or_eq_of_le hs_gt_r
            cases hs_lt_r_or_eq with
            | inl hs_lt =>
              have hcontra := h_rec s hs hs_lt  -- c_s > c_r
              linarith
            | inr hs_eq =>
              subst hs_eq
              linarith)
      q₀ hq₀_prime hq₀_c_lt hq₀_gt_r
  -- Now build the downward record-holder > p
  -- 2 is vacuously a downward record-holder (no primes < 2)
  have h2_rec : isDownwardRecordHolder E 2 Nat.prime_two := by
    intro q hq hq_lt
    exact absurd hq.two_le (not_le.mpr hq_lt)
  -- Start from 2 and iterate until we exceed p
  by_cases hp_eq_2 : p = 2
  · -- p = 2, find a downward record-holder > 2
    obtain ⟨r, hr, hr_gt_2, hr_rec⟩ := next_downwardRecordHolder 2 Nat.prime_two h2_rec
    exact ⟨r, hr, by omega, hr_rec⟩
  · -- p > 2
    -- Iterate next_downwardRecordHolder starting from 2
    -- Use well-founded recursion on p to find a downward record-holder > p
    have hp_gt_2 : p > 2 := by
      have h := hp.two_le
      omega
    -- Strategy: find any downward record-holder r, then iterate until r > p
    -- We have h2_rec, and can iterate to get arbitrarily large downward record-holders
    -- Use Nat.strong_induction to build a chain of downward record-holders
    suffices ∃ r : ℕ, ∃ hr : Nat.Prime r, p < r ∧ isDownwardRecordHolder E r hr by exact this
    -- Build sequence: start from 2, apply next_downwardRecordHolder repeatedly
    -- Since downward record-holders are strictly increasing, eventually exceed p
    have h_chain : ∀ n : ℕ, ∃ r : ℕ, ∃ hr : Nat.Prime r, n ≤ r ∧ isDownwardRecordHolder E r hr := by
      intro n
      induction n with
      | zero => exact ⟨2, Nat.prime_two, Nat.zero_le 2, h2_rec⟩
      | succ n ih =>
        obtain ⟨r, hr, hr_ge_n, hr_rec⟩ := ih
        by_cases h : n + 1 ≤ r
        · exact ⟨r, hr, h, hr_rec⟩
        · -- r < n + 1, so r ≤ n, and combined with n ≤ r, we have r = n
          push_neg at h
          -- Get a larger downward record-holder
          obtain ⟨r', hr', hr'_gt_r, hr'_rec⟩ := next_downwardRecordHolder r hr hr_rec
          -- r' > r ≥ n, so r' ≥ n + 1
          exact ⟨r', hr', by omega, hr'_rec⟩
    obtain ⟨r, hr, hr_ge, hr_rec⟩ := h_chain (p + 1)
    exact ⟨r, hr, by omega, hr_rec⟩

/-- **lambda_prime_upper_bound**: Symmetric to lambda_prime_lower_bound.
    For a downward record-holder p ≠ 2 (where c_p ≤ c_q for all primes q | (p-1)),
    we have λ_p ≤ (c_p - c_2) * log(2) + positive correction.

    Since c_p < c_2 implies (c_p - c_2) < 0, this gives an upper bound on λ_p
    that goes to -∞ as c_p → -∞. -/
theorem lambda_prime_upper_bound (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_dom : ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E p hp ≤ c_prime E q hq) :
    entropyIncrement E p hp.one_lt ≤ (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 +
        c_prime E p hp * Real.log (p / (p - 1)) := by
  unfold entropyIncrement
  have hp_pos : 0 < p := hp.pos
  have hp1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hp_ge_3 : 3 ≤ p := by have h2le := hp.two_le; omega
  have hFp := F_prime_eq_c_times_log E hp
  have h_even := prime_odd_pred_even hp hp2
  have h2_dvd : 2 ∣ (p - 1) := Even.two_dvd h_even
  have hc2_le := h_dom 2 Nat.prime_two h2_dvd
  obtain ⟨a, m, h2_not_dvd, hp1_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hp1_pos.ne' 2 (by decide)
  have hm_pos : 0 < m := by
    by_contra hm_not_pos; push_neg at hm_not_pos
    simp [Nat.le_zero.mp hm_not_pos] at hp1_eq; omega
  have hm_odd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2_not_dvd)
  have ha_pos : 0 < a := by
    by_contra ha_zero; push_neg at ha_zero
    have ha_eq : a = 0 := Nat.le_zero.mp ha_zero
    simp [ha_eq] at hp1_eq; rw [hp1_eq] at h2_dvd; exact h2_not_dvd h2_dvd
  have hFp1 := F_two_pow_mul E a hm_pos
  have h2am_pos : 0 < 2 ^ a * m := by positivity
  have hFp1' : F E (p - 1) hp1_pos = (a : ℝ) + F E m hm_pos := by
    have h_eq : p - 1 = 2 ^ a * m := hp1_eq
    have h1 : F E (p - 1) hp1_pos = F E (2 ^ a * m) h2am_pos := by simp_rw [h_eq]
    rw [h1, hFp1]
  -- All odd prime divisors of m also divide p - 1
  have h_dom_m : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m → Odd q → c_prime E p hp ≤ c_prime E q hq := by
    intro q hq hq_dvd _
    have hq_dvd_p1 : q ∣ (p - 1) := by rw [hp1_eq]; exact Dvd.dvd.mul_left hq_dvd (2 ^ a)
    exact h_dom q hq hq_dvd_p1
  -- F(m) ≥ c_p · log(m) by F_odd_lower_bound (since c_p ≤ c_q for odd q | m)
  have hFm_ge := F_odd_lower_bound E hm_pos hm_odd (c_prime E p hp) h_dom_m
  -- Key algebraic manipulation (symmetric to lambda_prime_lower_bound)
  have hp_real_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_pos
  have hp1_real_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have h : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
    linarith
  have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  have hc2_log2 : c_prime E 2 Nat.prime_two * Real.log 2 = 1 := by rw [c_prime_two E]; field_simp
  have hp1_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hlog_pm : Real.log ((p : ℝ) / m) = Real.log p + a * Real.log 2 - Real.log ((p : ℝ) - 1) := by
    have h_m_eq : (m : ℝ) = ((p : ℝ) - 1) / (2 : ℝ) ^ a := by
      have h1 : ((p : ℝ) - 1) = (2 : ℝ) ^ a * (m : ℝ) := by
        have hp1_eq' : (p - 1 : ℕ) = 2 ^ a * m := hp1_eq
        calc ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := hp1_cast.symm
          _ = ((2 ^ a * m : ℕ) : ℝ) := by rw [hp1_eq']
          _ = (2 : ℝ) ^ a * (m : ℝ) := by push_cast; ring
      field_simp at h1 ⊢; linarith
    have h2a_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
    rw [h_m_eq, Real.log_div hp_real_pos.ne' (by positivity)]
    rw [Real.log_div hp1_real_pos.ne' h2a_pos.ne', Real.log_pow]; ring
  -- Compute λ_p = F(p) - F(p-1) = c_p · log(p) - (a + F(m))
  --            ≤ c_p · log(p) - a - c_p · log(m)  [since F(m) ≥ c_p · log(m)]
  --            = c_p · log(p/m) - a
  have h_ratio : Real.log ((p : ℝ) / ((p : ℝ) - 1)) = Real.log p - Real.log ((p : ℝ) - 1) := by
    rw [Real.log_div hp_real_pos.ne' hp1_real_pos.ne']
  have hpm_eq : Real.log ((p : ℝ) / m) = a * Real.log 2 + Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [hlog_pm, h_ratio]; ring
  calc F E p hp.pos - F E (p - 1) hp1_pos
      = c_prime E p hp * Real.log p - (a + F E m hm_pos) := by rw [hFp, hFp1']
    _ ≤ c_prime E p hp * Real.log p - (a + c_prime E p hp * Real.log m) := by linarith [hFm_ge]
    _ = c_prime E p hp * (Real.log p - Real.log m) - a := by ring
    _ = c_prime E p hp * Real.log ((p : ℝ) / m) - a := by
        rw [Real.log_div hp_real_pos.ne' hm_real_pos.ne']
    _ = c_prime E p hp * (a * Real.log 2 + Real.log ((p : ℝ) / ((p : ℝ) - 1))) - a := by rw [hpm_eq]
    _ = a * (c_prime E p hp * Real.log 2 - 1) + c_prime E p hp * Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by ring
    _ = a * (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 +
        c_prime E p hp * Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
        rw [← hc2_log2]; ring
    _ ≤ 1 * (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 +
        c_prime E p hp * Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
        have ha_ge_1 : (1 : ℝ) ≤ a := by exact_mod_cast ha_pos
        have h_neg : c_prime E p hp - c_prime E 2 Nat.prime_two ≤ 0 := by linarith [hc2_le]
        have h1 : a * (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 ≤
            1 * (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 := by
          have hlog2_pos : 0 < Real.log 2 := log_two_pos
          have h2 : (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 ≤ 0 := by nlinarith
          nlinarith
        linarith
    _ = (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 +
        c_prime E p hp * Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by ring

/-- **Lemma 8'**: The set {c_p | p prime} has a minimum.

    This is proven independently of Lemma 9 (all c_p equal), using the λ → 0 argument.

    Proof by contradiction:
    1. If no min exists, build sequence p₁ > p₂ > ... where c_{p_i} < c_q for all primes q < p_i
    2. For each p_i > 2 (downward record-holder): λ_{p_i} ≤ (c_{p_i} - c_2)·log(2) + correction
       Since c_{p_i} → -∞, this upper bound → -∞.
    3. But λ_n → 0, so |λ_n| < ε for large n. Contradiction! -/
theorem faddeev_c_prime_has_min_aux (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E p hp ≤ c_prime E q hq := by
  -- Proof by contradiction using λ_n → 0
  by_contra h_no_min
  push_neg at h_no_min
  -- h_no_min: For each prime p, there exists prime q with c_q < c_p

  -- Key fact: λ_n → 0 as n → ∞
  have hlim := faddeev_lambda_tendsto_zero E

  -- Step 1: Get a prime p₁ with c_{p₁} < c_2
  obtain ⟨p₁, hp₁, hc₁⟩ := h_no_min 2 Nat.prime_two

  -- The uniform negative margin: δ = (c_2 - c_{p₁}) · log(2) > 0
  set δ := (c_prime E 2 Nat.prime_two - c_prime E p₁ hp₁) * Real.log 2 with hδ_def
  have hδ_pos : 0 < δ := by
    apply mul_pos
    · exact sub_pos.mpr hc₁
    · exact log_two_pos

  -- We need to handle the correction term c_{p₂} · log(p₂/(p₂-1)).
  -- Key insight: c_{p₂} is bounded above by c_2 (since c_{p₂} < c_{p₁} < c_2).
  -- So the correction is bounded by c_2 · log(p/(p-1)), which → 0 as p → ∞.

  -- Get bound on c_2
  have hc2_bound : c_prime E 2 Nat.prime_two = 1 / Real.log 2 := c_prime_two E

  -- For the correction term to be small enough, we need p large enough.
  -- Specifically: c_2 · log(p/(p-1)) < δ/4
  -- Since log(p/(p-1)) ~ 1/(p-1), we need p > some threshold.

  -- Step 2: By Tendsto definition, for ε = δ/4 > 0, there exists N such that
  -- for all n ≥ N, |λ_{n+2}| < δ/4.
  rw [Metric.tendsto_atTop] at hlim
  have hδ4_pos : 0 < δ / 4 := by linarith
  obtain ⟨N, hN⟩ := hlim (δ / 4) hδ4_pos

  -- Step 3: Find threshold P such that for p > P, the correction is small
  -- We need: c_2 · log(p/(p-1)) < δ/4, i.e., log(p/(p-1)) < (δ/4) · log(2)
  -- Since log(1 + 1/(p-1)) ≤ 2/(p-1) for p ≥ 2, we need 2/(p-1) < (δ/4) · log(2)
  -- i.e., p > 8/(δ · log(2)) + 1

  -- Use Archimedean property to find P such that for p > P, correction is small
  have harch := exists_nat_gt (8 / (δ * Real.log 2) + 1)
  obtain ⟨P, hP⟩ := harch

  -- Step 4: Find a downward record-holder p₂ with p₂ > max(N + 2, p₁, P)
  set M := max (max p₁ (N + 2)) P with hM_def
  have hM_lt_prime := Nat.exists_infinite_primes (M + 1)
  obtain ⟨p_big, hp_big_ge, hp_big_prime⟩ := hM_lt_prime
  have hp_big_gt_N2 : p_big > N + 2 := by omega
  have hp_big_gt_p1 : p_big > p₁ := by omega
  have hp_big_gt_P : p_big > P := by omega

  -- Find a downward record-holder > p_big
  obtain ⟨p₂, hp₂, hp₂_gt_pbig, hp₂_rec⟩ := exists_downwardRecordHolder_gt E h_no_min p_big hp_big_prime
  have hp₂_gt_N2 : p₂ > N + 2 := by omega
  have hp₂_gt_p1 : p₂ > p₁ := by omega
  have hp₂_gt_P : p₂ > P := by omega

  -- p₂ is a downward record-holder, so c_{p₂} < c_q for all primes q < p₂
  -- In particular, c_{p₂} < c_{p₁} < c_2
  have hc₂_lt_c1 : c_prime E p₂ hp₂ < c_prime E p₁ hp₁ := hp₂_rec p₁ hp₁ hp₂_gt_p1
  have hc₂_lt_c2 : c_prime E p₂ hp₂ < c_prime E 2 Nat.prime_two :=
    lt_trans hc₂_lt_c1 hc₁

  have hp₂_ne_2 : p₂ ≠ 2 := by omega

  -- Step 5: Apply lambda_prime_upper_bound to p₂
  have hp₂_dom := downwardRecordHolder_dominated_by_divisors E hp₂ hp₂_ne_2 hp₂_rec
  have hlambda_upper := lambda_prime_upper_bound E hp₂ hp₂_ne_2 hp₂_dom

  -- Main term: (c_{p₂} - c_2) · log(2) < (c_{p₁} - c_2) · log(2) = -δ
  have hmain_neg : (c_prime E p₂ hp₂ - c_prime E 2 Nat.prime_two) * Real.log 2 <
      (c_prime E p₁ hp₁ - c_prime E 2 Nat.prime_two) * Real.log 2 := by
    apply mul_lt_mul_of_pos_right _ log_two_pos
    exact sub_lt_sub_right hc₂_lt_c1 _

  have hmain_lt_neg_delta : (c_prime E p₂ hp₂ - c_prime E 2 Nat.prime_two) * Real.log 2 < -δ := by
    calc (c_prime E p₂ hp₂ - c_prime E 2 Nat.prime_two) * Real.log 2
        < (c_prime E p₁ hp₁ - c_prime E 2 Nat.prime_two) * Real.log 2 := hmain_neg
      _ = -(c_prime E 2 Nat.prime_two - c_prime E p₁ hp₁) * Real.log 2 := by ring
      _ = -((c_prime E 2 Nat.prime_two - c_prime E p₁ hp₁) * Real.log 2) := by ring
      _ = -δ := by rfl

  -- Correction term analysis:
  -- Case A: c_{p₂} ≤ 0, then correction ≤ 0
  -- Case B: c_{p₂} > 0, then correction < c_2 · log(p₂/(p₂-1)) < δ/4

  have hp₂_nat_pos : 0 < p₂ := hp₂.pos
  have hp₂_pos : (0 : ℝ) < p₂ := Nat.cast_pos.mpr hp₂_nat_pos
  have hp₂_ge_3 : 3 ≤ p₂ := by have h2le := hp₂.two_le; omega
  have hp₂m1_pos : (0 : ℝ) < (p₂ : ℝ) - 1 := by
    have : (1 : ℝ) < p₂ := Nat.one_lt_cast.mpr hp₂.one_lt
    linarith

  have hlog_ratio_pos : Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) > 0 := by
    apply Real.log_pos
    rw [one_lt_div hp₂m1_pos]
    linarith

  -- Bound on the correction term
  have hcorr_bound : c_prime E p₂ hp₂ * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) < δ / 4 := by
    by_cases hcp₂_sign : c_prime E p₂ hp₂ ≤ 0
    · -- Case A: c_{p₂} ≤ 0
      have hcorr_nonpos : c_prime E p₂ hp₂ * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg hcp₂_sign (le_of_lt hlog_ratio_pos)
      linarith
    · -- Case B: c_{p₂} > 0
      push_neg at hcp₂_sign
      -- c_{p₂} < c_2, so correction < c_2 · log(p₂/(p₂-1))
      have hcorr_lt : c_prime E p₂ hp₂ * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) <
          c_prime E 2 Nat.prime_two * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) := by
        apply mul_lt_mul_of_pos_right hc₂_lt_c2 hlog_ratio_pos
      -- Now bound c_2 · log(p₂/(p₂-1)) < δ/4
      -- c_2 = 1/log(2), so we need log(p₂/(p₂-1)) < (δ/4) · log(2)
      -- Using log(1 + x) ≤ 2x for x ∈ (0, 1], we have log(p/(p-1)) = log(1 + 1/(p-1)) ≤ 2/(p-1)
      -- We need 2/(p₂-1) < (δ/4) · log(2), i.e., p₂ > 8/(δ·log(2)) + 1

      -- Use the bound from P
      have hp₂_bound : (p₂ : ℝ) > 8 / (δ * Real.log 2) + 1 := by
        have : (P : ℝ) > 8 / (δ * Real.log 2) + 1 - 1 := by
          have hP' := hP
          have : (P : ℝ) > 8 / (δ * Real.log 2) + 1 := by exact_mod_cast hP
          linarith
        have hp₂_gt_P' : (p₂ : ℝ) > P := by exact_mod_cast hp₂_gt_P
        have hP'' : (P : ℝ) > 8 / (δ * Real.log 2) + 1 := by exact_mod_cast hP
        linarith

      -- p₂ - 1 > 8/(δ · log(2))
      have hp₂m1_bound : (p₂ : ℝ) - 1 > 8 / (δ * Real.log 2) := by linarith

      -- 1/(p₂ - 1) < (δ · log(2))/8
      have hinv_bound : 1 / ((p₂ : ℝ) - 1) < δ * Real.log 2 / 8 := by
        have hpos : δ * Real.log 2 > 0 := mul_pos hδ_pos log_two_pos
        -- From hp₂m1_bound: (p₂ - 1) > 8 / (δ * log 2)
        -- Taking reciprocals: 1 / (p₂ - 1) < (δ * log 2) / 8
        have hrhs_pos : 0 < 8 / (δ * Real.log 2) := by positivity
        have hrhs := one_div_lt_one_div_of_lt hrhs_pos hp₂m1_bound
        -- hrhs : 1 / (p₂ - 1) < 1 / (8 / (δ * Real.log 2))
        -- And 1 / (8 / (δ * Real.log 2)) = (δ * Real.log 2) / 8
        convert hrhs using 1
        field_simp

      -- log(p/(p-1)) = log(1 + 1/(p-1))
      have hlog_eq : Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) =
          Real.log (1 + 1 / ((p₂ : ℝ) - 1)) := by
        congr 1
        field_simp
        ring

      -- log(1 + x) < x for x > 0 (using log(y) < y - 1 for y ≠ 1)
      have hx_pos : 1 / ((p₂ : ℝ) - 1) > 0 := by positivity
      have hlog_le : Real.log (1 + 1 / ((p₂ : ℝ) - 1)) < 1 / ((p₂ : ℝ) - 1) := by
        have hy_pos : 0 < 1 + 1 / ((p₂ : ℝ) - 1) := by linarith
        have hy_ne_1 : 1 + 1 / ((p₂ : ℝ) - 1) ≠ 1 := by linarith
        have hexp := Real.log_lt_sub_one_of_pos hy_pos hy_ne_1
        calc Real.log (1 + 1 / ((p₂ : ℝ) - 1))
            < (1 + 1 / ((p₂ : ℝ) - 1)) - 1 := hexp
          _ = 1 / ((p₂ : ℝ) - 1) := by ring

      -- Combine: log(p₂/(p₂-1)) < 1/(p₂-1) < (δ · log(2))/8
      have hlog_bound : Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) < δ * Real.log 2 / 8 := by
        calc Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1))
            = Real.log (1 + 1 / ((p₂ : ℝ) - 1)) := hlog_eq
          _ < 1 / ((p₂ : ℝ) - 1) := hlog_le
          _ < δ * Real.log 2 / 8 := hinv_bound

      -- c_2 · log(p₂/(p₂-1)) < (1/log(2)) · (δ · log(2)/8) = δ/8 < δ/4
      calc c_prime E p₂ hp₂ * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1))
          < c_prime E 2 Nat.prime_two * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) := hcorr_lt
        _ = (1 / Real.log 2) * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) := by rw [hc2_bound]
        _ < (1 / Real.log 2) * (δ * Real.log 2 / 8) := by
            apply mul_lt_mul_of_pos_left hlog_bound
            positivity
        _ = δ / 8 := by
            have hlog2_ne : Real.log 2 ≠ 0 := log_two_pos.ne'
            field_simp [hlog2_ne]
        _ < δ / 4 := by linarith

  -- Step 6: Combine to get λ_{p₂} < -δ + δ/4 = -3δ/4 < -δ/4
  have hlambda_neg : entropyIncrement E p₂ hp₂.one_lt < -δ / 4 := by
    calc entropyIncrement E p₂ hp₂.one_lt
        ≤ (c_prime E p₂ hp₂ - c_prime E 2 Nat.prime_two) * Real.log 2 +
          c_prime E p₂ hp₂ * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - 1)) := hlambda_upper
      _ < -δ + δ / 4 := by linarith [hmain_lt_neg_delta, hcorr_bound]
      _ = -3 * δ / 4 := by ring
      _ < -δ / 4 := by linarith

  -- Step 7: But |λ_{p₂}| < δ/4 by hN
  have hp₂_sub_ge_N : p₂ - 2 ≥ N := by omega
  have hspec := hN (p₂ - 2) hp₂_sub_ge_N
  have hp₂_add : (p₂ - 2) + 2 = p₂ := by omega
  simp only [hp₂_add] at hspec

  -- hspec : dist (entropyIncrement E p₂ hp₂.one_lt) 0 < δ/4
  rw [Real.dist_eq, sub_zero] at hspec
  -- |λ_{p₂}| < δ/4 means -δ/4 < λ_{p₂} < δ/4
  -- But λ_{p₂} < -δ/4, contradiction
  -- From |λ| < δ/4, we get -(δ/4) < λ (using abs_lt)
  have habs_bound : -δ / 4 < entropyIncrement E p₂ hp₂.one_lt := by
    rw [abs_lt] at hspec
    -- hspec.1 : -(δ / 4) < λ, but we need -δ / 4 < λ
    -- These are equal: -(δ/4) = -δ/4
    convert hspec.1 using 1
    ring

  -- hlambda_neg: λ < -δ/4
  -- habs_bound: -δ/4 < λ
  -- These contradict each other
  linarith

set_option maxHeartbeats 800000 in
/-- **Faddeev's Lemma 9**: All c_p are equal.

    Proof: Let p_max achieve the maximum from Lemma 8.
    Apply the λ → 0 argument to the sequence p_max^m - 1 to show c_{p_max} ≤ c_2.
    Similarly, c_{p_min} ≥ c_2.
    Therefore all c_p = c_2. -/
theorem faddeev_c_prime_all_equal (E : FaddeevEntropy) :
    ∀ p q : ℕ, ∀ hp : Nat.Prime p, ∀ hq : Nat.Prime q,
      c_prime E p hp = c_prime E q hq := by
  -- DETAILED PROOF OUTLINE:
  --
  -- Step 1: Get p_max achieving maximum from Lemma 8.
  -- obtain ⟨p_max, hp_max, h_max⟩ := faddeev_c_prime_has_max E
  --
  -- Step 2: SHOW c_{p_max} ≤ c_2.
  -- If p_max = 2, then c_{p_max} = c_2, done.
  -- Otherwise p_max > 2, so p_max is odd.
  --
  -- Consider the sequence n_m = p_max^m for m = 1, 2, 3, ...
  -- Factor: p_max^m - 1 = (p_max - 1)(p_max^{m-1} + ... + 1)
  --
  -- KEY IDENTITY for λ_{p_max^m}:
  --   λ_{p_max^m} = F(p_max^m) - F(p_max^m - 1)
  --               = m · c_{p_max} · log(p_max) - F(p_max^m - 1)
  --
  -- Since all prime factors q of p_max^m - 1 satisfy q < p_max,
  -- and p_max achieves the maximum, we have c_q ≤ c_{p_max}.
  --
  -- Since p_max is odd, p_max^m - 1 is even, so 2 | (p_max^m - 1).
  --
  -- Similar rearrangement gives:
  --   λ_{p_max^m} = c_{p_max} · [m·log(p_max) - log(p_max^m - 1)]
  --                 + Σ α · (c_{p_max} - c_q) · log(q)
  --              ≥ c_{p_max} · [m·log(p_max) - log(p_max^m - 1)]
  --                 + (c_{p_max} - c_2) · α_2 · log(2)
  --
  -- As m → ∞:
  --   m·log(p_max) - log(p_max^m - 1) = log(p_max^m / (p_max^m - 1))
  --                                      = log(1 + 1/(p_max^m - 1)) → 0
  --
  -- But if c_{p_max} > c_2, then the second term provides a uniform positive bound,
  -- preventing λ_{p_max^m} → 0. Contradiction with faddeev_lambda_tendsto_zero!
  --
  -- Therefore c_{p_max} ≤ c_2.
  --
  -- Step 3: SHOW c_{p_min} ≥ c_2 (symmetric argument).
  -- obtain ⟨p_min, hp_min, h_min⟩ := faddeev_c_prime_has_min E
  -- Similar argument shows c_{p_min} ≥ c_2.
  --
  -- Step 4: CONCLUDE all c_p = c_2.
  -- For any prime p:
  --   c_{p_min} ≤ c_p ≤ c_{p_max}  [by Lemmas 8, 8']
  --   c_2 ≤ c_p ≤ c_2              [by Steps 2, 3]
  --   c_p = c_2
  --
  -- Since this holds for all primes p, q: c_p = c_q = c_2.
  --
  -- ACTUAL PROOF: Use λ_n → 0 to show all c_p = c_2

  -- Step 1: Get p_max achieving maximum
  obtain ⟨p_max, hp_max, h_max⟩ := faddeev_c_prime_has_max E

  -- Step 2: Show c_{p_max} ≤ c_2
  -- If p_max = 2, this is trivial. Otherwise, use the power sequence argument.
  have h_max_le_c2 : c_prime E p_max hp_max ≤ c_prime E 2 Nat.prime_two := by
    by_cases hp_max_eq_2 : p_max = 2
    · simp only [hp_max_eq_2, le_refl]
    · -- p_max > 2, odd. Use contradiction via λ → 0.
      by_contra h_max_gt_c2
      push_neg at h_max_gt_c2
      -- δ := (c_{p_max} - c_2) * log 2 > 0
      set δ := (c_prime E p_max hp_max - c_prime E 2 Nat.prime_two) * Real.log 2 with hδ_def
      have hδ_pos : 0 < δ := mul_pos (sub_pos.mpr h_max_gt_c2) log_two_pos
      -- By λ → 0, for ε = δ/2, there exists N such that |λ_n| < δ/2 for n ≥ N
      have hlim := faddeev_lambda_tendsto_zero E
      rw [Metric.tendsto_atTop] at hlim
      obtain ⟨N, hN⟩ := hlim (δ / 2) (by linarith)
      -- Find m large enough that p_max^m - 2 ≥ N
      have hp_max_ge_3 : p_max ≥ 3 := by
        have h2le := hp_max.two_le
        omega
      -- Use subsequence p_max^{2^k} for k = 1, 2, ...
      -- Key facts:
      -- 1. ord_2(p_max^{2^k} - 1) ≥ k + 1 (since p_max odd implies each factor 2^j + 1 is even)
      -- 2. F(p_max^{2^k}) = 2^k · c_{p_max} · log(p_max)
      -- 3. F(p_max^{2^k} - 1) = a_k + F(b_k) where b_k is odd
      -- 4. F(b_k) ≤ c_{p_max} · log(b_k) since p_max achieves max
      -- 5. λ_{p_max^{2^k}} ≥ a_k · (c_{p_max} - c_2) · log(2) + o(1) → +∞

      -- Find k₀ large enough that p_max^{2^{k₀}} - 2 ≥ N
      have hpow_large : ∃ k₀ : ℕ, N + 2 ≤ p_max ^ (2 ^ k₀) := by
        have hp_ge_2 : 2 ≤ p_max := hp_max.two_le
        use N + 2
        have h1 : 2 ^ (2 ^ (N + 2)) ≤ p_max ^ (2 ^ (N + 2)) := Nat.pow_le_pow_left hp_ge_2 _
        have h2 : N + 2 ≤ 2 ^ (N + 2) := (@Nat.lt_two_pow_self (N + 2)).le
        have h3 : 2 ^ (N + 2) ≤ 2 ^ (2 ^ (N + 2)) :=
          Nat.pow_le_pow_right (by norm_num) h2
        omega
      obtain ⟨k₀, hk₀⟩ := hpow_large

      -- For any k ≥ k₀, we have p_max^{2^k} - 2 ≥ N
      have hk_large : ∀ k ≥ k₀, N ≤ p_max ^ (2 ^ k) - 2 := by
        intro k hk
        have h1 : p_max ^ (2 ^ k₀) ≤ p_max ^ (2 ^ k) := by
          apply Nat.pow_le_pow_right hp_max.pos
          exact Nat.pow_le_pow_right (by norm_num) hk
        omega

      -- p_max is odd since p_max ≠ 2
      have hp_max_odd : Odd p_max := hp_max.odd_of_ne_two hp_max_eq_2

      -- For k ≥ 1, factor p_max^{2^k} - 1 = 2^{a_k} · b_k
      -- Key: a_k ≥ k + 1 for odd p_max ≥ 3
      have hord2_growth : ∀ k ≥ 1, k + 1 ≤ (p_max ^ (2 ^ k) - 1).factorization 2 := by
        intro k hk
        -- p_max^{2^k} - 1 = (p_max^{2^{k-1}} - 1)(p_max^{2^{k-1}} + 1)
        -- Each application of this factorization adds at least one factor of 2
        -- since p_max^{2^j} + 1 is even for odd p_max
        induction k with
        | zero => omega
        | succ k' ih =>
          by_cases hk' : k' = 0
          · -- Base: k = 1, need ord_2(p_max^2 - 1) ≥ 2
            -- p_max^2 - 1 = (p_max - 1)(p_max + 1)
            -- Both p_max - 1 and p_max + 1 are even for odd p_max ≥ 3
            simp only [hk']
            -- 2 | p_max - 1 since p_max is odd
            have h1 : 2 ∣ p_max - 1 := by
              rcases hp_max_odd with ⟨m, rfl⟩
              simp only [add_tsub_cancel_right, dvd_mul_right]
            -- 2 | p_max + 1 since p_max is odd
            have h2 : 2 ∣ p_max + 1 := Even.two_dvd (Odd.add_one hp_max_odd)
            have hp_ge_1 : 1 ≤ p_max := by omega
            have hp_sq_ge_1 : 1 ≤ p_max ^ 2 := Nat.one_le_pow 2 p_max (by omega)
            have h3 : p_max ^ 2 - 1 = (p_max - 1) * (p_max + 1) := by
              zify [hp_ge_1, hp_sq_ge_1]
              ring
            -- Both factors are ≥ 2, so the product has ord_2 ≥ 2
            have hp_ge_3 : 3 ≤ p_max := hp_max_ge_3
            have hdvd4 : 4 ∣ (p_max - 1) * (p_max + 1) := by
              -- p_max - 1 and p_max + 1 are consecutive even numbers
              -- One of them is divisible by 4
              have hdiv1 : p_max - 1 = (p_max - 1) / 2 * 2 := (Nat.div_mul_cancel h1).symm
              have hdiv2 : p_max + 1 = (p_max + 1) / 2 * 2 := (Nat.div_mul_cancel h2).symm
              rcases Nat.even_or_odd ((p_max - 1) / 2) with ⟨m, hm⟩ | ⟨m, hm⟩
              · -- (p_max - 1)/2 = 2m, so p_max - 1 = 4m
                have hpm1_eq : p_max - 1 = 4 * m := by omega
                exact ⟨m * (p_max + 1), by rw [hpm1_eq]; ring⟩
              · -- (p_max - 1)/2 = 2m + 1, so (p_max + 1)/2 = 2m + 2 is even
                have hpp1_half : (p_max + 1) / 2 = (p_max - 1) / 2 + 1 := by
                  have : p_max + 1 = (p_max - 1) + 2 := by omega
                  rw [this, Nat.add_div_right _ (by norm_num : 0 < 2)]
                have hpp1_half_even : Even ((p_max + 1) / 2) := by
                  rw [hpp1_half, hm]
                  exact ⟨m + 1, by ring⟩
                obtain ⟨n, hn⟩ := hpp1_half_even
                have hpp1_eq : p_max + 1 = 4 * n := by omega
                exact ⟨(p_max - 1) * n, by rw [hpp1_eq]; ring⟩
            -- 4 | (p_max - 1)(p_max + 1) implies ord_2 ≥ 2
            have hne : (p_max - 1) * (p_max + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
            have h2pow : 2 ^ 2 ∣ (p_max - 1) * (p_max + 1) := by simpa using hdvd4
            have hord2 := Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne |>.mp h2pow
            calc (p_max ^ (2 ^ 1) - 1).factorization 2
                = (p_max ^ 2 - 1).factorization 2 := by norm_num
              _ = ((p_max - 1) * (p_max + 1)).factorization 2 := by rw [h3]
              _ ≥ 2 := hord2
          · -- Inductive step: k' ≥ 1
            have hk'_ge_1 : 1 ≤ k' := Nat.one_le_iff_ne_zero.mpr hk'
            have ih' := ih hk'_ge_1
            -- p_max^{2^{k'+1}} - 1 = (p_max^{2^{k'}} - 1)(p_max^{2^{k'}} + 1)
            set a := p_max ^ (2 ^ k') with ha_def
            have ha_ge_1 : 1 ≤ a := Nat.one_le_pow _ _ hp_max.pos
            -- a ≥ 3 since p_max ≥ 3 and k' ≥ 1 means 2^k' ≥ 2
            have ha_ge_3 : 3 ≤ a := by
              have h1 : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
              calc a = p_max ^ (2 ^ k') := rfl
                _ ≥ p_max ^ 1 := Nat.pow_le_pow_right hp_max.pos h1
                _ = p_max := by ring
                _ ≥ 3 := hp_max_ge_3
            have ha_sq_ge_1 : 1 ≤ a * a := by nlinarith
            have hfact : p_max ^ (2 ^ (k' + 1)) - 1 = (a - 1) * (a + 1) := by
              have h2pow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by ring
              rw [h2pow, pow_add, ← ha_def]
              -- a * a - 1 = (a - 1) * (a + 1) when a ≥ 1
              zify [ha_ge_1, ha_sq_ge_1]
              ring
            -- a is odd (power of odd number)
            have ha_odd : Odd a := hp_max_odd.pow
            -- a + 1 is even, so ord_2(a + 1) ≥ 1
            have heven_succ : 2 ∣ a + 1 := Even.two_dvd (Odd.add_one ha_odd)
            have hord2_succ : 1 ≤ (a + 1).factorization 2 := by
              have hne : a + 1 ≠ 0 := by omega
              have h2pow : 2 ^ 1 ∣ a + 1 := by simpa using heven_succ
              exact Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne |>.mp h2pow
            -- Both factors are nonzero (a ≥ 3 ensures a - 1 ≥ 2 > 0)
            have ham1_ne : a - 1 ≠ 0 := by omega
            have hap1_ne : a + 1 ≠ 0 := by omega
            -- Use Nat.factorization_mul (no coprimality needed!)
            have hfact_mul := Nat.factorization_mul ham1_ne hap1_ne
            -- ord_2(product) = ord_2(a-1) + ord_2(a+1)
            calc (p_max ^ (2 ^ (k' + 1)) - 1).factorization 2
                = ((a - 1) * (a + 1)).factorization 2 := by rw [hfact]
              _ = (a - 1).factorization 2 + (a + 1).factorization 2 := by
                  rw [hfact_mul]; rfl
              _ ≥ (k' + 1) + 1 := by
                  -- By IH: (a - 1).factorization 2 ≥ k' + 1
                  -- By hord2_succ: (a + 1).factorization 2 ≥ 1
                  have hih : (k' + 1) ≤ (a - 1).factorization 2 := ih'
                  omega
              _ = k' + 1 + 1 := by ring
      -- Now use this to get the contradiction
      -- Pick k = max(k₀, 2) to ensure both conditions
      set k := max k₀ 2 with hk_def
      have hk_ge_k0 : k ≥ k₀ := le_max_left _ _
      have hk_ge_2 : k ≥ 2 := le_max_right _ _
      have hk_ge_1 : k ≥ 1 := by omega
      have hN_le := hk_large k hk_ge_k0
      have hord2 := hord2_growth k hk_ge_1
      -- Get the factorization
      set n := p_max ^ (2 ^ k) with hn_def
      have hn_pos : 0 < n := Nat.pow_pos hp_max.pos
      have hn_ge_2 : 2 ≤ n := by
        have h1 : 1 ≤ 2 ^ k := @Nat.one_le_two_pow k
        calc n = p_max ^ (2 ^ k) := rfl
          _ ≥ p_max ^ 1 := Nat.pow_le_pow_right hp_max.pos h1
          _ = p_max := pow_one _
          _ ≥ 3 := hp_max_ge_3
          _ ≥ 2 := by norm_num
      have hn1_pos : 0 < n - 1 := by omega
      have hn1_ne : n - 1 ≠ 0 := by omega
      -- Factor n - 1 = 2^a · b where b is odd
      obtain ⟨a, b, hb_odd, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1_ne 2 (by norm_num)
      have hb_pos : 0 < b := by
        by_contra hb_zero
        push_neg at hb_zero
        interval_cases b; simp_all
      have hb_ne : b ≠ 0 := by omega
      have ha_ge : k + 1 ≤ a := by
        -- 2^a and b are coprime since b is odd
        have hcop : (2 ^ a).Coprime b :=
          Nat.Coprime.pow_left _ (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr hb_odd)
        have h2a_ne : 2 ^ a ≠ 0 := ne_of_gt (Nat.pow_pos (by norm_num : 0 < 2))
        have hfact_eq : (n - 1).factorization 2 = a := by
          calc (n - 1).factorization 2 = (2 ^ a * b).factorization 2 := by rw [hab]
            _ = (2 ^ a).factorization 2 + b.factorization 2 := by
                rw [Nat.factorization_mul h2a_ne hb_ne]; rfl
            _ = a + 0 := by
                have h1 : (2 ^ a).factorization 2 = a := by
                  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
                    Nat.Prime.factorization_self Nat.prime_two, mul_one]
                have h2 : b.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hb_odd
                rw [h1, h2]
            _ = a := by ring
        rw [← hfact_eq]
        exact hord2
      -- Now compute the entropy increment bound
      -- F(n) = 2^k · F(p_max) and F(n-1) = a + F(b)
      have hFn := faddeev_F_pow E hp_max.pos (2 ^ k)
      have hFn1 := F_two_pow_mul E a hb_pos
      -- entropyIncrement at n
      have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
      -- Key insight: since p_max achieves the maximum of {c_q : q prime},
      -- we have c_q ≤ c_{p_max} for ALL primes q (not just those < p_max).
      -- Therefore F(b) ≤ c_{p_max} · log(b) for ANY odd b by F_odd_upper_bound.
      have hb_bound : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ b → Odd q → c_prime E q hq ≤ c_prime E p_max hp_max :=
        fun q hq _ _ => h_max q hq
      have hb_is_odd : Odd b := (Nat.even_or_odd b).resolve_left (fun heven => hb_odd (Even.two_dvd heven))
      have hFb_bound := F_odd_upper_bound E hb_pos hb_is_odd (c_prime E p_max hp_max) hb_bound

      -- Now compute the entropy increment
      -- λ_n = F(n) - F(n-1) = 2^k · F(p_max) - (a + F(b))
      -- Using F(p_max) = c_{p_max} · log(p_max):
      -- λ_n = 2^k · c_{p_max} · log(p_max) - a - F(b)
      --     ≥ 2^k · c_{p_max} · log(p_max) - a - c_{p_max} · log(b)
      --     = c_{p_max} · (2^k · log(p_max) - log(b)) - a

      -- Key identity: log(n) - log(n-1) = log(1 + 1/(n-1)) ≈ 1/(n-1) → 0
      -- And: 2^k · log(p_max) - log(b) = log(n) - log(b) = log(n/b) = log(2^a) + log(1 + 1/(n-1))
      --                                 = a · log(2) + ε_k where ε_k → 0

      -- So: λ_n ≥ c_{p_max} · (a · log(2) + ε_k) - a
      --        = a · (c_{p_max} · log(2) - 1) + c_{p_max} · ε_k
      --        = a · (c_{p_max} - c_2) · log(2) + c_{p_max} · ε_k
      -- Since c_{p_max} > c_2, and a ≥ k + 1 → ∞, this → +∞, contradicting λ → 0.

      -- The formal calculation:
      have hFpmax := F_prime_eq_c_times_log E hp_max
      -- F(p_max) = c_{p_max} · log(p_max)

      -- For the limit argument, we need to show λ_n > δ for large n
      -- We have: F(n) = F(p_max^{2^k}) = 2^k · F(p_max) = 2^k · c_{p_max} · log(p_max)
      --          F(n-1) = a + F(b) ≤ a + c_{p_max} · log(b)
      -- So: λ_n ≥ 2^k · c_{p_max} · log(p_max) - a - c_{p_max} · log(b)

      -- Using n = 2^a · b + 1, we have:
      -- log(n) = log(2^a · b + 1) = log(2^a · b) + log(1 + 1/(2^a · b))
      --        = a · log(2) + log(b) + ε where ε = log(1 + 1/(n-1)) > 0

      -- So: 2^k · log(p_max) = log(p_max^{2^k}) = log(n) = a · log(2) + log(b) + ε
      -- Therefore: 2^k · log(p_max) - log(b) = a · log(2) + ε

      -- λ_n ≥ c_{p_max} · (a · log(2) + ε) - a - c_{p_max} · log(b)
      --     = c_{p_max} · a · log(2) + c_{p_max} · ε - a
      --     = a · (c_{p_max} · log(2) - 1) + c_{p_max} · ε

      -- Since c_2 = 1/log(2), we have c_2 · log(2) = 1, so:
      -- c_{p_max} · log(2) - 1 = (c_{p_max} - c_2) · log(2) = δ / log(2) · log(2) / log(2)... wait

      -- Actually: δ = (c_{p_max} - c_2) · log(2), so:
      -- c_{p_max} · log(2) - 1 = c_{p_max} · log(2) - c_2 · log(2) = (c_{p_max} - c_2) · log(2) = δ

      -- So: λ_n ≥ a · δ + c_{p_max} · ε > a · δ ≥ (k + 1) · δ

      -- For k large enough that (k + 1) · δ > δ/2, we get λ_n > δ/2.
      -- But by hN, for n - 2 ≥ N, we have |λ_n| < δ/2. Contradiction!

      -- Since the above calculation requires careful handling of real arithmetic and logs,
      -- we defer to the key bound: for large k, λ_n ≥ (k + 1) · δ which eventually exceeds δ/2.

      have hc2_eq : c_prime E 2 Nat.prime_two * Real.log 2 = 1 := by
        rw [c_prime_two E]
        field_simp
      have hδ_eq : (c_prime E p_max hp_max - c_prime E 2 Nat.prime_two) * Real.log 2 = δ := rfl

      -- For k ≥ 1, we have a ≥ k + 1 ≥ 2
      have ha_pos : 0 < a := by linarith [ha_ge, hk_ge_1]

      -- Now derive the contradiction via entropy increment bound
      -- First, compute F(p_max) = c_{p_max} · log(p_max)
      have hFp_eq : F E p_max hp_max.pos = c_prime E p_max hp_max * Real.log p_max := by
        rw [c_prime]
        have hlog_pos : 0 < Real.log p_max := by
          apply Real.log_pos
          have h := hp_max.one_lt
          exact Nat.one_lt_cast.mpr h
        field_simp

      -- F(n) = 2^k · F(p_max) = 2^k · c_{p_max} · log(p_max) = c_{p_max} · log(n)
      have hFn_eq : F E n hn_pos = (2 ^ k : ℕ) * c_prime E p_max hp_max * Real.log p_max := by
        have h1 : F E n hn_pos = (2 ^ k : ℕ) * F E p_max hp_max.pos := by
          have h2 : n = p_max ^ (2 ^ k) := hn_def
          calc F E n hn_pos = F E (p_max ^ (2 ^ k)) (by rw [← hn_def]; exact hn_pos) := by congr 1
            _ = (2 ^ k : ℕ) * F E p_max hp_max.pos := hFn
        rw [h1, hFp_eq]
        ring

      -- F(n-1) = a + F(b) and F(b) ≤ c_{p_max} · log(b)
      have hFn1_eq : F E (n - 1) hn1_pos = a + F E b hb_pos := by
        have h : n - 1 = 2 ^ a * b := hab
        calc F E (n - 1) hn1_pos = F E (2 ^ a * b) (by rw [← hab]; exact hn1_pos) := by
              congr 1
          _ = a + F E b hb_pos := hFn1

      -- The entropy increment is F(n) - F(n-1)
      have hn_gt_1 : 1 < n := by omega
      have hlam_eq : entropyIncrement E n hn_gt_1 = F E n (by omega) - F E (n - 1) (by omega) := rfl

      -- Compute the lower bound
      -- λ_n = F(n) - F(n-1)
      --     = 2^k · c_{p_max} · log(p_max) - (a + F(b))
      --     ≥ 2^k · c_{p_max} · log(p_max) - a - c_{p_max} · log(b)
      --     = c_{p_max} · (2^k · log(p_max) - log(b)) - a
      --     = c_{p_max} · log(p_max^{2^k} / b) - a
      --     = c_{p_max} · log(n / b) - a

      -- Key fact: n - 1 = 2^a · b, so b = (n-1) / 2^a
      -- Hence n / b = n · 2^a / (n - 1) = 2^a · n / (n - 1) = 2^a · (1 + 1/(n-1))
      -- So log(n/b) = a · log(2) + log(1 + 1/(n-1))

      -- Therefore: λ_n ≥ c_{p_max} · (a · log(2) + log(1 + 1/(n-1))) - a
      --               = a · (c_{p_max} · log(2) - 1) + c_{p_max} · log(1 + 1/(n-1))
      --               = a · δ + (positive term)

      -- The key: c_{p_max} · log(2) - 1 = (c_{p_max} - c_2) · log(2) = δ
      have hcpmax_log2_sub_1 : c_prime E p_max hp_max * Real.log 2 - 1 = δ := by
        calc c_prime E p_max hp_max * Real.log 2 - 1
            = c_prime E p_max hp_max * Real.log 2 - c_prime E 2 Nat.prime_two * Real.log 2 := by
                rw [hc2_eq]
          _ = (c_prime E p_max hp_max - c_prime E 2 Nat.prime_two) * Real.log 2 := by ring
          _ = δ := rfl

      -- Since a ≥ k + 1 ≥ 3, and δ > 0, we have a · δ ≥ 3δ
      have ha_ge_3 : 3 ≤ a := by omega

      -- Apply hN: for m ≥ N, |λ_{m+2}| < δ/2
      -- We have n - 2 ≥ N, so |λ_n| < δ/2
      have hlam_bound := hN (n - 2) hN_le
      simp only [Nat.sub_add_cancel (by omega : 2 ≤ n)] at hlam_bound

      -- Key positivity facts
      have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hn1_real_pos : (0 : ℝ) < n - 1 := by
        have h : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn_gt_1
        linarith
      have hb_real_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb_pos

      have hc_pos : 0 < c_prime E p_max hp_max := by
        have hc2_pos : 0 < c_prime E 2 Nat.prime_two := by
          rw [c_prime_two E]; positivity
        linarith [h_max_gt_c2]

      -- The key calculation: n - 1 = 2^a · b, so n / b = 2^a · n / (n-1)
      have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have h2a_ne : (2 : ℝ) ^ a ≠ 0 := pow_ne_zero a (by norm_num)
      have hb_ne' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn1_ne : (n : ℝ) - 1 ≠ 0 := by linarith

      have hn1_eq_2ab : (n : ℝ) - 1 = 2 ^ a * b := by
        rw [← hn1_cast]
        have h := hab  -- (n - 1 : ℕ) = 2^a * b
        norm_cast

      have hnb_eq : (n : ℝ) / b = 2 ^ a * n / (n - 1) := by
        have h1 : (n : ℝ) / b = n * (1 / b) := by ring
        have h2 : (1 : ℝ) / b = 2 ^ a / (n - 1) := by
          rw [hn1_eq_2ab]
          field_simp
        rw [h1, h2]
        field_simp [hn1_ne]

      -- log(n/b) = a · log(2) + log(n/(n-1))
      have h_ratio_pos : 0 < (n : ℝ) / (n - 1) := div_pos hn_real_pos hn1_real_pos
      have h2a_pos : (0 : ℝ) < 2 ^ a := pow_pos (by norm_num : (0 : ℝ) < 2) a

      have hlog_nb : Real.log (n / b) = a * Real.log 2 + Real.log (n / (n - 1)) := by
        rw [hnb_eq, mul_div_assoc]
        rw [Real.log_mul (ne_of_gt h2a_pos) (ne_of_gt h_ratio_pos), Real.log_pow]

      -- log(n / (n-1)) > 0 since n > n - 1
      have hlog_ratio_pos : 0 < Real.log (n / (n - 1)) := by
        have h1 : (n : ℝ) / (n - 1) > 1 := by
          have hn_gt_n1 : (n : ℝ) > n - 1 := by linarith
          exact one_lt_div hn1_real_pos |>.mpr hn_gt_n1
        exact Real.log_pos h1

      set_option maxHeartbeats 400000 in
      -- Lower bound: λ_n ≥ a · δ
      have hlam_lower : entropyIncrement E n hn_gt_1 ≥ a * δ := by
        -- λ_n = F(n) - F(n-1) ≥ F(n) - a - c_{p_max} · log(b)
        have h1 : entropyIncrement E n hn_gt_1 = F E n (by omega) - F E (n - 1) (by omega) := rfl
        have hF1 : F E n (by omega) = F E n hn_pos := by congr 1
        have hF2 : F E (n - 1) (by omega) = F E (n - 1) hn1_pos := by congr 1
        rw [h1, hF1, hF2, hFn_eq, hFn1_eq]
        have hFb_le : F E b hb_pos ≤ c_prime E p_max hp_max * Real.log b := hFb_bound
        have hlog_n : Real.log n = (2 ^ k : ℕ) * Real.log p_max := by
          have hn_eq : (n : ℝ) = (p_max : ℝ) ^ (2 ^ k : ℕ) := by
            have h : n = p_max ^ (2 ^ k) := hn_def
            simp only [h, Nat.cast_pow]
          rw [hn_eq, Real.log_pow]
        -- Simplify: (2^k) * c * log(p) - (a + Fb) ≥ (2^k) * c * log(p) - a - c * log(b)
        --         = c * ((2^k) * log(p) - log(b)) - a = c * (log(n) - log(b)) - a
        --         = c * log(n/b) - a = c * (a * log(2) + log(n/(n-1))) - a
        --         = a * (c * log(2) - 1) + c * log(n/(n-1)) = a * δ + (positive term) ≥ a * δ
        have h_step1 : (2 ^ k : ℕ) * c_prime E p_max hp_max * Real.log p_max - (↑a + F E b hb_pos)
            ≥ (2 ^ k : ℕ) * c_prime E p_max hp_max * Real.log p_max - (a + c_prime E p_max hp_max * Real.log b) := by
          linarith [hFb_le]
        have h_step2 : (2 ^ k : ℕ) * c_prime E p_max hp_max * Real.log p_max - (a + c_prime E p_max hp_max * Real.log b)
            = c_prime E p_max hp_max * (Real.log n - Real.log b) - a := by
          -- RHS has Real.log n, substitute using hlog_n: log(n) = (2^k) * log(p)
          conv_rhs => rw [hlog_n]
          ring
        have h_step3 : c_prime E p_max hp_max * (Real.log n - Real.log b) - a
            = c_prime E p_max hp_max * Real.log (n / b) - a := by
          rw [Real.log_div (ne_of_gt hn_real_pos) (ne_of_gt hb_real_pos)]
        have h_step4 : c_prime E p_max hp_max * Real.log (n / b) - a
            = c_prime E p_max hp_max * (a * Real.log 2 + Real.log (n / (n - 1))) - a := by
          rw [hlog_nb]
        have h_step5 : c_prime E p_max hp_max * (a * Real.log 2 + Real.log (n / (n - 1))) - a
            = a * (c_prime E p_max hp_max * Real.log 2 - 1) + c_prime E p_max hp_max * Real.log (n / (n - 1)) := by
          ring
        have h_step6 : a * (c_prime E p_max hp_max * Real.log 2 - 1) + c_prime E p_max hp_max * Real.log (n / (n - 1))
            = a * δ + c_prime E p_max hp_max * Real.log (n / (n - 1)) := by
          rw [hcpmax_log2_sub_1]
        have h_step7 : a * δ + c_prime E p_max hp_max * Real.log (n / (n - 1)) ≥ a * δ := by
          linarith [mul_pos hc_pos hlog_ratio_pos]
        linarith [h_step1, h_step2, h_step3, h_step4, h_step5, h_step6, h_step7]

      -- Since a ≥ 3 and δ > 0, we have a · δ ≥ 3δ > δ/2
      have ha_ge_3_real : (3 : ℝ) ≤ a := by exact_mod_cast ha_ge_3
      have ha_δ_large : a * δ > δ / 2 := by
        have h1 : a * δ ≥ 3 * δ := by nlinarith
        have h2 : 3 * δ > δ / 2 := by linarith
        linarith

      -- So λ_n > δ/2, but hlam_bound says |λ_n| < δ/2. Contradiction!
      have hlam_large : entropyIncrement E n hn_gt_1 > δ / 2 := by linarith [hlam_lower]
      have hcontra : dist (entropyIncrement E n hn_gt_1) 0 < δ / 2 := by
        have h := hlam_bound
        convert h using 2
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith [hlam_lower, hδ_pos])] at hcontra
      linarith

  -- Step 3: For any prime p, c_p ≤ c_{p_max} ≤ c_2
  have h_all_le_c2 : ∀ p : ℕ, ∀ hp : Nat.Prime p, c_prime E p hp ≤ c_prime E 2 Nat.prime_two :=
    fun p hp => le_trans (h_max p hp) h_max_le_c2

  -- Step 4: Show c_p ≥ c_2 for all primes p (SYMMETRIC ARGUMENT)
  --
  -- **Mathematical Outline** (symmetric to Step 2):
  --
  -- 1. By contradiction: Assume ∃ prime p₀ with c_{p₀} < c_2.
  --
  -- 2. Key insight: Use the prime p_min achieving the MINIMUM c_prime.
  --    - If c_{p_min} < c_2, the power sequence n = p_min^{2^k} gives λ_n → -∞.
  --    - Since p_min achieves the min, c_{p_min} ≤ c_q for all primes q.
  --    - This gives F(b) ≥ c_{p_min} * log(b) for odd b (via F_odd_lower_bound).
  --
  -- 3. For the power sequence n = p_min^{2^k}:
  --    - n - 1 = 2^a * b where a ≥ k+1 (from 2-adic valuation) and b is odd.
  --    - F(n) = 2^k * c_{p_min} * log(p_min)
  --    - F(n-1) = a + F(b) ≥ a + c_{p_min} * log(b)
  --    - λ_n = F(n) - F(n-1) ≤ [upper bound that → -∞]
  --
  -- 4. The upper bound calculation (symmetric to Step 2's lower bound):
  --    λ_n ≤ (c_{p_min} - c_2) * (something growing) + O(1) → -∞
  --    since c_{p_min} - c_2 < 0.
  --
  -- 5. But λ_n → 0 (by faddeev_lambda_tendsto_zero), contradiction.
  --
  -- This proves: c_p ≥ c_2 for all primes p.
  -- Combined with Step 2 (c_p ≤ c_2), we get c_p = c_2 for all p.
  --
  have h_all_ge_c2 : ∀ p : ℕ, ∀ hp : Nat.Prime p, c_prime E 2 Nat.prime_two ≤ c_prime E p hp := by
    -- By faddeev_c_prime_has_min_aux, a minimum exists among {c_p}
    obtain ⟨p_min, hp_min, h_min⟩ := faddeev_c_prime_has_min_aux E

    -- For any prime p, c_{p_min} ≤ c_p
    -- In particular, c_{p_min} ≤ c_2
    have h_min_le_c2 : c_prime E p_min hp_min ≤ c_prime E 2 Nat.prime_two := h_min 2 Nat.prime_two

    -- Combined with h_max_le_c2 (c_{p_max} ≤ c_2) and h_max (c_p ≤ c_{p_max}),
    -- and the fact that p_min achieves the minimum:
    -- For any p: c_{p_min} ≤ c_p ≤ c_{p_max} ≤ c_2
    -- Also c_{p_min} ≤ c_2

    -- Case analysis on p_min:
    -- If p_min = 2: Then c_2 = c_{p_min} ≤ c_p for all p, which is what we want.
    -- If p_min ≠ 2: We need to show c_{p_min} ≥ c_2 as well.

    by_cases hp_min_eq_2 : p_min = 2
    · -- p_min = 2: Then c_{p_min} = c_2, so c_2 ≤ c_p for all p
      subst hp_min_eq_2
      intro p hp
      exact h_min p hp
    · -- p_min ≠ 2: Show c_{p_min} = c_2 using the power sequence argument
      -- By contradiction: if c_{p_min} < c_2, then λ → -∞ for the power sequence
      -- But λ → 0, contradiction. So c_{p_min} ≥ c_2.
      -- Combined with h_min_le_c2, we get c_{p_min} = c_2.

      -- The detailed power sequence argument (symmetric to Step 2) is encapsulated
      -- in faddeev_c_prime_has_min_aux. Once that's proven, we have:
      -- c_{p_min} achieves the minimum, so for any p: c_{p_min} ≤ c_p.
      -- We already have c_{p_min} ≤ c_2.
      -- The power sequence argument in faddeev_c_prime_has_min_aux shows c_{p_min} ≥ c_2.
      -- (If c_{p_min} < c_2, the λ → -∞ contradiction rules this out.)
      -- Therefore c_{p_min} = c_2, and for any p: c_2 = c_{p_min} ≤ c_p.

      intro p hp
      -- From h_min: c_{p_min} ≤ c_p
      -- We need: c_2 ≤ c_p
      -- This follows from: c_{p_min} = c_2 (which faddeev_c_prime_has_min_aux implies
      -- via the power sequence argument ruling out c_{p_min} < c_2)

      -- For now, we use the minimum directly:
      have h1 := h_min p hp  -- c_{p_min} ≤ c_p
      have h2 := h_min 2 Nat.prime_two  -- c_{p_min} ≤ c_2

      -- We also have c_{p_max} ≤ c_2 from Step 2, and c_p ≤ c_{p_max}
      -- So: c_{p_min} ≤ c_p ≤ c_{p_max} ≤ c_2 and c_{p_min} ≤ c_2
      -- This gives c_{p_min} ≤ c_2

      -- The key insight from faddeev_c_prime_has_min_aux is that c_{p_min} = c_2:
      -- If c_{p_min} < c_2, the power sequence p_min^{2^k} would give λ → -∞,
      -- contradicting λ → 0. So c_{p_min} ≥ c_2.
      -- Combined with h_min_le_c2 (c_{p_min} ≤ c_2), we get c_{p_min} = c_2.

      -- Therefore c_2 = c_{p_min} ≤ c_p
      have h_eq : c_prime E p_min hp_min = c_prime E 2 Nat.prime_two := by
        apply le_antisymm h_min_le_c2
        -- Need: c_2 ≤ c_{p_min}
        -- By contradiction: if c_{p_min} < c_2, the power sequence p_min^{2^k} gives λ → -∞
        -- This contradicts λ → 0 (faddeev_lambda_tendsto_zero).
        by_contra h_lt_c2
        push_neg at h_lt_c2

        -- p_min ≠ 2, so p_min ≥ 3 and odd
        have hp_min_ge_3 : 3 ≤ p_min := by
          have h2le := hp_min.two_le
          omega
        have hp_min_odd : Odd p_min := hp_min.odd_of_ne_two hp_min_eq_2

        -- δ = (c_2 - c_{p_min}) · log(2) > 0
        set δ := (c_prime E 2 Nat.prime_two - c_prime E p_min hp_min) * Real.log 2 with hδ_def
        have hδ_pos : 0 < δ := by
          rw [hδ_def]; apply mul_pos; · linarith
          · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

        -- By λ → 0, ∃ N such that for m ≥ N, |λ_{m+2}| < δ/2
        have h_lim := faddeev_lambda_tendsto_zero E
        rw [Metric.tendsto_atTop] at h_lim
        obtain ⟨N, hN⟩ := h_lim (δ / 2) (by linarith)

        -- LTE: 2-adic valuation of p_min^{2^k} - 1 grows (ord_2 ≥ k + 1 for k ≥ 1)
        have hord2_growth : ∀ k ≥ 1, k + 1 ≤ (p_min ^ (2 ^ k) - 1).factorization 2 := by
          intro k hk
          induction k with
          | zero => omega
          | succ k' ih =>
            by_cases hk' : k' = 0
            · -- Base: k = 1, need ord_2(p_min^2 - 1) ≥ 2
              simp only [hk']
              have h1 : 2 ∣ p_min - 1 := by
                rcases hp_min_odd with ⟨m, rfl⟩; simp only [add_tsub_cancel_right, dvd_mul_right]
              have h2 : 2 ∣ p_min + 1 := Even.two_dvd (Odd.add_one hp_min_odd)
              have hp_ge_1 : 1 ≤ p_min := by omega
              have hp_sq_ge_1 : 1 ≤ p_min ^ 2 := Nat.one_le_pow 2 p_min (by omega)
              have h3 : p_min ^ 2 - 1 = (p_min - 1) * (p_min + 1) := by zify [hp_ge_1, hp_sq_ge_1]; ring
              have hdvd4 : 4 ∣ (p_min - 1) * (p_min + 1) := by
                have hdiv1 : p_min - 1 = (p_min - 1) / 2 * 2 := (Nat.div_mul_cancel h1).symm
                have hdiv2 : p_min + 1 = (p_min + 1) / 2 * 2 := (Nat.div_mul_cancel h2).symm
                rcases Nat.even_or_odd ((p_min - 1) / 2) with ⟨m, hm⟩ | ⟨m, hm⟩
                · have hpm1_eq : p_min - 1 = 4 * m := by omega
                  exact ⟨m * (p_min + 1), by rw [hpm1_eq]; ring⟩
                · have hpp1_half : (p_min + 1) / 2 = (p_min - 1) / 2 + 1 := by
                    have : p_min + 1 = (p_min - 1) + 2 := by omega
                    rw [this, Nat.add_div_right _ (by norm_num : 0 < 2)]
                  have hpp1_half_even : Even ((p_min + 1) / 2) := by rw [hpp1_half, hm]; exact ⟨m + 1, by ring⟩
                  obtain ⟨n, hn⟩ := hpp1_half_even
                  have hpp1_eq : p_min + 1 = 4 * n := by omega
                  exact ⟨(p_min - 1) * n, by rw [hpp1_eq]; ring⟩
              have hne : (p_min - 1) * (p_min + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
              have h2pow : 2 ^ 2 ∣ (p_min - 1) * (p_min + 1) := by simpa using hdvd4
              have hord2 := Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne |>.mp h2pow
              calc (p_min ^ (2 ^ 1) - 1).factorization 2 = (p_min ^ 2 - 1).factorization 2 := by norm_num
                _ = ((p_min - 1) * (p_min + 1)).factorization 2 := by rw [h3]
                _ ≥ 2 := hord2
            · -- Inductive step: k' ≥ 1
              have hk'_ge_1 : 1 ≤ k' := Nat.one_le_iff_ne_zero.mpr hk'
              have ih' := ih hk'_ge_1
              set a := p_min ^ (2 ^ k') with ha_def
              have ha_ge_1 : 1 ≤ a := Nat.one_le_pow _ _ hp_min.pos
              have ha_ge_3 : 3 ≤ a := by
                have h1 : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
                calc a = p_min ^ (2 ^ k') := rfl
                  _ ≥ p_min ^ 1 := Nat.pow_le_pow_right hp_min.pos h1
                  _ = p_min := by ring
                  _ ≥ 3 := hp_min_ge_3
              have ha_sq_ge_1 : 1 ≤ a * a := by nlinarith
              have hfact : p_min ^ (2 ^ (k' + 1)) - 1 = (a - 1) * (a + 1) := by
                have h2pow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by ring
                rw [h2pow, pow_add, ← ha_def]; zify [ha_ge_1, ha_sq_ge_1]; ring
              have ha_odd : Odd a := hp_min_odd.pow
              have heven_succ : 2 ∣ a + 1 := Even.two_dvd (Odd.add_one ha_odd)
              have hord2_succ : 1 ≤ (a + 1).factorization 2 := by
                have hne : a + 1 ≠ 0 := by omega
                have h2pow : 2 ^ 1 ∣ a + 1 := by simpa using heven_succ
                exact Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne |>.mp h2pow
              have ham1_ne : a - 1 ≠ 0 := by omega
              have hap1_ne : a + 1 ≠ 0 := by omega
              have hfact_mul := Nat.factorization_mul ham1_ne hap1_ne
              calc (p_min ^ (2 ^ (k' + 1)) - 1).factorization 2
                  = ((a - 1) * (a + 1)).factorization 2 := by rw [hfact]
                _ = (a - 1).factorization 2 + (a + 1).factorization 2 := by rw [hfact_mul]; rfl
                _ ≥ (k' + 1) + 1 := by have hih : (k' + 1) ≤ (a - 1).factorization 2 := ih'; omega
                _ = k' + 1 + 1 := by ring

        -- Find k large enough that n - 2 ≥ N AND correction term < δ/4
        -- Use a simple approach: pick k large enough that p_min^{2^k} > max(N+3, 4·c_2/δ + 2)
        have hc2_pos : 0 < c_prime E 2 Nat.prime_two := by rw [c_prime_two E]; positivity

        -- Helper: 2^k ≥ k + 1 for all k
        have h2k_bound : ∀ k : ℕ, 2 ^ k ≥ k + 1 := by
          intro k; induction k with
          | zero => simp
          | succ n ih =>
            calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
              _ ≥ 2 * (n + 1) := Nat.mul_le_mul_left 2 ih
              _ ≥ n + 1 + 1 := by omega

        -- For large enough k, both conditions hold
        set M := max (N + 4) (Nat.ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ) + 2) with hM_def

        have hk_exists : ∃ k₀, ∀ k ≥ k₀, p_min ^ (2 ^ k) - 2 ≥ N ∧
            (1 : ℝ) / (p_min ^ (2 ^ k) - 1) < δ / (4 * (c_prime E 2 Nat.prime_two + 1)) := by
          -- Use k₀ = M since p_min^{2^k} ≥ 3^{2^k} ≥ 2^{2^k} ≥ 2^k ≥ k for k ≥ k₀
          use M
          intro k hk
          have hk_ge_N4 : k ≥ N + 4 := le_trans (le_max_left _ _) hk
          have hk_ge_ceil : k ≥ Nat.ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ) + 2 :=
            le_trans (le_max_right _ _) hk

          have h_pmin_ge : p_min ^ (2 ^ k) ≥ 3 ^ (2 ^ k) := Nat.pow_le_pow_left hp_min_ge_3 _
          have h_3_ge_2 : 3 ^ (2 ^ k) ≥ 2 ^ (2 ^ k) := Nat.pow_le_pow_left (by norm_num) _
          have h_2k_ge_k1 : 2 ^ k ≥ k + 1 := h2k_bound k
          have h_k_le_2pk : k ≤ 2 ^ k := Nat.le_of_succ_le h_2k_ge_k1
          have h_2pow_ge : 2 ^ (2 ^ k) ≥ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h_k_le_2pk

          -- n = p_min^{2^k} ≥ 3^{2^k} ≥ 2^{2^k} ≥ 2^k ≥ k + 1 ≥ N + 5
          have hn_ge : p_min ^ (2 ^ k) ≥ k + 1 := by
            calc p_min ^ (2 ^ k) ≥ 3 ^ (2 ^ k) := h_pmin_ge
              _ ≥ 2 ^ (2 ^ k) := h_3_ge_2
              _ ≥ 2 ^ k := h_2pow_ge
              _ ≥ k + 1 := h_2k_ge_k1

          constructor
          · -- n - 2 ≥ N
            have h1 : p_min ^ (2 ^ k) ≥ N + 5 := by
              calc p_min ^ (2 ^ k) ≥ k + 1 := hn_ge
                _ ≥ N + 4 + 1 := by omega
                _ = N + 5 := by ring
            omega
          · -- 1/(n-1) < δ/(4(c_2+1))
            have hn_large : (p_min ^ (2 ^ k) : ℝ) - 1 > 4 * (c_prime E 2 Nat.prime_two + 1) / δ := by
              have h1 : (p_min ^ (2 ^ k) : ℝ) ≥ k + 1 := by exact_mod_cast hn_ge
              have hk_real : (k : ℝ) ≥ Nat.ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ) + 2 := by
                exact_mod_cast hk_ge_ceil
              have hceil := Nat.le_ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ)
              have h3 : (Nat.ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ) : ℝ) + 1 ≥
                  4 * (c_prime E 2 Nat.prime_two + 1) / δ := by linarith
              have h2 : (k : ℝ) + 1 > (Nat.ceil (4 * (c_prime E 2 Nat.prime_two + 1) / δ) : ℝ) + 1 := by
                linarith
              linarith
            have h_bound_pos : (0 : ℝ) < 4 * (c_prime E 2 Nat.prime_two + 1) / δ := by positivity
            calc (1 : ℝ) / (p_min ^ (2 ^ k) - 1)
                < 1 / (4 * (c_prime E 2 Nat.prime_two + 1) / δ) :=
                  one_div_lt_one_div_of_lt h_bound_pos hn_large
              _ = δ / (4 * (c_prime E 2 Nat.prime_two + 1)) := by field_simp
        obtain ⟨k₀, hk_cond⟩ := hk_exists

        -- Pick k = max(k₀, 2)
        set k := max k₀ 2 with hk_def
        have hk_ge_k0 : k ≥ k₀ := le_max_left _ _
        have hk_ge_2 : k ≥ 2 := le_max_right _ _
        have hk_ge_1 : k ≥ 1 := by omega
        obtain ⟨hN_le, hcorr_bound⟩ := hk_cond k hk_ge_k0
        have hord2 := hord2_growth k hk_ge_1

        -- n = p_min^{2^k}
        set n := p_min ^ (2 ^ k) with hn_def
        have hn_pos : 0 < n := Nat.pow_pos hp_min.pos
        have hn_ge_2 : 2 ≤ n := by
          calc n = p_min ^ (2 ^ k) := rfl
            _ ≥ p_min ^ 1 := Nat.pow_le_pow_right hp_min.pos (@Nat.one_le_two_pow k)
            _ = p_min := pow_one _
            _ ≥ 3 := hp_min_ge_3
            _ ≥ 2 := by norm_num
        have hn1_pos : 0 < n - 1 := by omega
        have hn1_ne : n - 1 ≠ 0 := by omega
        have hn_gt_1 : 1 < n := by omega

        -- Factor n - 1 = 2^a · b where b is odd
        obtain ⟨a, b, hb_odd, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1_ne 2 (by norm_num)
        have hb_pos : 0 < b := by
          by_contra hb_zero
          push_neg at hb_zero
          interval_cases b; simp_all
        have hb_ne : b ≠ 0 := by omega
        have ha_ge : k + 1 ≤ a := by
          have h2a_ne : 2 ^ a ≠ 0 := ne_of_gt (Nat.pow_pos (by norm_num : 0 < 2))
          have hfact_eq : (n - 1).factorization 2 = a := by
            calc (n - 1).factorization 2 = (2 ^ a * b).factorization 2 := by rw [hab]
              _ = (2 ^ a).factorization 2 + b.factorization 2 := by rw [Nat.factorization_mul h2a_ne hb_ne]; rfl
              _ = a + 0 := by
                have h1 : (2 ^ a).factorization 2 = a := by
                  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
                    Nat.Prime.factorization_self Nat.prime_two, mul_one]
                have h2 : b.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hb_odd
                rw [h1, h2]
              _ = a := by ring
          rw [← hfact_eq]; exact hord2

        -- Since p_min achieves minimum, c_{p_min} ≤ c_q for all primes q
        have hb_is_odd : Odd b := (Nat.even_or_odd b).resolve_left (fun h => hb_odd (Even.two_dvd h))
        have hb_bound : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ b → Odd q → c_prime E p_min hp_min ≤ c_prime E q hq :=
          fun q hq _ _ => h_min q hq
        have hFb_bound := F_odd_lower_bound E hb_pos hb_is_odd (c_prime E p_min hp_min) hb_bound

        -- Key facts for calculation
        have hc2_eq : c_prime E 2 Nat.prime_two * Real.log 2 = 1 := by rw [c_prime_two E]; field_simp
        have hc2_pos : 0 < c_prime E 2 Nat.prime_two := by rw [c_prime_two E]; positivity
        have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
        have hn1_real_pos : (0 : ℝ) < n - 1 := by have h : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn_gt_1; linarith
        have hb_real_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb_pos
        have ha_pos : 0 < a := by linarith [ha_ge, hk_ge_1]
        have ha_ge_3 : 3 ≤ a := by omega

        -- F formulas
        have hFn := faddeev_F_pow E hp_min.pos (2 ^ k)
        have hFn1 := F_two_pow_mul E a hb_pos
        have hFp_eq : F E p_min hp_min.pos = c_prime E p_min hp_min * Real.log p_min := by
          rw [c_prime]; have hlog_pos : 0 < Real.log p_min := Real.log_pos (Nat.one_lt_cast.mpr hp_min.one_lt)
          field_simp

        have hFn_eq : F E n hn_pos = (2 ^ k : ℕ) * c_prime E p_min hp_min * Real.log p_min := by
          calc F E n hn_pos = F E (p_min ^ (2 ^ k)) (by rw [← hn_def]; exact hn_pos) := by congr 1
            _ = (2 ^ k : ℕ) * F E p_min hp_min.pos := hFn
            _ = (2 ^ k : ℕ) * (c_prime E p_min hp_min * Real.log p_min) := by rw [hFp_eq]
            _ = _ := by ring

        have hFn1_eq : F E (n - 1) hn1_pos = a + F E b hb_pos := by
          calc F E (n - 1) hn1_pos = F E (2 ^ a * b) (by rw [← hab]; exact hn1_pos) := by congr 1
            _ = a + F E b hb_pos := hFn1

        -- Log calculations
        have hlog_n : Real.log n = (2 ^ k : ℕ) * Real.log p_min := by
          have hn_eq : (n : ℝ) = (p_min : ℝ) ^ (2 ^ k : ℕ) := by simp only [hn_def, Nat.cast_pow]
          rw [hn_eq, Real.log_pow]

        have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have hn1_ne_real : (n : ℝ) - 1 ≠ 0 := by linarith
        have hn1_eq_2ab : (n : ℝ) - 1 = 2 ^ a * b := by rw [← hn1_cast]; norm_cast

        have h_ratio_pos : 0 < (n : ℝ) / (n - 1) := div_pos hn_real_pos hn1_real_pos
        have h2a_pos : (0 : ℝ) < 2 ^ a := pow_pos (by norm_num) a

        have hlog_nb : Real.log (n / b) = a * Real.log 2 + Real.log (n / (n - 1)) := by
          have hnb_eq : (n : ℝ) / b = 2 ^ a * n / (n - 1) := by
            have h2 : (1 : ℝ) / b = 2 ^ a / (n - 1) := by rw [hn1_eq_2ab]; field_simp
            calc (n : ℝ) / b = n * (1 / b) := by ring
              _ = n * (2 ^ a / (n - 1)) := by rw [h2]
              _ = 2 ^ a * n / (n - 1) := by ring
          rw [hnb_eq, mul_div_assoc, Real.log_mul (ne_of_gt h2a_pos) (ne_of_gt h_ratio_pos), Real.log_pow]

        have hlog_ratio_pos : 0 < Real.log (n / (n - 1)) := by
          have h1 : (n : ℝ) / (n - 1) > 1 := one_lt_div hn1_real_pos |>.mpr (by linarith)
          exact Real.log_pos h1

        -- Upper bound on λ_n
        set_option maxHeartbeats 600000 in
        have hlam_upper : entropyIncrement E n hn_gt_1 ≤ -(a : ℝ) * δ + c_prime E p_min hp_min * Real.log (n / (n - 1)) := by
          have hFb_ge : c_prime E p_min hp_min * Real.log b ≤ F E b hb_pos := hFb_bound
          have h_step1 : (2 ^ k : ℕ) * c_prime E p_min hp_min * Real.log p_min - (↑a + F E b hb_pos)
              ≤ (2 ^ k : ℕ) * c_prime E p_min hp_min * Real.log p_min - (a + c_prime E p_min hp_min * Real.log b) := by
            linarith [hFb_ge]
          have h_step2 : (2 ^ k : ℕ) * c_prime E p_min hp_min * Real.log p_min - (a + c_prime E p_min hp_min * Real.log b)
              = c_prime E p_min hp_min * (Real.log n - Real.log b) - a := by
            rw [hlog_n]
            ring
          have h_step3 : c_prime E p_min hp_min * (Real.log n - Real.log b) - a
              = c_prime E p_min hp_min * Real.log (n / b) - a := by
            rw [Real.log_div (ne_of_gt hn_real_pos) (ne_of_gt hb_real_pos)]
          have h_step4 : c_prime E p_min hp_min * Real.log (n / b) - a
              = c_prime E p_min hp_min * (a * Real.log 2 + Real.log (n / (n - 1))) - a := by rw [hlog_nb]
          have h_step5 : c_prime E p_min hp_min * (a * Real.log 2 + Real.log (n / (n - 1))) - a
              = a * (c_prime E p_min hp_min * Real.log 2 - 1) + c_prime E p_min hp_min * Real.log (n / (n - 1)) := by ring
          have hcpmin_eq : c_prime E p_min hp_min * Real.log 2 - 1 = -δ := by rw [hδ_def]; linarith [hc2_eq]
          have h_step6 : a * (c_prime E p_min hp_min * Real.log 2 - 1) + c_prime E p_min hp_min * Real.log (n / (n - 1))
              = -(a : ℝ) * δ + c_prime E p_min hp_min * Real.log (n / (n - 1)) := by rw [hcpmin_eq]; ring
          calc entropyIncrement E n hn_gt_1 = F E n (by omega) - F E (n - 1) (by omega) := rfl
            _ = F E n hn_pos - F E (n - 1) hn1_pos := by
              have hFn : F E n (by omega : 0 < n) = F E n hn_pos :=
                F_congr (E := E) (hn := (by omega : 0 < n)) (hn' := hn_pos)
              have hFn1 : F E (n - 1) (by omega : 0 < n - 1) = F E (n - 1) hn1_pos :=
                F_congr (E := E) (hn := (by omega : 0 < n - 1)) (hn' := hn1_pos)
              simp
            _ = (2 ^ k : ℕ) * c_prime E p_min hp_min * Real.log p_min - (↑a + F E b hb_pos) := by rw [hFn_eq, hFn1_eq]
            _ ≤ _ := by linarith [h_step1, h_step2, h_step3, h_step4, h_step5, h_step6]

        -- Correction term is small: c_{p_min} · log(n/(n-1)) < δ/4
        have hcorr_small : c_prime E p_min hp_min * Real.log (n / (n - 1)) < δ / 4 := by
          -- log(n/(n-1)) = log(1 + 1/(n-1)) < 1/(n-1)
          have hlog_bound : Real.log (n / (n - 1)) < 1 / (n - 1) := by
            have h1 : (n : ℝ) / (n - 1) = 1 + 1 / (n - 1) := by field_simp [hn1_ne_real]; ring
            rw [h1]
            -- Use: log(1 + x) < x for x > 0, derived from 1 + x < exp(x)
            have hx_pos : (0 : ℝ) < 1 / (n - 1) := by positivity
            have hx_ne : (1 : ℝ) / (n - 1) ≠ 0 := ne_of_gt hx_pos
            have h_exp := Real.add_one_lt_exp hx_ne
            -- h_exp has form: x + 1 < exp(x), need: 1 + x < exp(x)
            have h_exp' : 1 + 1 / ((n : ℝ) - 1) < Real.exp (1 / (n - 1)) := by linarith
            have h_1x_pos : (0 : ℝ) < 1 + 1 / (n - 1) := by linarith
            calc Real.log (1 + 1 / (n - 1))
                < Real.log (Real.exp (1 / (n - 1))) := Real.log_lt_log h_1x_pos h_exp'
              _ = 1 / (n - 1) := Real.log_exp _
          -- c_{p_min} < c_2, so c_{p_min} · log(...) < c_2 · 1/(n-1) < c_2 · δ/(4(c_2+1)) < δ/4
          have hcpmin_lt : c_prime E p_min hp_min < c_prime E 2 Nat.prime_two := h_lt_c2
          -- Handle by cases on sign of c_{p_min}
          by_cases hcpmin_sign : 0 < c_prime E p_min hp_min
          case pos =>
            -- c_{p_min} > 0 case: use the full calc chain
            calc c_prime E p_min hp_min * Real.log (n / (n - 1))
                < c_prime E p_min hp_min * (1 / (n - 1)) := by
                  apply mul_lt_mul_of_pos_left hlog_bound hcpmin_sign
              _ ≤ c_prime E 2 Nat.prime_two * (1 / (n - 1)) := by
                  apply mul_le_mul_of_nonneg_right (le_of_lt hcpmin_lt); positivity
              _ < c_prime E 2 Nat.prime_two * (δ / (4 * (c_prime E 2 Nat.prime_two + 1))) := by
                  -- hcorr_bound : 1 / ((↑p_min)^(2^k) - 1) < δ / (4 * (c_2 + 1)) (Real subtraction)
                  -- n = p_min ^ (2 ^ k), so (n : ℝ) - 1 = (↑p_min)^(2^k) - 1
                  have hn_cast_eq : (n : ℝ) = (p_min : ℝ) ^ (2 ^ k) := by
                    simp only [hn_def, Nat.cast_pow]
                  have hcorr' : (1 : ℝ) / (n - 1) < δ / (4 * (c_prime E 2 Nat.prime_two + 1)) := by
                    calc (1 : ℝ) / (n - 1) = 1 / ((p_min : ℝ) ^ (2 ^ k) - 1) := by rw [hn_cast_eq]
                      _ < δ / (4 * (c_prime E 2 Nat.prime_two + 1)) := hcorr_bound
                  apply mul_lt_mul_of_pos_left hcorr' hc2_pos
              _ = c_prime E 2 Nat.prime_two * δ / (4 * (c_prime E 2 Nat.prime_two + 1)) := by ring
              _ < δ / 4 := by
                  have hc2p1_pos : (0 : ℝ) < c_prime E 2 Nat.prime_two + 1 := by linarith
                  have h1 : c_prime E 2 Nat.prime_two < c_prime E 2 Nat.prime_two + 1 := by linarith
                  have h2 : c_prime E 2 Nat.prime_two / (c_prime E 2 Nat.prime_two + 1) < 1 :=
                    (div_lt_one hc2p1_pos).mpr h1
                  calc c_prime E 2 Nat.prime_two * δ / (4 * (c_prime E 2 Nat.prime_two + 1))
                      = δ / 4 * (c_prime E 2 Nat.prime_two / (c_prime E 2 Nat.prime_two + 1)) := by
                        field_simp
                    _ < δ / 4 * 1 := by apply mul_lt_mul_of_pos_left h2; positivity
                    _ = δ / 4 := by ring
          case neg =>
            -- c_{p_min} ≤ 0 case: product is nonpositive, δ/4 is positive
            push_neg at hcpmin_sign
            have h1 : c_prime E p_min hp_min * Real.log (n / (n - 1)) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hcpmin_sign (le_of_lt hlog_ratio_pos)
            have h2 : (0 : ℝ) < δ / 4 := by positivity
            linarith

        -- λ_n < -δ/2
        have hlam_neg : entropyIncrement E n hn_gt_1 < -δ / 2 := by
          have ha_ge_3_real : (3 : ℝ) ≤ a := by exact_mod_cast ha_ge_3
          calc entropyIncrement E n hn_gt_1
              ≤ -(a : ℝ) * δ + c_prime E p_min hp_min * Real.log (n / (n - 1)) := hlam_upper
            _ < -(a : ℝ) * δ + δ / 4 := by linarith [hcorr_small]
            _ ≤ -3 * δ + δ / 4 := by nlinarith
            _ = -(11 : ℝ) / 4 * δ := by ring
            _ < -δ / 2 := by linarith

        -- But |λ_n| < δ/2 from hN, so λ_n > -δ/2. Contradiction!
        have hlam_bound := hN (n - 2) hN_le
        simp only [Nat.sub_add_cancel (by omega : 2 ≤ n)] at hlam_bound
        rw [Real.dist_eq, sub_zero] at hlam_bound
        have hlam_bound' : entropyIncrement E n hn_gt_1 > -δ / 2 := by
          have h1 : |entropyIncrement E n hn_gt_1| < δ / 2 := hlam_bound
          have h2 := (abs_lt.mp h1).1
          -- h2 : -(δ / 2) < entropyIncrement, need: entropyIncrement > -δ / 2
          linarith
        linarith
      rw [← h_eq]
      exact h1


  -- Step 5: Conclude c_p = c_2 for all primes
  intro p q hp hq
  have hp_eq_c2 : c_prime E p hp = c_prime E 2 Nat.prime_two :=
    le_antisymm (h_all_le_c2 p hp) (h_all_ge_c2 p hp)
  have hq_eq_c2 : c_prime E q hq = c_prime E 2 Nat.prime_two :=
    le_antisymm (h_all_le_c2 q hq) (h_all_ge_c2 q hq)
  rw [hp_eq_c2, hq_eq_c2]

/-- **Faddeev's Lemma 8'**: The set {c_p | p prime} has a minimum.

    Note: This follows directly from Lemma 9 (all c_p equal). -/
theorem faddeev_c_prime_has_min (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E p hp ≤ c_prime E q hq := by
  -- Using Lemma 9, all c_p = c_2, so 2 achieves the minimum
  have h_all_eq := faddeev_c_prime_all_equal E
  exact ⟨2, Nat.prime_two, fun q hq => le_of_eq (h_all_eq 2 q Nat.prime_two hq)⟩

/-! ### Deriving F(n) = log₂(n) from Lemmas 8-9 -/

/-- **KEY RESULT**: F(n) = log₂(n) for all n ≥ 1.

    Proof: By Lemma 9, all c_p = c_2 = 1/log(2).
    By the prime factorization theorem, F(n) = c_2 · log(n) = log(n)/log(2) = log₂(n).

    This breaks the circular dependency: we derive F = log₂ WITHOUT using monotonicity! -/
theorem faddeev_F_eq_log2 (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    F E n hn = Real.log n / Real.log 2 := by
  have h_all_equal := faddeev_c_prime_all_equal E
  -- Convert to the form needed by F_eq_c2_times_log_of_c_prime_const
  have h_const : ∀ p : ℕ, ∀ hp : Nat.Prime p, c_prime E p hp = c_prime E 2 Nat.prime_two :=
    fun p hp => h_all_equal p 2 hp Nat.prime_two
  have h_F_c2_log := F_eq_c2_times_log_of_c_prime_const E h_const hn
  have h_c2 := c_prime_two E
  rw [h_F_c2_log, h_c2]
  ring

/-- **COROLLARY**: Monotonicity follows trivially!

    Once we have F(n) = log₂(n), monotonicity is immediate since log is monotone.
    This completes the circle-breaking: prove F = log₂ first, THEN get monotonicity. -/
theorem faddeev_F_monotone (E : FaddeevEntropy) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    F E m hm ≤ F E n hn := by
  rw [faddeev_F_eq_log2 E hm, faddeev_F_eq_log2 E hn]
  apply div_le_div_of_nonneg_right
  · have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    exact Real.log_le_log (Nat.cast_pos.mpr hm) this
  · exact le_of_lt log_two_pos

end ContinuityProof

/-! ## The Error Function and Convergence Properties

The error function Err(n) = F(n) - log₂(n) measures deviation from Shannon entropy.
The key result `faddeev_F_eq_log2` (proven via Lemma 9) shows Err ≡ 0.

This section contains supporting infrastructure for analyzing convergence. -/

section Sandwich

/-! ### Direct Proof of F = log₂ Using Convergence

The key insight: we can prove F(n) = log₂(n) directly from the convergence results
without needing monotonicity. Then non-negativity follows trivially.

**Mathematical Argument:**
1. Define Err(n) = F(n) - log₂(n) as the "deviation from Shannon entropy".
2. By multiplicativity: Err(n) = Σ_{p|n} v_p(n) · ε_p where ε_p = F(p) - log₂(p).
3. We know ε_2 = 0 (since F(2) = 1 = log₂(2)).
4. From λ_n → 0 and log₂(n/(n-1)) → 0, we get Err(n) - Err(n-1) → 0.
5. For the sequence n = p^k (prime power):
   - λ_{p^k} = F(p^k) - F(p^k - 1) = k·F(p) - F(p^k - 1)
   - For this to go to 0, the growth of k·ε_p must be compensated by F(p^k - 1)
6. The only consistent solution across all primes is ε_p = 0 for all p.
7. Therefore F(n) = log₂(n) ≥ 0.

This avoids the circularity of needing monotonicity for the sandwich argument. -/

/-- The error function: deviation of F from log₂. -/
noncomputable def Err (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  F E n hn - Real.log n / Real.log 2

/-- `Err` does not depend on the proof argument `hn : 0 < n`. -/
theorem Err_congr (E : FaddeevEntropy) {n : ℕ} (hn hn' : 0 < n) :
    Err E n hn = Err E n hn' := by
  unfold Err
  rw [F_congr (E := E) (hn := hn) (hn' := hn')]

/-- Error at powers of 2 is zero. -/
theorem Err_pow2_eq_zero (E : FaddeevEntropy) (k : ℕ) :
    Err E (2 ^ k) (by positivity : 0 < 2 ^ k) = 0 := by
  unfold Err F
  have hF2k := faddeev_F_pow2 E k
  simp only at hF2k
  have hlog : Real.log (2 ^ k : ℕ) / Real.log 2 = k := by
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    calc Real.log ((2 : ℕ) ^ k : ℕ) / Real.log 2
        = Real.log ((2 : ℝ) ^ k) / Real.log 2 := by norm_cast
      _ = (k : ℝ) * Real.log 2 / Real.log 2 := by rw [Real.log_pow]
      _ = k := by field_simp [hlog2_pos.ne']
  linarith [hF2k, hlog]

/-- Consequence of λ_n → 0: the error changes vanishingly.
    Since λ_n = F(n) - F(n-1) → 0 and log₂(n/(n-1)) → 0, we have
    Err(n) - Err(n-1) = [F(n) - F(n-1)] - [log₂(n) - log₂(n-1)] → 0. -/
theorem Err_diff_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => Err E (n + 2) (by omega) - Err E (n + 1) (by omega))
      Filter.atTop (nhds 0) := by
  have hlam := faddeev_lambda_tendsto_zero E
  -- Step 1: Show log₂((n+2)/(n+1)) → 0
  have hlog_ratio : Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    use Nat.ceil (1/δ)
    intro n hn
    simp only [Real.dist_eq]
    have hn1_pos : (0 : ℝ) < ((n : ℕ) : ℝ) + 1 := by positivity
    have h_eq : ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = 1 / (((n : ℕ) : ℝ) + 1) := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      field_simp [hn1_pos.ne']
      ring
    rw [h_eq, abs_of_pos (by positivity : (0 : ℝ) < 1 / (((n : ℕ) : ℝ) + 1))]
    -- Key: n ≥ ⌈1/δ⌉ ≥ 1/δ, so n + 1 > 1/δ, thus 1/(n+1) < δ
    have hceil_le : (1/δ : ℝ) ≤ ⌈1/δ⌉₊ := Nat.le_ceil (1/δ)
    have hn_ge : ((n : ℕ) : ℝ) ≥ ⌈1/δ⌉₊ := Nat.cast_le.mpr hn
    have h_n1_gt : ((n : ℕ) : ℝ) + 1 > 1/δ := by linarith
    rw [div_lt_iff₀ hn1_pos]
    calc (1 : ℝ) = δ * (1/δ) := by field_simp
      _ < δ * (((n : ℕ) : ℝ) + 1) := by nlinarith
  have hlog_zero : Filter.Tendsto
      (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
    have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have htend : Filter.Tendsto Real.log (nhds 1) (nhds (Real.log 1)) := hcont.tendsto
    rw [Real.log_one] at htend
    exact htend.comp hlog_ratio
  -- Step 2: Convert log(ratio) to log difference / log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog_diff : Filter.Tendsto
      (fun n : ℕ => Real.log ((n + 2 : ℕ) : ℝ) / Real.log 2 - Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2)
      Filter.atTop (nhds 0) := by
    have heq : ∀ n : ℕ,
        Real.log ((n + 2 : ℕ) : ℝ) / Real.log 2 - Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2 =
        Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) / Real.log 2 := by
      intro n
      have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hn2_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      rw [← sub_div]
      congr 1
      exact (Real.log_div hn2_pos.ne' hn1_pos.ne').symm
    simp_rw [heq]
    have h0 : (0 : ℝ) / Real.log 2 = 0 := zero_div _
    rw [← h0]
    exact hlog_zero.div_const (Real.log 2)
  -- Step 3: Combine λ_n → 0 and log diff → 0
  rw [Metric.tendsto_atTop] at hlam hlog_diff ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hlog_diff (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hlam (ε / 2) (by linarith)
  use max N₁ N₂
  intro n hn
  have hn1 : N₁ ≤ n := le_of_max_le_left hn
  have hn2 : N₂ ≤ n := le_of_max_le_right hn
  simp only [Real.dist_eq, sub_zero] at hN₁ hN₂ ⊢
  -- Key identity: Err(n+2) - Err(n+1) = [F(n+2) - F(n+1)] - [log(n+2) - log(n+1)]/log(2)
  have h_err_expand : Err E (n + 2) (by omega) - Err E (n + 1) (by omega) =
      (F E (n + 2) (by omega) - F E (n + 1) (by omega)) -
      (Real.log ((n + 2 : ℕ) : ℝ) / Real.log 2 - Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2) := by
    simp only [Err, F]; ring
  -- F(n+2) - F(n+1) = entropyIncrement(n+2) with matching proof terms
  have h_incr_eq : F E (n + 2) (by omega) - F E (n + 1) (by omega) =
      entropyIncrement E (n + 2) (by omega : 1 < n + 2) := by
    simp [entropyIncrement, F]
  simp only [h_err_expand, h_incr_eq]
  calc |entropyIncrement E (n + 2) (by omega) -
          (Real.log ↑(n + 2) / Real.log 2 - Real.log ↑(n + 1) / Real.log 2)|
      ≤ |entropyIncrement E (n + 2) (by omega)| +
          |Real.log ↑(n + 2) / Real.log 2 - Real.log ↑(n + 1) / Real.log 2| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hN₂ n hn2) (hN₁ n hn1)
    _ = ε := by ring

/-- Helper: 2^(n+1) ≥ n+2 for all n ∈ ℕ -/
private theorem pow2_ge_succ (n : ℕ) : 2 ^ (n + 1) ≥ n + 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    calc 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
      _ ≥ 2 * (m + 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 * m + 4 := by ring
      _ ≥ m + 1 + 2 := by omega

/-- Err at 2^k + 1 converges to 0.
    From Err(n+2) - Err(n+1) → 0 and Err(2^k) = 0, we get Err(2^k + 1) → 0. -/
theorem Err_pow2_succ_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun k : ℕ => Err E (2 ^ k + 1) (by positivity))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdiff := Err_diff_tendsto_zero E
  rw [Metric.tendsto_atTop] at hdiff
  obtain ⟨N, hN⟩ := hdiff ε hε
  use N + 1
  intro k hk
  simp only [Real.dist_eq, sub_zero]
  -- 2^k + 1 > N + 2 for k ≥ N + 1
  have hk_large : 2 ^ k + 1 ≥ N + 2 := by
    have h2k : 2 ^ k ≥ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
    have h2N1 : 2 ^ (N + 1) ≥ N + 2 := pow2_ge_succ N
    omega
  -- Err(2^k + 1) - Err(2^k) is part of the convergent sequence
  -- The sequence is indexed by n where Err(n+2) - Err(n+1)
  -- For 2^k + 1 = (n+2), we need n = 2^k - 1
  -- So we need 2^k - 1 ≥ N, which follows from hk_large
  have hn : N ≤ 2 ^ k - 1 := by omega
  specialize hN (2 ^ k - 1) hn
  simp only [Real.dist_eq, sub_zero] at hN
  -- (2^k - 1) + 2 = 2^k + 1 and (2^k - 1) + 1 = 2^k
  have h_eq1 : 2 ^ k - 1 + 2 = 2 ^ k + 1 := by omega
  have h_eq2 : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  have hErr_2k := Err_pow2_eq_zero E k
  -- Need to show |Err(2^k+1) - Err(2^k)| < ε
  have hgoal : |Err E (2 ^ k + 1) (by positivity) - Err E (2 ^ k) (by positivity)| < ε := by
    have : Err E (2 ^ k - 1 + 2) (by omega) - Err E (2 ^ k - 1 + 1) (by omega) =
           Err E (2 ^ k + 1) (by positivity) - Err E (2 ^ k) (by positivity) := by
      have hpos1 : 0 < 2 ^ k + 1 := by positivity
      have hpos2 : 0 < 2 ^ k := by positivity
      calc
        Err E (2 ^ k - 1 + 2) (by omega) - Err E (2 ^ k - 1 + 1) (by omega)
            = Err E (2 ^ k + 1) (by omega : 0 < 2 ^ k + 1) - Err E (2 ^ k) (by omega : 0 < 2 ^ k) := by
              simp [h_eq1, h_eq2]
        _ = Err E (2 ^ k + 1) hpos1 - Err E (2 ^ k) hpos2 := by
              simp
    rw [← this]
    exact hN
  rw [hErr_2k, sub_zero] at hgoal
  exact hgoal

/-- Helper: 2^(n+2) ≥ n+3 for all n ∈ ℕ -/
private theorem pow2_ge_succ_succ (n : ℕ) : 2 ^ (n + 2) ≥ n + 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    calc 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
      _ ≥ 2 * (m + 3) := Nat.mul_le_mul_left 2 ih
      _ = 2 * m + 6 := by ring
      _ ≥ m + 1 + 3 := by omega

/-- Helper: 0 < 2^(k+1) - 1 for all k ∈ ℕ -/
private theorem pow2_pred_pos (k : ℕ) : 0 < 2 ^ (k + 1) - 1 := by
  have h : 2 ^ (k + 1) ≥ 2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_add_left 1 k)
  omega

/-- Err at 2^k - 1 converges to 0 for k ≥ 1.
    From Err(n+2) - Err(n+1) → 0 and Err(2^k) = 0, we get Err(2^k - 1) → 0. -/
theorem Err_pow2_pred_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun k : ℕ => Err E (2 ^ (k + 1) - 1) (pow2_pred_pos k))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdiff := Err_diff_tendsto_zero E
  rw [Metric.tendsto_atTop] at hdiff
  obtain ⟨N, hN⟩ := hdiff ε hε
  use N + 1
  intro k hk
  simp only [Real.dist_eq, sub_zero]
  -- 2^(k+1) - 1 ≥ N + 2 for k ≥ N + 1
  have h_pow_bound : 2 ^ (k + 1) ≥ 2 ^ (N + 2) :=
    Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : N + 2 ≤ k + 1)
  have h_exp_bound : 2 ^ (N + 2) ≥ N + 3 := pow2_ge_succ_succ N
  have hk_large : 2 ^ (k + 1) - 1 ≥ N + 2 := by omega
  -- Err(2^(k+1)) - Err(2^(k+1) - 1) is part of the convergent sequence
  have hn : N ≤ 2 ^ (k + 1) - 2 := by omega
  specialize hN (2 ^ (k + 1) - 2) hn
  simp only [Real.dist_eq, sub_zero] at hN
  -- (2^(k+1) - 2) + 2 = 2^(k+1) and (2^(k+1) - 2) + 1 = 2^(k+1) - 1
  have hErr_2k1 := Err_pow2_eq_zero E (k + 1)
  -- |Err(2^(k+1)) - Err(2^(k+1) - 1)| < ε means |0 - Err(2^(k+1) - 1)| < ε
  have h_pow_pos : 0 < 2 ^ (k + 1) := by positivity
  have h_pred_pos : 0 < 2 ^ (k + 1) - 1 := pow2_pred_pos k
  -- The Err function only depends on n, not the proof
  -- hN has type: |Err E (2^(k+1)-2+2) _ - Err E (2^(k+1)-2+1) _| < ε
  -- which equals |Err E (2^(k+1)) _ - Err E (2^(k+1)-1) _| < ε
  -- Using hErr_2k1, this becomes |Err E (2^(k+1)-1) _| < ε
  have h_eq1 : 2 ^ (k + 1) - 2 + 2 = 2 ^ (k + 1) := by omega
  have h_eq2 : 2 ^ (k + 1) - 2 + 1 = 2 ^ (k + 1) - 1 := by omega
  -- Show positivity for the intermediate terms
  have h_mid_pos_1 : 0 < 2 ^ (k + 1) - 2 + 2 := by omega
  have h_mid_pos_2 : 0 < 2 ^ (k + 1) - 2 + 1 := by omega
  -- Rewrite the absolute value using the numeric equalities
  calc |Err E (2 ^ (k + 1) - 1) h_pred_pos|
      = |0 - Err E (2 ^ (k + 1) - 1) h_pred_pos| := by rw [zero_sub, abs_neg]
    _ = |Err E (2 ^ (k + 1)) h_pow_pos - Err E (2 ^ (k + 1) - 1) h_pred_pos| := by
        rw [hErr_2k1]
    _ = |Err E (2 ^ (k + 1) - 2 + 2) h_mid_pos_1 - Err E (2 ^ (k + 1) - 2 + 1) h_mid_pos_2| := by
        simp only [h_eq1, h_eq2]
    _ < ε := hN

/-- Alias for `faddeev_F_eq_log2`. -/
theorem faddeev_F_eq_log2' (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    E.H (uniformDist n hn) = Real.log n / Real.log 2 :=
  faddeev_F_eq_log2 E hn

/-- **Key uniqueness step**: From F = log₂, we have Err ≡ 0.

    This follows directly from the definition Err(n) = F(n) - log₂(n)
    and the uniqueness theorem faddeev_F_eq_log2'. -/
theorem faddeev_Err_eq_zero (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    Err E n hn = 0 := by
  have hF := faddeev_F_eq_log2' E hn
  simp only [Err, F, hF, sub_self]

/-- F(n) = log₂(n) implies F(n) ≥ 0 for n ≥ 1. -/
theorem faddeev_F_nonneg (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    0 ≤ E.H (uniformDist n hn) := by
  have hF := faddeev_F_eq_log2' E hn
  rw [hF]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply div_nonneg _ (le_of_lt hlog2_pos)
  exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn.ne' : (1 : ℝ) ≤ n)

end Sandwich

/-! ## Full Uniqueness: E.H = shannonEntropyNormalized

This section proves the **full uniqueness theorem**: any Faddeev entropy equals
Shannon entropy on ALL distributions, not just uniform ones.

The strategy (following GPT-5.2 Pro's guidance):
1. Define binary entropy functions ηE and ηSh
2. Prove equality on rationals m/n via the splitting lemma
3. Extend to all of [0,1] via continuity
4. Lift to all ProbVec n by induction using recursivity
-/

section FullUniqueness

/-- The binary entropy function for a Faddeev entropy. -/
noncomputable def ηE (E : FaddeevEntropy) : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun x => E.H (binaryDist x.1 x.2.1 x.2.2)

/-- The binary Shannon entropy function. -/
noncomputable def ηSh : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun x => shannonEntropyNormalized (binaryDist x.1 x.2.1 x.2.2)

/-- ηE is continuous (this is Faddeev's axiom F1). -/
theorem continuous_ηE (E : FaddeevEntropy) : Continuous (ηE E) :=
  E.continuous_binary

/-- ηSh is continuous (from continuity of negMulLog). -/
theorem continuous_ηSh : Continuous ηSh := by
  unfold ηSh shannonEntropyNormalized shannonEntropy binaryDist
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Continuous.div_const
  apply Continuous.add
  · exact continuous_negMulLog.comp (continuous_subtype_val.comp continuous_id)
  · apply continuous_negMulLog.comp
    apply Continuous.sub continuous_const
    exact continuous_subtype_val.comp continuous_id

/-- Key algebraic identity: For m ≤ n with n > 0, the binary entropy at m/n can be
    computed from F(n), F(m), F(n-m) via the splitting lemma.

    η(m/n) = F(n) - (m/n)·F(m) - ((n-m)/n)·F(n-m)

    Since F(k) = log₂(k), this equals the Shannon binary entropy. -/
theorem ηE_rat_eq_ηSh (E : FaddeevEntropy) (m n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    ηE E ⟨(m : ℝ) / n, by
      constructor
      · exact div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      · exact div_le_one_of_le₀ (by exact_mod_cast hm) (Nat.cast_nonneg n)⟩ =
    ηSh ⟨(m : ℝ) / n, by
      constructor
      · exact div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      · exact div_le_one_of_le₀ (by exact_mod_cast hm) (Nat.cast_nonneg n)⟩ := by
  -- The proof uses the splitting lemma to relate binary entropy to F values
  -- For m = 0 or m = n, both sides are 0
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · -- m = 0: η(0) = 0 on both sides
    simp only [Nat.cast_zero, zero_div]
    unfold ηE ηSh
    -- binaryDist 0 = (0, 1) is a point mass, so entropy = 0
    have hE : E.H (binaryDist 0 (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)) = 0 :=
      binaryEntropy_at_zero E
    have hSh : shannonEntropyNormalized (binaryDist 0 (by norm_num) (by norm_num)) = 0 := by
      unfold shannonEntropyNormalized shannonEntropy binaryDist
      simp [negMulLog]
    rw [hE, hSh]
  · rcases eq_or_lt_of_le hm with rfl | hm_lt
    · -- m = n: η(1) = 0 on both sides
      -- After rfl, m = n, so we use hm_pos : 0 < m (which is now 0 < n)
      have h_ne_zero : (m : ℝ) ≠ 0 := by
        have : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
        exact Nat.cast_ne_zero.mpr this
      simp only [div_self h_ne_zero]
      unfold ηE ηSh
      -- binaryDist 1 = (1, 0) is a point mass, so entropy = 0
      have hE : E.H (binaryDist 1 (by norm_num) (by norm_num)) = 0 := faddeev_H_one_zero E
      have hSh : shannonEntropyNormalized (binaryDist 1 (by norm_num) (by norm_num)) = 0 := by
        unfold shannonEntropyNormalized shannonEntropy binaryDist
        simp [negMulLog]
      rw [hE, hSh]
    · -- 0 < m < n: Algebraic proof using binary entropy formula
      unfold ηE ηSh
      -- First, establish explicit proof terms for the bounds
      have hp0 : 0 ≤ (m : ℝ) / n := div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      have hp1 : (m : ℝ) / n ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast le_of_lt hm_lt) (Nat.cast_nonneg n)

      -- We need to use Nat.cast_sub to reconcile ↑(n-m) vs ↑n - ↑m
      have hcast : (↑(n - m) : ℝ) = ↑n - ↑m := Nat.cast_sub (le_of_lt hm_lt)

      -- Apply the binary entropy formula to the LHS
      have hE_raw : E.H (binaryDist ((m : ℝ) / n) hp0 hp1) =
          F E n hn - (m / n) * F E m hm_pos - ((n - m) / n) * F E (n - m) (Nat.sub_pos_of_lt hm_lt) :=
        faddeev_binary_entropy_formula E m n hm_pos hn hm_lt

      -- Substitute F(k) = log(k)/log(2) using faddeev_F_eq_log2
      have hE : E.H (binaryDist ((m : ℝ) / n) hp0 hp1) =
          (Real.log n - (m / n) * Real.log m - ((n - m) / n) * Real.log (↑n - ↑m)) / Real.log 2 := by
        rw [hE_raw, faddeev_F_eq_log2 E hn, faddeev_F_eq_log2 E hm_pos,
            faddeev_F_eq_log2 E (Nat.sub_pos_of_lt hm_lt), hcast]
        field_simp

      -- Now expand the Shannon side
      have hSh : shannonEntropyNormalized (binaryDist ((m : ℝ) / n) hp0 hp1) =
          (Real.log n - (m / n) * Real.log m - ((n - m) / n) * Real.log (↑n - ↑m)) / Real.log 2 := by
        unfold shannonEntropyNormalized shannonEntropy binaryDist
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        -- Shannon entropy is negMulLog(p) + negMulLog(1-p)
        have h_nm_div : 1 - (m : ℝ) / n = ((n : ℝ) - m) / n := by field_simp
        rw [h_nm_div]
        -- Expand negMulLog
        unfold negMulLog
        -- Use Real.log_div for both terms
        have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
        have hn_pos_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
        have hnm_pos : 0 < (n : ℝ) - m := sub_pos.mpr (Nat.cast_lt.mpr hm_lt)
        -- Goal: [-(m/n)·log(m/n) - ((n-m)/n)·log((n-m)/n)] / log(2)
        --     = [log n - (m/n)·log m - ((n-m)/n)·log(n-m)] / log(2)
        congr 1
        rw [Real.log_div (ne_of_gt hm_pos_real) (ne_of_gt hn_pos_real),
            Real.log_div (ne_of_gt hnm_pos) (ne_of_gt hn_pos_real)]
        -- Now it's pure algebra
        field_simp
        ring

      -- Now hE and hSh both equal the same expression
      rw [hE, hSh]
/-- The set of rationals m/n with 0 < n and m ≤ n is dense in [0,1]. -/
theorem rat_dense_in_Icc : Dense {x : Set.Icc (0 : ℝ) 1 | ∃ m n : ℕ, 0 < n ∧ m ≤ n ∧ x.1 = m / n} := by
  -- For any x ∈ [0,1] and ε > 0, find rational m/n within ε
  rw [Metric.dense_iff]
  intro x ε hε
  -- Choose n large enough that 1/n < ε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have h1_div_ε_pos : 0 < 1 / ε := by positivity
  have hn_pos : 0 < n := by
    have h1 : (n : ℝ) > 1 / ε := by exact_mod_cast hn
    have h2 : (n : ℝ) > 0 := lt_trans h1_div_ε_pos h1
    exact Nat.cast_pos.mp h2
  have hn_real_pos : (0 : ℝ) < n := by positivity
  -- Let m = ⌊x * n⌋
  let m := Nat.floor (x.1 * n)
  have hm_le : m ≤ n := by
    have hxn_le : x.1 * n ≤ n := by nlinarith [x.2.2]
    exact Nat.floor_le_of_le hxn_le
  -- Construct the rational point
  have h_nonneg : 0 ≤ (m : ℝ) / n := div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have h_le_one : (m : ℝ) / n ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hm_le) (Nat.cast_nonneg n)
  let y : Set.Icc (0 : ℝ) 1 := ⟨(m : ℝ) / n, h_nonneg, h_le_one⟩
  -- Show y is in the set of rationals
  have hy_rat : y ∈ {x : Set.Icc (0 : ℝ) 1 | ∃ m n : ℕ, 0 < n ∧ m ≤ n ∧ x.1 = m / n} := by
    simp only [Set.mem_setOf_eq, y]
    exact ⟨m, n, hn_pos, hm_le, rfl⟩
  -- Show y is close to x
  have hy_close : dist y x < ε := by
    rw [Subtype.dist_eq]
    simp only [y]
    have hfloor : (m : ℝ) ≤ x.1 * n := Nat.floor_le (by nlinarith [x.2.1] : 0 ≤ x.1 * n)
    have hfloor_lt : x.1 * n < m + 1 := Nat.lt_floor_add_one (x.1 * n)
    have h1 : |((m : ℝ) / n) - x.1| ≤ 1 / n := by
      have h_lower : (m : ℝ) / n ≤ x.1 := by
        have : (m : ℝ) / n * n ≤ x.1 * n := by
          rw [div_mul_cancel₀]
          · exact hfloor
          · exact ne_of_gt hn_real_pos
        calc (m : ℝ) / n = (m : ℝ) / n * n / n := by field_simp
          _ ≤ x.1 * n / n := by apply div_le_div_of_nonneg_right this; positivity
          _ = x.1 := by field_simp
      have h_upper : x.1 - (m : ℝ) / n ≤ 1 / n := by
        have : x.1 * n - m < 1 := by linarith [hfloor_lt]
        calc x.1 - (m : ℝ) / n = (x.1 * n - m) / n := by field_simp
          _ ≤ 1 / n := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hn_real_pos)
            linarith
      rw [abs_sub_le_iff]
      constructor <;> linarith [h_lower, h_upper]
    have h2 : 1 / (n : ℝ) < ε := by
      have hn_gt : (n : ℝ) > 1 / ε := by exact_mod_cast hn
      calc 1 / (n : ℝ) < 1 / (1 / ε) := by
            apply one_div_lt_one_div_of_lt
            · exact h1_div_ε_pos
            · exact hn_gt
        _ = ε := by field_simp
    calc |((m : ℝ) / n) - x.1| ≤ 1 / n := h1
      _ < ε := h2
  -- Metric.dense_iff expects: ∃ y, y ∈ Metric.ball x ε ∧ y ∈ s
  exact ⟨y, hy_close, hy_rat⟩

/-- Extending equality from rationals to all of [0,1] via continuity.

    Since ηE and ηSh are both continuous and agree on a dense set (rationals),
    they agree everywhere on [0,1]. Uses `Continuous.ext_on` from mathlib. -/
theorem ηE_eq_ηSh (E : FaddeevEntropy) : ηE E = ηSh := by
  -- Apply Continuous.ext_on: continuous functions agreeing on dense set are equal
  apply Continuous.ext_on rat_dense_in_Icc (continuous_ηE E) continuous_ηSh
  -- Show ηE and ηSh agree on rationals
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  obtain ⟨m, n, hn_pos, hm_le, hx_eq⟩ := hx
  -- x.1 = m/n, need to show ηE E x = ηSh x
  -- First rewrite x as the standard rational form
  have h := ηE_rat_eq_ηSh E m n hn_pos hm_le
  simp only [ηE, ηSh]
  -- The key is that x = ⟨m/n, _⟩ and we need to show the binaryDists are equal
  have hx_val : x.1 = (m : ℝ) / n := hx_eq
  -- Both E.H and shannonEntropyNormalized applied to binaryDist x.1 give same as at m/n
  have hbinary_eq : binaryDist x.1 x.2.1 x.2.2 = binaryDist ((m : ℝ) / n)
      (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
      (div_le_one_of_le₀ (by exact_mod_cast hm_le) (Nat.cast_nonneg n)) := by
    apply Subtype.ext; funext i; fin_cases i <;> simp [binaryDist, hx_val]
  simp_rw [hbinary_eq]
  exact h

/-- **THE KEY UNIQUENESS THEOREM**: Every Faddeev entropy equals Shannon entropy
    on ALL distributions.

    Proof by induction on n using recursivity. -/
theorem faddeev_H_eq_shannon (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.H p = shannonEntropyNormalized p := by
  -- Induction on n
  induction n with
  | zero =>
    -- ProbVec 0 is impossible: sum of 0 elements can't equal 1
    exfalso
    have hsum := p.sum_eq_one
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  | succ n ih =>
    cases n with
    | zero =>
      -- n = 1: Only distribution is the point mass [1]
      -- Both E.H and Shannon give 0
      have hp : p = uniformDist 1 (by norm_num) := by
        apply Subtype.ext; funext i; fin_cases i
        have hp1 : p.1 0 = 1 := by
          have hsum := p.sum_eq_one
          rw [Fin.sum_univ_one] at hsum
          exact hsum
        simp [uniformDist, hp1]
      rw [hp]
      rw [faddeev_F_eq_log2' E (by norm_num : 0 < 1)]
      unfold shannonEntropyNormalized shannonEntropy uniformDist
      simp [negMulLog]
    | succ n' =>
      -- n ≥ 2: Use recursivity
      -- Need to handle the case where p.1 0 + p.1 1 > 0
      -- Use permutation to ensure this (since sum = 1, some entry is positive)
      by_cases h : 0 < p.1 0 + p.1 1
      · -- Can apply recursivity directly
        have hrec_E := E.recursivity p h
        -- groupFirstTwo p h : ProbVec (n' + 1)
        -- normalizeBinary ... : ProbVec 2
        have ih_group : E.H (groupFirstTwo p h) =
            shannonEntropyNormalized (groupFirstTwo p h) := ih (groupFirstTwo p h)
        -- For the binary part, use ηE_eq_ηSh
        have h_binary : E.H (normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h) =
            shannonEntropyNormalized (normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h) := by
          -- normalizeBinary gives a binary distribution
          -- Show it equals binaryDist applied to p.1 0 / (p.1 0 + p.1 1)
          have hx : p.1 0 / (p.1 0 + p.1 1) ∈ Set.Icc (0 : ℝ) 1 := by
            constructor
            · exact div_nonneg (p.nonneg 0) (le_of_lt h)
            · apply div_le_one_of_le₀
              linarith [p.nonneg 1]
              exact le_of_lt h
          have hnorm_eq : normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h =
              binaryDist (p.1 0 / (p.1 0 + p.1 1)) (by exact hx.1) (by exact hx.2) := by
            apply Subtype.ext; funext i; fin_cases i
            · -- Index 0: both sides have same first element
              simp only [normalizeBinary, binaryDist]
              rfl
            · -- Index 1: b/(a+b) = 1 - a/(a+b)
              simp only [normalizeBinary, binaryDist]
              have hne : p.1 0 + p.1 1 ≠ 0 := ne_of_gt h
              field_simp [hne]
              ring_nf
          rw [hnorm_eq]
          -- Use ηE_eq_ηSh
          have hη := congr_fun (ηE_eq_ηSh E) ⟨p.1 0 / (p.1 0 + p.1 1), hx⟩
          unfold ηE ηSh at hη
          exact hη
        -- Combine: Use Shannon's recursivity divided by log 2
        rw [hrec_E, ih_group, h_binary]
        unfold shannonEntropyNormalized
        have hrec_Sh := shannonEntropy_recursivity p h
        rw [hrec_Sh]
        ring
      · -- p.1 0 + p.1 1 = 0, so p.1 0 = p.1 1 = 0
        -- Use permutation to bring a positive entry to position 0
        push_neg at h
        have hp0 : p.1 0 = 0 := le_antisymm (by linarith [p.nonneg 1]) (p.nonneg 0)
        have hp1 : p.1 1 = 0 := le_antisymm (by linarith [p.nonneg 0]) (p.nonneg 1)
        -- Find a positive index (exists since sum = 1)
        have hpos : ∃ i, 0 < p.1 i := by
          by_contra h_all_zero
          push_neg at h_all_zero
          have hsum := p.sum_eq_one
          have : ∑ i, p.1 i ≤ 0 := Finset.sum_nonpos (fun i _ => h_all_zero i)
          linarith
        obtain ⟨i, hi⟩ := hpos
        -- Use symmetry to permute i to position 0
        let σ := Equiv.swap (0 : Fin (n' + 2)) i
        have hperm_E : E.H p = E.H (permute σ p) := (E.symmetry p σ).symm
        have hperm_Sh : shannonEntropyNormalized p = shannonEntropyNormalized (permute σ p) := by
          unfold shannonEntropyNormalized
          rw [shannonEntropy_permute]
        rw [hperm_E, hperm_Sh]
        -- Now (permute σ p).1 0 = p.1 i > 0
        have h' : 0 < (permute σ p).1 0 + (permute σ p).1 1 := by
          have hperm0 : (permute σ p).1 0 = p.1 i := by
            simp only [permute_apply, σ]
            simp [Equiv.swap_inv, Equiv.swap_apply_left]
          linarith [(permute σ p).nonneg 1]
        -- Apply recursivity to permute σ p
        have hrec_E := E.recursivity (permute σ p) h'
        have ih_group : E.H (groupFirstTwo (permute σ p) h') =
            shannonEntropyNormalized (groupFirstTwo (permute σ p) h') := ih _
        have h_binary : E.H (normalizeBinary ((permute σ p).1 0) ((permute σ p).1 1)
            ((permute σ p).nonneg 0) ((permute σ p).nonneg 1) h') =
            shannonEntropyNormalized (normalizeBinary ((permute σ p).1 0) ((permute σ p).1 1)
            ((permute σ p).nonneg 0) ((permute σ p).nonneg 1) h') := by
          have hx : (permute σ p).1 0 / ((permute σ p).1 0 + (permute σ p).1 1) ∈ Set.Icc (0 : ℝ) 1 := by
            constructor
            · exact div_nonneg ((permute σ p).nonneg 0) (le_of_lt h')
            · apply div_le_one_of_le₀
              linarith [(permute σ p).nonneg 1]
              exact le_of_lt h'
          have hnorm_eq : normalizeBinary ((permute σ p).1 0) ((permute σ p).1 1)
              ((permute σ p).nonneg 0) ((permute σ p).nonneg 1) h' =
              binaryDist ((permute σ p).1 0 / ((permute σ p).1 0 + (permute σ p).1 1))
                (by exact hx.1) (by exact hx.2) := by
            apply Subtype.ext; funext j; fin_cases j
            · -- Index 0: both sides have same first element
              simp only [normalizeBinary, binaryDist]
              rfl
            · -- Index 1: b/(a+b) = 1 - a/(a+b)
              simp only [normalizeBinary, binaryDist]
              have hne : (permute σ p).1 0 + (permute σ p).1 1 ≠ 0 := ne_of_gt h'
              field_simp [hne]
              ring_nf
          rw [hnorm_eq]
          have hη := congr_fun (ηE_eq_ηSh E)
            ⟨(permute σ p).1 0 / ((permute σ p).1 0 + (permute σ p).1 1), hx⟩
          unfold ηE ηSh at hη
          exact hη
        -- Combine: Use Shannon's recursivity divided by log 2
        rw [hrec_E, ih_group, h_binary]
        unfold shannonEntropyNormalized
        have hrec_Sh := shannonEntropy_recursivity (permute σ p) h'
        rw [hrec_Sh]
        ring

end FullUniqueness

/-! ## Derived Properties (from Full Uniqueness)

Now that we have `faddeev_H_eq_shannon`, we can derive all the properties that
Shannon-Khinchin explicitly assumes. These are used in Equivalence.lean.

The key theorem `faddeev_H_eq_shannon` shows:
```
∀ (p : ProbVec n), E.H p = shannonEntropyNormalized p
```

With this, all three derived properties become trivial rewrites!
-/

/-- Faddeev entropy is fully continuous (not just binary continuous).

Proof: Rewrite E.H to shannonEntropyNormalized, then use continuity of Shannon entropy. -/
theorem faddeev_full_continuity (E : FaddeevEntropy) : Continuous (E.H (n := n)) := by
  have h : (fun p : ProbVec n => E.H p) = fun p => shannonEntropyNormalized p := by
    funext p
    exact faddeev_H_eq_shannon E p
  simp only [h]
  exact continuous_shannonEntropy.div_const _

/-- Faddeev entropy satisfies maximality: uniform distribution maximizes entropy.

Proof: Rewrite to Shannon entropy and use `shannonEntropy_le_log_card`. -/
theorem faddeev_maximality (E : FaddeevEntropy) (hn : 0 < n) (p : ProbVec n) :
    E.H p ≤ E.H (uniformDist n hn) := by
  rw [faddeev_H_eq_shannon E p, faddeev_H_eq_shannon E (uniformDist n hn)]
  unfold shannonEntropyNormalized
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply div_le_div_of_nonneg_right _ (le_of_lt hlog2_pos)
  rw [shannonEntropy_uniform n hn]
  exact shannonEntropy_le_log_card hn p

/-- Faddeev entropy satisfies expansibility: adding zero probability doesn't change entropy.

Proof: Rewrite to Shannon entropy and use `shannonEntropy_expandZero`. -/
theorem faddeev_expansibility (E : FaddeevEntropy) (p : ProbVec n) :
    E.H (expandZero p) = E.H p := by
  rw [faddeev_H_eq_shannon E (expandZero p), faddeev_H_eq_shannon E p]
  unfold shannonEntropyNormalized
  rw [shannonEntropy_expandZero]

end Mettapedia.InformationTheory
