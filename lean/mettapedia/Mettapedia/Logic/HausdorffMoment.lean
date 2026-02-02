import Mettapedia.Logic.MomentSequences
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Order.Interval.Set.Infinite

/-!
# Hausdorff Moment Problem

This file proves the Hausdorff moment theorem for completely monotone sequences bounded in [0,1].

## Main Results

* `hausdorff_moment_exists`: A completely monotone sequence bounded in [0,1] with m₀ = 1
  is the moment sequence of a probability measure on [0,1].

## References

* Hausdorff, F. (1921). "Summationsmethoden und Momentfolgen"
* Feller, W. (1971). "An Introduction to Probability Theory and Its Applications", Vol. II
* Berg, Christensen & Ressel (1984). "Harmonic Analysis on Semigroups"

-/

namespace Mettapedia.Logic.HausdorffMoment

open MeasureTheory Polynomial Finset BigOperators Filter
open scoped unitInterval Polynomial CompactlySupported

-- Forward-difference definitions and complete monotonicity
open Mettapedia.Logic.MomentSequences

/-! ## Polynomials are determined by their values on `[0,1]` -/

lemma polynomial_eq_of_toContinuousMapOn_eq {p q : ℝ[X]}
    (h : p.toContinuousMapOn I = q.toContinuousMapOn I) : p = q := by
  -- If two polynomials agree on an infinite set, they are equal.
  apply Polynomial.eq_of_infinite_eval_eq
  have hsubset : (Set.Icc (0 : ℝ) 1) ⊆ {x | Polynomial.eval x p = Polynomial.eval x q} := by
    intro x hx
    -- convert x ∈ Icc to an element of the unit interval subtype
    have hx' : (x : ℝ) ∈ (Set.Icc (0 : ℝ) 1) := hx
    have : (⟨x, hx'⟩ : I) ∈ Set.univ := by trivial
    -- use equality of continuous maps on `I`
    have hval : p.toContinuousMapOn I ⟨x, hx'⟩ = q.toContinuousMapOn I ⟨x, hx'⟩ := by
      simp [h]
    -- unfold `toContinuousMapOn`
    simpa using hval
  -- `[0,1]` is infinite
  have hinf : (Set.Icc (0 : ℝ) 1).Infinite := by
    -- `[0,1]` is infinite in a densely ordered linear order
    simpa using (Set.Icc_infinite (a := (0 : ℝ)) (b := (1 : ℝ)) (h := by norm_num))
  exact hinf.mono hsubset

/-! ### Evaluation of finite sums of polynomials -/

lemma eval_fin_sum {n : ℕ} (x : ℝ) (f : Fin n → ℝ[X]) :
    Polynomial.eval x (Finset.sum (Finset.univ : Finset (Fin n)) f) =
      Finset.sum (Finset.univ : Finset (Fin n)) (fun i => Polynomial.eval x (f i)) := by
  classical
  -- Push evaluation through a finite sum by induction on the finset.
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?h0 ?hstep
  · simp
  · intro a s ha hs
    -- `eval` is additive.
    simp [Finset.sum_insert, ha, hs, Polynomial.eval_add]

/-! ## Moment Functional on Polynomials

We define a linear functional Λ on polynomials that maps
`p = Σᵢ aᵢ Xⁱ` to `Σᵢ aᵢ * mᵢ` where `m` is a given moment sequence.
-/

section MomentFunctional

variable (m : ℕ → ℝ)

/-- The moment functional on polynomials: Λ(p) = Σᵢ (coeff p i) * m(i).
    This maps the polynomial Xⁿ to m(n). -/
noncomputable def momentFunctional : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∑ i ∈ p.support, p.coeff i * m i
  map_add' p q := by
    have hsup : (p + q).support ⊆ p.support ∪ q.support := Polynomial.support_add
    have h1 : ∑ i ∈ (p + q).support, (p + q).coeff i * m i =
        ∑ i ∈ p.support ∪ q.support, (p + q).coeff i * m i := by
      apply Finset.sum_subset hsup
      intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, zero_mul]
    have h2 : ∑ i ∈ p.support, p.coeff i * m i =
        ∑ i ∈ p.support ∪ q.support, p.coeff i * m i := by
      apply Finset.sum_subset Finset.subset_union_left
      intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, zero_mul]
    have h3 : ∑ i ∈ q.support, q.coeff i * m i =
        ∑ i ∈ p.support ∪ q.support, q.coeff i * m i := by
      apply Finset.sum_subset Finset.subset_union_right
      intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, zero_mul]
    rw [h1, h2, h3, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Polynomial.coeff_add, add_mul]
  map_smul' r p := by
    simp only [RingHom.id_apply, smul_eq_mul]
    have hsup : (r • p).support ⊆ p.support := Polynomial.support_smul r p
    have h1 : ∑ i ∈ (r • p).support, (r • p).coeff i * m i =
        ∑ i ∈ p.support, (r • p).coeff i * m i := by
      apply Finset.sum_subset hsup
      intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, zero_mul]
    rw [h1]
    simp only [Polynomial.coeff_smul, smul_eq_mul, mul_assoc]
    rw [← Finset.mul_sum]

@[simp]
theorem momentFunctional_X_pow (n : ℕ) : momentFunctional m (X ^ n) = m n := by
  simp only [momentFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  have hne : (1 : ℝ) ≠ 0 := one_ne_zero
  rw [Polynomial.support_X_pow hne, Finset.sum_singleton]
  simp only [Polynomial.coeff_X_pow_self, one_mul]

@[simp]
theorem momentFunctional_C (c : ℝ) : momentFunctional m (C c) = c * m 0 := by
  simp only [momentFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hc : c = 0
  · simp [hc]
  · rw [Polynomial.support_C hc, Finset.sum_singleton, Polynomial.coeff_C_zero]

@[simp]
theorem momentFunctional_one : momentFunctional m 1 = m 0 := by
  have h : (1 : Polynomial ℝ) = C 1 := by simp
  rw [h, momentFunctional_C]
  ring

theorem momentFunctional_monomial (n : ℕ) (c : ℝ) :
    momentFunctional m (monomial n c) = c * m n := by
  simp only [momentFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hc : c = 0
  · simp [hc]
  · rw [Polynomial.support_monomial n hc, Finset.sum_singleton, Polynomial.coeff_monomial_same]

theorem momentFunctional_eq_sum_range (p : Polynomial ℝ) :
    momentFunctional m p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m i := by
  simp only [momentFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_subset
  · intro i hi
    have := Polynomial.le_natDegree_of_mem_supp _ hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
  · intro i _ hi
    rw [Polynomial.notMem_support_iff.mp hi, zero_mul]

/-- The moment functional preserves sums over Finset -/
theorem momentFunctional_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    momentFunctional m (∑ i ∈ s, f i) = ∑ i ∈ s, momentFunctional m (f i) :=
  map_sum (momentFunctional m) f s

end MomentFunctional

/-! ## Bernstein Polynomials and the Moment Functional

The key identity connecting Bernstein polynomials to forward differences.
-/

section BernsteinMoment

variable (m : ℕ → ℝ)

/-- The moment functional applied to x^ν * (1-x)^d equals the d-th forward difference at ν.

    We have: x^ν * (1-x)^d = Σⱼ C(d,j) (-1)^j x^(ν+j)
    Applying moment functional: Σⱼ C(d,j) (-1)^j m(ν+j) = Δ^d m(ν) -/
theorem momentFunctional_X_pow_mul_one_sub_X_pow (ν d : ℕ) :
    momentFunctional m (X ^ ν * (1 - X) ^ d) = fwdDiffIter d m ν := by
  -- Proof by induction on d, using Δ^(d+1) m(ν) = Δ^d m(ν) - Δ^d m(ν+1)
  induction d generalizing ν with
  | zero =>
    simp only [pow_zero, mul_one, fwdDiffIter, Function.iterate_zero, id_eq, pow_zero, one_mul]
    exact momentFunctional_X_pow m ν
  | succ d ih =>
    -- X^ν * (1-X)^(d+1) = X^ν * (1-X)^d - X^(ν+1) * (1-X)^d
    have hexp : X ^ ν * (1 - X : ℝ[X]) ^ (d + 1) =
        X ^ ν * (1 - X) ^ d - X ^ (ν + 1) * (1 - X) ^ d := by
      rw [pow_succ (1 - X : ℝ[X]) d]
      ring
    rw [hexp, map_sub, ih ν, ih (ν + 1), fwdDiffIter_succ]

/-- The moment functional on a Bernstein polynomial equals
    C(n,ν) * Δ^(n-ν) m(ν), where Δ is the forward difference operator.

    This is the KEY LEMMA connecting Bernstein polynomials to complete monotonicity. -/
theorem momentFunctional_bernsteinPolynomial (n ν : ℕ) :
    momentFunctional m (bernsteinPolynomial ℝ n ν) =
      (Nat.choose n ν : ℝ) * fwdDiffIter (n - ν) m ν := by
  unfold bernsteinPolynomial
  -- B_{n,ν}(X) = C(n,ν) * X^ν * (1-X)^(n-ν)
  -- First reassociate: (a * b * c) = a * (b * c)
  have hassoc : ((Nat.choose n ν : ℕ) : ℝ[X]) * X ^ ν * (1 - X) ^ (n - ν) =
      ((Nat.choose n ν : ℕ) : ℝ[X]) * (X ^ ν * (1 - X) ^ (n - ν)) := by ring
  rw [hassoc]
  -- Use that (n : ℝ[X]) = C n and C c * p = c • p
  have hpoly : ((Nat.choose n ν : ℕ) : ℝ[X]) * (X ^ ν * (1 - X) ^ (n - ν)) =
      C (Nat.choose n ν : ℝ) * (X ^ ν * (1 - X) ^ (n - ν)) := by
    rw [← Polynomial.C_eq_natCast]
  rw [hpoly, ← Polynomial.smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul]
  congr 1
  exact momentFunctional_X_pow_mul_one_sub_X_pow m ν (n - ν)

/-- Complete monotonicity implies the moment functional is non-negative on Bernstein polynomials. -/
theorem momentFunctional_bernstein_nonneg (hcm : CompletelyMonotone m)
    (n ν : ℕ) :
    0 ≤ momentFunctional m (bernsteinPolynomial ℝ n ν) := by
  rw [momentFunctional_bernsteinPolynomial m n ν]
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact hcm (n - ν) ν

end BernsteinMoment

/-! ## Positivity on Non-negative Polynomials -/

section Positivity

variable (m : ℕ → ℝ)

/-- The moment functional is non-negative on nonnegative combinations of Bernstein polynomials. -/
theorem momentFunctional_nonneg_of_bernstein_coeffs_nonneg (hcm : CompletelyMonotone m)
    (n : ℕ) (coeffs : Fin (n + 1) → ℝ) (hcoeffs : ∀ k, 0 ≤ coeffs k)
    (p : Polynomial ℝ) (hp : p = ∑ k : Fin (n + 1), coeffs k • bernsteinPolynomial ℝ n k) :
    0 ≤ momentFunctional m p := by
  rw [hp, map_sum]
  apply Finset.sum_nonneg
  intro k _
  simp only [LinearMap.map_smul, smul_eq_mul]
  apply mul_nonneg (hcoeffs k)
  apply momentFunctional_bernstein_nonneg m hcm n k

end Positivity

/-! ## Properties of Bernstein Weights

The Bernstein weights wₙₖ = C(n,k) * Δⁿ⁻ᵏm(k) are non-negative and sum to 1.
-/

section BernsteinWeights

variable (m : ℕ → ℝ)

/-- Bernstein weight: wₙₖ = C(n,k) * Δⁿ⁻ᵏm(k) -/
noncomputable def bernsteinWeight (n k : ℕ) : ℝ :=
  if _h : k ≤ n then (Nat.choose n k : ℝ) * fwdDiffIter (n - k) m k else 0

theorem bernsteinWeight_nonneg (hcm : CompletelyMonotone m) (n k : ℕ) :
    0 ≤ bernsteinWeight m n k := by
  unfold bernsteinWeight
  split_ifs with h
  · apply mul_nonneg (Nat.cast_nonneg _)
    exact hcm (n - k) k
  · rfl

/-- The Bernstein weights sum to m(0). -/
theorem bernsteinWeight_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), bernsteinWeight m n k = momentFunctional m 1 := by
  have hsum := bernsteinPolynomial.sum ℝ n
  have hmf : momentFunctional m (∑ k ∈ Finset.range (n + 1), bernsteinPolynomial ℝ n k) =
      momentFunctional m 1 := by congr 1
  rw [momentFunctional_sum] at hmf
  rw [← hmf]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [momentFunctional_bernsteinPolynomial m n k]
  simp only [bernsteinWeight, hkn, dite_true]

/-- When m(0) = 1, the Bernstein weights sum to 1. -/
theorem bernsteinWeight_sum_eq_one (hzero : m 0 = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), bernsteinWeight m n k = 1 := by
  rw [bernsteinWeight_sum, momentFunctional_one, hzero]

theorem bernsteinWeight_sum_eq_one_fin (hzero : m 0 = 1) (n : ℕ) :
    ∑ k : Fin (n + 1), bernsteinWeight m n k = 1 := by
  -- convert the `Fin` sum to a `range` sum
  simpa [Fin.sum_univ_eq_sum_range] using (bernsteinWeight_sum_eq_one (m := m) hzero n)

end BernsteinWeights

/-! ## Hausdorff Moment Theorem

The main theorem: a completely monotone sequence bounded in [0,1] with m₀ = 1
is the moment sequence of a probability measure on [0,1].
-/

section HausdorffTheorem

/-- The k-th moment of the discrete Bernstein approximation measure.
    μₙ = Σⱼ wₙⱼ δ_{j/n} has k-th moment Σⱼ wₙⱼ (j/n)^k. -/
noncomputable def bernsteinMoment (m : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ j : Fin (n + 1), bernsteinWeight m n j * ((bernstein.z (n := n) j : I) : ℝ) ^ k

/-- The discrete functional induced by Bernstein weights on `C(I, ℝ)`:
    Λₙ(f) = Σⱼ wₙⱼ f(j/n). -/
noncomputable def bernsteinFunctional (m : ℕ → ℝ) (n : ℕ) (f : C(I, ℝ)) : ℝ :=
  ∑ j : Fin (n + 1), bernsteinWeight m n j * f (bernstein.z (n := n) j)

@[simp]
theorem bernsteinFunctional_apply (m : ℕ → ℝ) (n : ℕ) (f : C(I, ℝ)) :
    bernsteinFunctional m n f =
      ∑ j : Fin (n + 1), bernsteinWeight m n j * f (bernstein.z (n := n) j) := rfl

theorem bernsteinFunctional_nonneg (m : ℕ → ℝ) (hcm : CompletelyMonotone m)
    (n : ℕ) (f : C(I, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ bernsteinFunctional m n f := by
  unfold bernsteinFunctional
  refine Finset.sum_nonneg ?_
  intro j _
  have hw : 0 ≤ bernsteinWeight m n j := bernsteinWeight_nonneg m hcm n j
  have hf' : 0 ≤ f (bernstein.z (n := n) j) := hf _
  exact mul_nonneg hw hf'

theorem bernsteinFunctional_bound (m : ℕ → ℝ) (hcm : CompletelyMonotone m)
    (hzero : m 0 = 1) (n : ℕ) (f : C(I, ℝ)) :
    |bernsteinFunctional m n f| ≤ ‖f‖ := by
  -- Use nonnegativity of the weights and their sum to 1.
  unfold bernsteinFunctional
  have hsum : (∑ j : Fin (n + 1), bernsteinWeight m n j) = 1 :=
    bernsteinWeight_sum_eq_one_fin m hzero n
  have hw : ∀ j : Fin (n + 1), 0 ≤ bernsteinWeight m n j :=
    fun j => bernsteinWeight_nonneg m hcm n j
  -- triangle inequality + bound each term by ‖f‖
  calc
    |∑ j : Fin (n + 1), bernsteinWeight m n j * f (bernstein.z (n := n) j)|
        ≤ ∑ j : Fin (n + 1), |bernsteinWeight m n j * f (bernstein.z (n := n) j)| := by
              simpa using (abs_sum_le_sum_abs
                (s := Finset.univ)
                (f := fun j : Fin (n + 1) =>
                  bernsteinWeight m n j * f (bernstein.z (n := n) j)))
    _ = ∑ j : Fin (n + 1), bernsteinWeight m n j * |f (bernstein.z (n := n) j)| := by
          apply Finset.sum_congr rfl
          intro j _
          have hwj : 0 ≤ bernsteinWeight m n j := hw j
          simp [abs_mul, abs_of_nonneg hwj]
    _ ≤ ∑ j : Fin (n + 1), bernsteinWeight m n j * ‖f‖ := by
          refine Finset.sum_le_sum ?_
          intro j _
          have hwj : 0 ≤ bernsteinWeight m n j := hw j
          have hf' : |f (bernstein.z (n := n) j)| ≤ ‖f‖ := by
            simpa using (ContinuousMap.norm_coe_le_norm f (bernstein.z (n := n) j))
          exact mul_le_mul_of_nonneg_left hf' hwj
    _ = ‖f‖ * ∑ j : Fin (n + 1), bernsteinWeight m n j := by
          simp [Finset.mul_sum, mul_comm]
    _ = ‖f‖ := by
          simp [hsum]

/-- The discrete functional agrees with `bernsteinMoment` on monomials. -/
noncomputable def monomialFun (k : ℕ) : C(I, ℝ) :=
  ⟨fun x : I => (x : ℝ) ^ k, by fun_prop⟩

theorem bernsteinFunctional_monomial (m : ℕ → ℝ) (n k : ℕ) :
    bernsteinFunctional m n (monomialFun k) =
      bernsteinMoment m n k := by
  -- `f(x) = x^k` on `I`
  unfold bernsteinFunctional bernsteinMoment
  -- The `pow` is pointwise, so `f (bernstein.z j) = (j/n)^k`.
  simp [monomialFun]

-- NOTE: A more explicit monomial function, if needed:
-- def monomialFun (k : ℕ) : C(I, ℝ) := (ContinuousMap.restrict I (ContinuousMap.id ℝ)) ^ k

-- A polynomial whose momentFunctional matches `bernsteinMoment`.
-- This rewrites the weighted sum into `momentFunctional` of a Bernstein-basis polynomial.
theorem bernsteinMoment_eq_momentFunctional (m : ℕ → ℝ) (n k : ℕ) :
    bernsteinMoment m n k =
      momentFunctional m
        (∑ j : Fin (n + 1),
          bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k)) := by
  classical
  unfold bernsteinMoment
  -- Push `momentFunctional` through the sum and the scalar multiplication.
  have hsum :
      momentFunctional m
          (∑ j : Fin (n + 1),
            bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k))
        = ∑ j : Fin (n + 1),
            momentFunctional m
              (bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k)) := by
    -- `momentFunctional` is linear, so it maps sums to sums.
    simp
  -- Rewrite each summand using Bernstein weights.
  have hterm :
      ∀ j : Fin (n + 1),
        momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k))
          = bernsteinWeight m n j * (((bernstein.z (n := n) j : I) : ℝ) ^ k) := by
    intro j
    have hj' : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    -- Pull out the scalar `((j / n)^k)` using linearity.
    have hsmul :
        momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k)) =
          (((bernstein.z (n := n) j : I) : ℝ) ^ k) * momentFunctional m (bernsteinPolynomial ℝ n j) := by
      -- rewrite multiplication by a constant as scalar multiplication, then use linearity
      set c : ℝ := ((bernstein.z (n := n) j : I) : ℝ) ^ k
      -- keep `c` abstract to avoid `simp` turning product equalities into disjunctions
      have : momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C c) =
          c * momentFunctional m (bernsteinPolynomial ℝ n j) := by
        calc
          momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C c)
              = momentFunctional m (Polynomial.C c * bernsteinPolynomial ℝ n j) := by
                  simp [mul_comm]
          _ = momentFunctional m (c • bernsteinPolynomial ℝ n j) := by
                  simp [Polynomial.smul_eq_C_mul]
          _ = c * momentFunctional m (bernsteinPolynomial ℝ n j) := by
                  simp
      simpa [c] using this
    -- Now expand the Bernstein weight.
    calc
      momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k))
          = (((bernstein.z (n := n) j : I) : ℝ) ^ k) * momentFunctional m (bernsteinPolynomial ℝ n j) := hsmul
      _ = (((bernstein.z (n := n) j : I) : ℝ) ^ k) * ((Nat.choose n (j : ℕ) : ℝ) * fwdDiffIter (n - (j : ℕ)) m (j : ℕ)) := by
            rw [momentFunctional_bernsteinPolynomial m n (j : ℕ)]
      _ = bernsteinWeight m n (j : ℕ) * (((bernstein.z (n := n) j : I) : ℝ) ^ k) := by
            -- unfold the weight and rearrange
            simp [bernsteinWeight, hj', mul_comm, mul_left_comm]
  -- Combine.
  have hcalc :
      momentFunctional m
          (∑ j : Fin (n + 1),
            bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k))
        = ∑ j : Fin (n + 1),
            bernsteinWeight m n j * (((bernstein.z (n := n) j : I) : ℝ) ^ k) := by
    calc
      momentFunctional m
          (∑ j : Fin (n + 1),
            bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k))
          = ∑ j : Fin (n + 1),
              momentFunctional m (bernsteinPolynomial ℝ n j * Polynomial.C (((bernstein.z (n := n) j : I) : ℝ) ^ k)) := by
                exact hsum
      _ = ∑ j : Fin (n + 1),
              bernsteinWeight m n j * (((bernstein.z (n := n) j : I) : ℝ) ^ k) := by
                apply Finset.sum_congr rfl
                intro j _
                exact hterm j
  -- Finish by symmetry.
  exact hcalc.symm

/-- The 0-th Bernstein moment is 1 (for m(0) = 1). -/
theorem bernsteinMoment_zero (m : ℕ → ℝ) (hzero : m 0 = 1) (n : ℕ) :
    bernsteinMoment m n 0 = 1 := by
  simp only [bernsteinMoment, pow_zero, mul_one]
  exact bernsteinWeight_sum_eq_one_fin m hzero n

/-- A power `j ^ k` can be expressed as a linear combination of descending factorials
    using Stirling numbers of the second kind. -/
lemma mul_descFactorial_eq_descFactorial_succ_add (j r : ℕ) :
    j * j.descFactorial r = j.descFactorial (r + 1) + r * j.descFactorial r := by
  by_cases hr : r ≤ j
  · -- In the `r ≤ j` case, use `descFactorial_succ` and `Nat.sub_add_cancel`.
    have hsub : j - r + r = j := Nat.sub_add_cancel hr
    calc
      j * j.descFactorial r = (j - r + r) * j.descFactorial r := by simp [hsub]
      _ = (j - r) * j.descFactorial r + r * j.descFactorial r := by
            simp [Nat.add_mul]
      _ = j.descFactorial (r + 1) + r * j.descFactorial r := by
            simp [Nat.descFactorial_succ]
  · -- If `j < r`, both sides are zero since `descFactorial` vanishes above `j`.
    have hjr : j < r := Nat.lt_of_not_ge hr
    have h0 : j.descFactorial r = 0 := (Nat.descFactorial_eq_zero_iff_lt).2 hjr
    have h0' : j.descFactorial (r + 1) = 0 := (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_succ_of_lt hjr)
    simp [h0, Nat.descFactorial_succ, hjr.le]

theorem pow_eq_sum_stirlingSecond_descFactorial (j k : ℕ) :
    j ^ k = ∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * j.descFactorial r := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Start from `j^(k+1) = j^k * j` and use the induction hypothesis.
      have hmul_desc : ∀ r, j * j.descFactorial r = j.descFactorial (r + 1) + r * j.descFactorial r :=
        fun r => mul_descFactorial_eq_descFactorial_succ_add j r
      calc
        j ^ (k + 1)
            = j ^ k * j := by simp [pow_succ]
        _ = (∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * j.descFactorial r) * j := by
              simp [ih]
        _ = ∑ r ∈ Finset.range (k + 1),
              (Nat.stirlingSecond k r * j.descFactorial r) * j := by
              simp [Finset.sum_mul]
        _ = ∑ r ∈ Finset.range (k + 1),
              Nat.stirlingSecond k r * (j * j.descFactorial r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              simp [mul_assoc, mul_comm]
        _ = ∑ r ∈ Finset.range (k + 1),
              (Nat.stirlingSecond k r * j.descFactorial (r + 1) +
                (Nat.stirlingSecond k r * (r * j.descFactorial r))) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              -- Expand `j * descFactorial r` and distribute.
              have hmul := hmul_desc r
              calc
                Nat.stirlingSecond k r * (j * j.descFactorial r)
                    = Nat.stirlingSecond k r * (j.descFactorial (r + 1) + r * j.descFactorial r) := by
                        simp [hmul]
                _ = Nat.stirlingSecond k r * j.descFactorial (r + 1) +
                    Nat.stirlingSecond k r * (r * j.descFactorial r) := by
                        simp [mul_add, Nat.mul_assoc, Nat.mul_comm]
        _ = (∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * j.descFactorial (r + 1)) +
              ∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * (r * j.descFactorial r) := by
              simp [Finset.sum_add_distrib]
        _ = (∑ s ∈ Finset.Ico 1 (k + 2), Nat.stirlingSecond k (s - 1) * j.descFactorial s) +
              ∑ r ∈ Finset.range (k + 1), (r * Nat.stirlingSecond k r) * j.descFactorial r := by
              -- Reindex the first sum via `s = r+1`, and commute factors in the second.
              have hshift :
                  ∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * j.descFactorial (r + 1)
                    = ∑ s ∈ Finset.Ico 1 (k + 2), Nat.stirlingSecond k (s - 1) * j.descFactorial s := by
                -- `sum_Ico_eq_sum_range` gives: `∑ s∈Ico 1 (k+2), f s = ∑ r∈range (k+1), f (1+r)`.
                -- Apply it to `f s := stirlingSecond k (s-1) * descFactorial s`.
                have h := (Finset.sum_Ico_eq_sum_range (f := fun s =>
                  Nat.stirlingSecond k (s - 1) * j.descFactorial s) 1 (k + 2)).symm
                -- Rewrite `1 + r - 1 = r`.
                simp [Nat.add_comm] at h
                exact h
              -- Second sum: commute `r` and `stirlingSecond` into the same factor.
              have hcomm :
                  (∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond k r * (r * j.descFactorial r))
                    = ∑ r ∈ Finset.range (k + 1), (r * Nat.stirlingSecond k r) * j.descFactorial r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              simpa [hshift, hcomm]
        _ = ∑ s ∈ Finset.Ico 1 (k + 2),
              (Nat.stirlingSecond k (s - 1) + s * Nat.stirlingSecond k s) * j.descFactorial s := by
              -- Combine the two sums over `Ico 1 (k+2)`.
              -- The second sum is over `range (k+1)`; restrict to `Ico 1 (k+2)` (the `r=0` term is 0).
              have hsecond :
                  (∑ r ∈ Finset.range (k + 1), (r * Nat.stirlingSecond k r) * j.descFactorial r)
                    = ∑ s ∈ Finset.Ico 1 (k + 2), (s * Nat.stirlingSecond k s) * j.descFactorial s := by
                -- Define the summand.
                let f : ℕ → ℕ := fun r => (r * Nat.stirlingSecond k r) * j.descFactorial r
                -- Remove the `r = 0` term (it is zero).
                have hsplit0 :
                    ∑ r ∈ Finset.range (k + 1), f r =
                      ∑ r ∈ Finset.Ico 1 (k + 1), f r := by
                  have hsplit :=
                    (Finset.sum_range_add_sum_Ico
                      (f := f) (m := 1) (n := k + 1) (by exact Nat.succ_le_succ (Nat.zero_le k))).symm
                  have hsum1 : ∑ r ∈ Finset.range 1, f r = 0 := by
                    simp [f, Finset.range_one, Finset.sum_singleton]
                  have hsplit0' :
                      ∑ r ∈ Finset.range (k + 1), f r =
                        ∑ r ∈ Finset.range 1, f r + ∑ r ∈ Finset.Ico 1 (k + 1), f r := by
                    simpa using hsplit
                  calc
                    ∑ r ∈ Finset.range (k + 1), f r
                        = ∑ r ∈ Finset.range 1, f r + ∑ r ∈ Finset.Ico 1 (k + 1), f r := hsplit0'
                    _ = ∑ r ∈ Finset.Ico 1 (k + 1), f r := by
                          simpa [hsum1]
                -- Extend the upper bound by one term (also zero).
                have hIco_extend :
                    ∑ r ∈ Finset.Ico 1 (k + 1), f r =
                      ∑ r ∈ Finset.Ico 1 (k + 2), f r := by
                  have hIco1 :
                      ∑ r ∈ Finset.Ico 1 (k + 1), f r =
                        ∑ t ∈ Finset.range k, f (1 + t) := by
                    simpa [f] using (Finset.sum_Ico_eq_sum_range (f := f) 1 (k + 1))
                  have hIco2 :
                      ∑ r ∈ Finset.Ico 1 (k + 2), f r =
                        ∑ t ∈ Finset.range (k + 1), f (1 + t) := by
                    simpa [f] using (Finset.sum_Ico_eq_sum_range (f := f) 1 (k + 2))
                  have hzero : f (k + 1) = 0 := by
                    simp [f, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self k)]
                  have hsum_succ :
                      ∑ t ∈ Finset.range (k + 1), f (1 + t) =
                        ∑ t ∈ Finset.range k, f (1 + t) := by
                    have h := Finset.sum_range_succ (f := fun t => f (1 + t)) (n := k)
                    simpa [hzero, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
                  calc
                    ∑ r ∈ Finset.Ico 1 (k + 1), f r = ∑ t ∈ Finset.range k, f (1 + t) := hIco1
                    _ = ∑ t ∈ Finset.range (k + 1), f (1 + t) := by
                          simpa using hsum_succ.symm
                    _ = ∑ r ∈ Finset.Ico 1 (k + 2), f r := by
                          simpa using hIco2.symm
                -- Combine the two rewrites.
                simpa [f] using hsplit0.trans hIco_extend
              -- Combine over `Ico 1 (k+2)`.
              rw [hsecond]
              have hfg :
                  ∀ s,
                    (Nat.stirlingSecond k (s - 1) + s * Nat.stirlingSecond k s) * j.descFactorial s =
                      (Nat.stirlingSecond k (s - 1)) * j.descFactorial s +
                        (s * Nat.stirlingSecond k s) * j.descFactorial s := by
                intro s
                simp [mul_add, mul_left_comm, mul_comm]
              symm
              calc
                ∑ s ∈ Finset.Ico 1 (k + 2),
                    (Nat.stirlingSecond k (s - 1) + s * Nat.stirlingSecond k s) * j.descFactorial s
                    =
                    ∑ s ∈ Finset.Ico 1 (k + 2),
                      ((Nat.stirlingSecond k (s - 1)) * j.descFactorial s +
                        (s * Nat.stirlingSecond k s) * j.descFactorial s) := by
                      refine Finset.sum_congr rfl ?_
                      intro s hs
                      simp [hfg s]
                _ = ∑ s ∈ Finset.Ico 1 (k + 2), (Nat.stirlingSecond k (s - 1)) * j.descFactorial s +
                      ∑ s ∈ Finset.Ico 1 (k + 2), (s * Nat.stirlingSecond k s) * j.descFactorial s := by
                      simp [Finset.sum_add_distrib]
        _ = ∑ s ∈ Finset.Ico 1 (k + 2), Nat.stirlingSecond (k + 1) s * j.descFactorial s := by
              -- Use the Stirling recurrence `S(k+1,s) = s*S(k,s) + S(k,s-1)` for `s ≠ 0`.
              refine Finset.sum_congr rfl ?_
              intro s hs
              have hs0 : s ≠ 0 := by
                have : 1 ≤ s := by
                  -- `s ∈ Ico 1 (k+2)` implies `1 ≤ s`.
                  exact (Finset.mem_Ico.mp hs).1
                exact Nat.ne_of_gt this
              -- Rewrite using the recurrence.
              have := Nat.stirlingSecond_succ_left k s hs0
              -- Put it in the right additive order.
              -- `S(k+1,s) = s*S(k,s) + S(k,s-1)`.
              -- Our coefficient is `S(k,s-1) + s*S(k,s)`.
              simp [this, Nat.add_comm]
        _ = ∑ s ∈ Finset.range (k + 2), Nat.stirlingSecond (k + 1) s * j.descFactorial s := by
              -- Extend the `Ico 1 (k+2)` sum to `range (k+2)`; the `s=0` term is zero.
              -- `range (k+2)` splits into `{0} ∪ Ico 1 (k+2)`.
              have : ∑ s ∈ Finset.range (k + 2), Nat.stirlingSecond (k + 1) s * j.descFactorial s =
                  (Nat.stirlingSecond (k + 1) 0 * j.descFactorial 0) +
                    ∑ s ∈ Finset.Ico 1 (k + 2), Nat.stirlingSecond (k + 1) s * j.descFactorial s := by
                simpa [Finset.range_one, Finset.sum_singleton] using
                  (Finset.sum_range_add_sum_Ico (f := fun s =>
                    Nat.stirlingSecond (k + 1) s * j.descFactorial s) (m := 1) (n := k + 2) (by omega)).symm
              -- The `s=0` term vanishes since `stirlingSecond (k+1) 0 = 0`.
              simpa [Nat.stirlingSecond_succ_zero] using this.symm

/-! ### Bernstein weights reproduce factorial moments -/

lemma sum_choose_smul_bernsteinPolynomial (n r : ℕ) :
    (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) • bernsteinPolynomial ℝ n (j : ℕ)) =
      (Nat.choose n r : ℝ) • (X ^ r : ℝ[X]) := by
  classical
  -- Compare the two polynomials by evaluating on `[0,1]`.
  apply polynomial_eq_of_toContinuousMapOn_eq
  ext x
  -- Expand the left-hand side pointwise using Bernstein's formula.
  have hL :
      ((∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) • bernsteinPolynomial ℝ n (j : ℕ)).toContinuousMapOn I) x
        =
        ∑ j : Fin (n + 1),
          (x : ℝ) ^ (j : ℕ) *
            ((Nat.choose n (j : ℕ) : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * (1 - (x : ℝ)) ^ (n - (j : ℕ)))) := by
    -- Evaluation is linear, and Bernstein polynomials have a closed form.
    change Polynomial.eval (x : ℝ)
        (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) • bernsteinPolynomial ℝ n (j : ℕ)) = _
    -- Push evaluation through the finite sum and expand Bernstein polynomials.
    let f : Fin (n + 1) → ℝ[X] := fun j =>
      (Nat.choose (j : ℕ) r : ℝ) • bernsteinPolynomial ℝ n (j : ℕ)
    simpa [f, bernsteinPolynomial, smul_eq_mul, Polynomial.eval_pow, mul_left_comm, mul_comm, mul_assoc] using
        (eval_fin_sum (n := n + 1) (x := (x : ℝ)) (f := f))
  -- Expand the right-hand side pointwise.
  have hR :
      (((Nat.choose n r : ℝ) • (X ^ r : ℝ[X])).toContinuousMapOn I) x
        = (Nat.choose n r : ℝ) * (x : ℝ) ^ r := by
    simp [Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, Polynomial.eval_pow,
      Polynomial.eval_smul]
  -- Reduce to a scalar identity over ℝ.
  -- Convert the Finite sum over `Fin` to a range sum and reindex.
  -- Then apply the binomial identity.
  -- 1) Drop the `j < r` terms (choose j r = 0).
  -- 2) Reindex `j = r + t`.
  -- 3) Use `choose_mul` and binomial expansion.
  -- The algebra below is pointwise over `ℝ`.
  by_cases hr : r ≤ n
  ·
    -- Convert `Fin` sum to `range`.
    have hfin :
        (∑ j : Fin (n + 1),
          (x : ℝ) ^ (j : ℕ) *
            ((Nat.choose n (j : ℕ) : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * (1 - (x : ℝ)) ^ (n - (j : ℕ)))))
          =
          ∑ j ∈ Finset.range (n + 1),
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))) := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (f := fun j : ℕ =>
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))))
          (n := n + 1))
    -- Split off the `j < r` terms (they vanish).
    have hsplit :
        (∑ j ∈ Finset.range (n + 1),
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))))
          =
        ∑ j ∈ Finset.Ico r (n + 1),
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))) := by
      have hr' : r ≤ n + 1 := Nat.le_trans hr (Nat.le_succ _)
      have hdecomp :=
        (Finset.sum_range_add_sum_Ico
          (f := fun j =>
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))))
          (m := r) (n := n + 1) hr')
      have hzero :
          ∑ j ∈ Finset.range r,
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjlt : j < r := Finset.mem_range.mp hj
        simp [Nat.choose_eq_zero_of_lt hjlt]
      simpa [hzero, add_zero] using hdecomp.symm
    -- Reindex the sum `j = r + t`.
    have hreindex :
        (∑ j ∈ Finset.Ico r (n + 1),
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))))
          =
        ∑ t ∈ Finset.range (n + 1 - r),
          (x : ℝ) ^ (r + t) * ((Nat.choose n (r + t) : ℝ) *
            ((Nat.choose (r + t) r : ℝ) * (1 - (x : ℝ)) ^ (n - (r + t)))) := by
      -- `sum_Ico_eq_sum_range` shifts indices by `r`.
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Finset.sum_Ico_eq_sum_range
          (f := fun j =>
            (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))))
          (m := r) (n := n + 1))
    -- Now use the binomial identity.
    -- `choose n (r+t) * choose (r+t) r = choose n r * choose (n-r) t`.
    have hchoose :
        ∀ t ∈ Finset.range (n + 1 - r),
          (Nat.choose n (r + t) : ℝ) * (Nat.choose (r + t) r : ℝ)
            = (Nat.choose n r : ℝ) * (Nat.choose (n - r) t : ℝ) := by
      intro t ht
      have ht' : t ≤ n - r := by
        -- t < n+1-r
        have ht' : t < n + 1 - r := Finset.mem_range.mp ht
        have hlen : n + 1 - r = n - r + 1 := by
          omega
        have ht'' : t < n - r + 1 := by simpa [hlen] using ht'
        exact Nat.lt_succ_iff.mp ht''
      have hrle : r ≤ r + t := Nat.le_add_right _ _
      have hnat : n.choose (r + t) * (r + t).choose r =
          n.choose r * (n - r).choose (r + t - r) :=
        Nat.choose_mul (n := n) (k := r + t) (s := r) hrle
      have hsub : r + t - r = t := Nat.add_sub_cancel_left _ _
      exact_mod_cast (by simpa [hsub] using hnat)
    -- Apply the binomial theorem on `x + (1-x)`.
    have hbinom :
        ∑ t ∈ Finset.range (n + 1 - r),
            (Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t * (1 - (x : ℝ)) ^ ((n - r) - t)
          = 1 := by
      have hpow :=
        (add_pow (x : ℝ) (1 - (x : ℝ)) (n - r))
      -- `x + (1-x) = 1`
      have hx1 : (x : ℝ) + (1 - (x : ℝ)) = 1 := by ring
      -- Reorder the binomial expansion.
      have hsum :
          ∑ t ∈ Finset.range ((n - r) + 1),
              (Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t * (1 - (x : ℝ)) ^ ((n - r) - t)
            = ((x : ℝ) + (1 - (x : ℝ))) ^ (n - r) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hpow.symm
      have hlen : (n + 1 - r) = (n - r + 1) := by
        omega
      simpa [hx1, hlen] using hsum
    -- Finish.
    -- Put all transformations together.
    have hmain :
        ∑ j : Fin (n + 1),
            (x : ℝ) ^ (j : ℕ) *
              ((Nat.choose n (j : ℕ) : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * (1 - (x : ℝ)) ^ (n - (j : ℕ))))
          = (Nat.choose n r : ℝ) * (x : ℝ) ^ r := by
      -- assemble the chain
      calc
        ∑ j : Fin (n + 1),
            (x : ℝ) ^ (j : ℕ) *
              ((Nat.choose n (j : ℕ) : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * (1 - (x : ℝ)) ^ (n - (j : ℕ))))
            = ∑ j ∈ Finset.range (n + 1),
                (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))) := hfin
        _ = ∑ j ∈ Finset.Ico r (n + 1),
              (x : ℝ) ^ j * ((Nat.choose n j : ℝ) * ((Nat.choose j r : ℝ) * (1 - (x : ℝ)) ^ (n - j))) := hsplit
        _ = ∑ t ∈ Finset.range (n + 1 - r),
              (x : ℝ) ^ (r + t) * ((Nat.choose n (r + t) : ℝ) *
                ((Nat.choose (r + t) r : ℝ) * (1 - (x : ℝ)) ^ (n - (r + t)))) := hreindex
        _ = (Nat.choose n r : ℝ) * (x : ℝ) ^ r *
              ∑ t ∈ Finset.range (n + 1 - r),
                (Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t * (1 - (x : ℝ)) ^ ((n - r) - t) := by
              -- First rewrite each summand, then pull constants out.
              have hsum' :
                  ∑ t ∈ Finset.range (n + 1 - r),
                      (x : ℝ) ^ (r + t) * ((Nat.choose n (r + t) : ℝ) *
                        ((Nat.choose (r + t) r : ℝ) * (1 - (x : ℝ)) ^ (n - (r + t))))
                    =
                  ∑ t ∈ Finset.range (n + 1 - r),
                      (Nat.choose n r : ℝ) * (x : ℝ) ^ r *
                        ((Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t *
                          (1 - (x : ℝ)) ^ ((n - r) - t)) := by
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    have hxpow : (x : ℝ) ^ (r + t) = (x : ℝ) ^ r * (x : ℝ) ^ t := by
                      simp [pow_add]
                    have hsub : n - (r + t) = (n - r) - t := by
                      -- `Nat.sub_sub` gives the reverse direction
                      exact (Nat.sub_sub n r t).symm
                    have hA : (1 - (x : ℝ)) ^ (n - (r + t)) = (1 - (x : ℝ)) ^ ((n - r) - t) := by
                      simp [hsub]
                    calc
                      (x : ℝ) ^ (r + t) * ((Nat.choose n (r + t) : ℝ) *
                          ((Nat.choose (r + t) r : ℝ) * (1 - (x : ℝ)) ^ (n - (r + t))))
                          = (x : ℝ) ^ r * (x : ℝ) ^ t *
                              (((Nat.choose n (r + t) : ℝ) * (Nat.choose (r + t) r : ℝ)) *
                                (1 - (x : ℝ)) ^ ((n - r) - t)) := by
                              -- rewrite powers and the exponent
                              simp [hxpow, hA, mul_assoc]
                      _ = (x : ℝ) ^ r * (x : ℝ) ^ t *
                              (((Nat.choose n r : ℝ) * (Nat.choose (n - r) t : ℝ)) *
                                (1 - (x : ℝ)) ^ ((n - r) - t)) := by
                              -- apply the combinatorial identity
                              simp [hchoose t ht, mul_assoc]
                      _ = (Nat.choose n r : ℝ) * (x : ℝ) ^ r *
                              ((Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t *
                                (1 - (x : ℝ)) ^ ((n - r) - t)) := by
                              -- reorder factors
                              simp [mul_assoc, mul_left_comm, mul_comm]
              -- pull constants outside the sum
              simp [hsum', Finset.mul_sum]
        _ = (Nat.choose n r : ℝ) * (x : ℝ) ^ r := by
              calc
                (Nat.choose n r : ℝ) * (x : ℝ) ^ r *
                    ∑ t ∈ Finset.range (n + 1 - r),
                      (Nat.choose (n - r) t : ℝ) * (x : ℝ) ^ t * (1 - (x : ℝ)) ^ ((n - r) - t)
                    = (Nat.choose n r : ℝ) * (x : ℝ) ^ r * 1 := by
                        simp [hbinom]
                _ = (Nat.choose n r : ℝ) * (x : ℝ) ^ r := by ring
    -- Conclude.
    simp [hL, hR, hmain]
  ·
    -- `r > n`: both sides evaluate to zero.
    have hr' : n < r := Nat.lt_of_not_ge hr
    have hchoose : (Nat.choose n r : ℝ) = 0 := by
      exact_mod_cast (Nat.choose_eq_zero_of_lt hr')
    have hsum0 :
        ∑ j : Fin (n + 1),
          (x : ℝ) ^ (j : ℕ) *
            ((Nat.choose n (j : ℕ) : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * (1 - (x : ℝ)) ^ (n - (j : ℕ)))) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjle : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
      have hjlt : (j : ℕ) < r := lt_of_le_of_lt hjle hr'
      simp [Nat.choose_eq_zero_of_lt hjlt]
    simp [hL, hsum0, hchoose]

lemma bernsteinWeight_choose_moment (m : ℕ → ℝ) (n r : ℕ) :
    (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) * bernsteinWeight m n j) =
      (Nat.choose n r : ℝ) * m r := by
  classical
  -- Apply `momentFunctional` to the polynomial identity from `sum_choose_smul_bernsteinPolynomial`.
  have hid := congrArg (momentFunctional m) (sum_choose_smul_bernsteinPolynomial (n := n) (r := r))
  -- Expand both sides using linearity and the `momentFunctional` evaluation on Bernstein polynomials.
  -- On the left, `momentFunctional m (bernsteinPolynomial ℝ n j) = bernsteinWeight m n j`.
  -- On the right, `momentFunctional m (X^r) = m r`.
  -- First rewrite the LHS as a Finset sum.
  have hL :
      momentFunctional m (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) • bernsteinPolynomial ℝ n (j : ℕ))
        = ∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) * momentFunctional m (bernsteinPolynomial ℝ n (j : ℕ)) := by
    -- Turn scalar multiplication into multiplication by a scalar.
    simp [map_sum, smul_eq_mul]
  -- And similarly for the RHS.
  have hR : momentFunctional m ((Nat.choose n r : ℝ) • (X ^ r : ℝ[X])) =
      (Nat.choose n r : ℝ) * momentFunctional m (X ^ r : ℝ[X]) := by
    simp [smul_eq_mul]
  -- Now combine.
  -- `momentFunctional m (bernsteinPolynomial ℝ n j) = bernsteinWeight m n j` since `j ≤ n`.
  have hbern : ∀ j : Fin (n + 1), momentFunctional m (bernsteinPolynomial ℝ n (j : ℕ)) = bernsteinWeight m n (j : ℕ) := by
    intro j
    have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    simp [bernsteinWeight, hj, momentFunctional_bernsteinPolynomial m n (j : ℕ)]
  -- Finish by rewriting `hid` with these expansions.
  -- Note: `momentFunctional_X_pow` gives the moment of `X^r`.
  have : ∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) * bernsteinWeight m n (j : ℕ) =
        (Nat.choose n r : ℝ) * m r := by
    -- Rewrite `hid` using `hL`, `hR`, and `hbern`.
    simpa [hL, hR, hbern, momentFunctional_X_pow] using hid
  exact this

lemma bernsteinWeight_descFactorial_moment (m : ℕ → ℝ) (n r : ℕ) :
    (∑ j : Fin (n + 1), ((j : ℕ).descFactorial r : ℝ) * bernsteinWeight m n (j : ℕ)) =
      (n.descFactorial r : ℝ) * m r := by
  classical
  -- Reduce to the `choose`-moment identity using `descFactorial = r! * choose`.
  have hchoose := bernsteinWeight_choose_moment (m := m) (n := n) (r := r)
  have hdf (a : ℕ) : (a.descFactorial r : ℝ) = (r.factorial : ℝ) * (a.choose r : ℝ) := by
    -- Cast the Nat identity `a.descFactorial r = r! * a.choose r`.
    have h : a.descFactorial r = r.factorial * a.choose r :=
      Nat.descFactorial_eq_factorial_mul_choose a r
    exact_mod_cast h
  -- Multiply the `choose` identity by `r!` and rewrite both sides via `hdf`.
  have hmul :
      (r.factorial : ℝ) *
          (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) * bernsteinWeight m n (j : ℕ)) =
        (r.factorial : ℝ) * ((Nat.choose n r : ℝ) * m r) := by
    exact congrArg (fun t => (r.factorial : ℝ) * t) hchoose
  -- Simplify the multiplied identity into the desired descending-factorial moment statement.
  -- Left: pull `r!` inside and rewrite as `descFactorial`.
  -- Right: rewrite `r! * choose n r` as `descFactorial`.
  -- We keep the arithmetic commutativity explicit for readability.
  -- LHS
  have hL :
      (r.factorial : ℝ) *
          (∑ j : Fin (n + 1), (Nat.choose (j : ℕ) r : ℝ) * bernsteinWeight m n (j : ℕ)) =
        ∑ j : Fin (n + 1), ((j : ℕ).descFactorial r : ℝ) * bernsteinWeight m n (j : ℕ) := by
    -- Distribute and use `hdf`.
    -- `r! * (choose j r * w_j) = (descFactorial j r) * w_j`.
    have : ∀ j : Fin (n + 1),
        (r.factorial : ℝ) * ((Nat.choose (j : ℕ) r : ℝ) * bernsteinWeight m n (j : ℕ)) =
          ((j : ℕ).descFactorial r : ℝ) * bernsteinWeight m n (j : ℕ) := by
      intro j
      simp [hdf (j : ℕ), mul_assoc, mul_left_comm, mul_comm]
    -- Use `Finset.mul_sum` and rewrite each term.
    simp [Finset.mul_sum, this]
  -- RHS
  have hR :
      (r.factorial : ℝ) * ((Nat.choose n r : ℝ) * m r) = (n.descFactorial r : ℝ) * m r := by
    -- `n.descFactorial r = r! * n.choose r`.
      simp [hdf n, mul_assoc, mul_comm]
  -- Conclude.
  -- Rewrite `hmul` using `hL` and `hR`.
  have h := hmul
  rw [hL, hR] at h
  exact h

/-! ## Asymptotics for descending factorials -/

private lemma tendsto_sub_div (i : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - (i : ℝ)) / (n : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hdiv : Filter.Tendsto (fun n : ℕ => (i : ℝ) / (n : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (i : ℝ)) Filter.atTop (nhds (i : ℝ)) := by
      exact (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (i : ℝ)) Filter.atTop (nhds (i : ℝ)))
    have hdiv' := hconst.mul hinv
    simpa using hdiv'
  have hEq :
      (fun n : ℕ => ((n : ℝ) - (i : ℝ)) / (n : ℝ)) =ᶠ[Filter.atTop]
        fun n : ℕ => (1 : ℝ) - (i : ℝ) / (n : ℝ) := by
    have hne : (∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≠ 0) := by
      refine (Filter.eventually_atTop.2 ?_)
      refine ⟨1, ?_⟩
      intro n hn
      exact_mod_cast (Nat.succ_le_iff.1 hn).ne'
    filter_upwards [hne] with n hn
    field_simp [hn]
  have hsub :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (i : ℝ) / (n : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    have h := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
      (nhds (1 : ℝ))).sub hdiv)
    simp at h
    exact h
  exact hsub.congr' hEq.symm

private lemma cast_descFactorial_eq_prod_sub (n r : ℕ) (hn : r ≤ n) :
    (n.descFactorial r : ℝ) = ∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) := by
  classical
  have hnat : n.descFactorial r = ∏ i ∈ Finset.range r, (n - i) :=
    Nat.descFactorial_eq_prod_range n r
  have hcast : (n.descFactorial r : ℝ) =
      ∏ i ∈ Finset.range r, ((n - i : ℕ) : ℝ) := by
    simpa using congrArg (fun t : ℕ => (t : ℝ)) hnat
  refine hcast.trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i < r := Finset.mem_range.mp hi
  have hin : i ≤ n := le_trans (Nat.le_of_lt hir) hn
  exact (Nat.cast_sub hin)

private lemma prod_div_by_const (r : ℕ) (n : ℕ) :
    (∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) / (n : ℝ)) =
      (∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ))) / (n : ℝ) ^ r := by
  classical
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, mul_comm]

private lemma tendsto_descFactorial_div_pow (r : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n.descFactorial r : ℝ) / (n : ℝ) ^ r)
      Filter.atTop (nhds (1 : ℝ)) := by
  classical
  by_cases hr : r = 0
  · subst hr
    simp
  have hEq :
      (fun n : ℕ => (n.descFactorial r : ℝ) / (n : ℝ) ^ r) =ᶠ[Filter.atTop]
        fun n : ℕ => ∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) / (n : ℝ) := by
    refine (Filter.eventually_atTop.2 ?_)
    refine ⟨r, ?_⟩
    intro n hn
    have hprod := cast_descFactorial_eq_prod_sub n r hn
    calc
      (n.descFactorial r : ℝ) / (n : ℝ) ^ r
          = (∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ))) / (n : ℝ) ^ r := by
              simp [hprod]
      _ = ∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) / (n : ℝ) := by
            symm
            exact prod_div_by_const r n
  have hprod :
      Filter.Tendsto (fun n : ℕ =>
        ∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) / (n : ℝ))
        Filter.atTop (nhds (∏ i ∈ Finset.range r, (1 : ℝ))) := by
    refine tendsto_finset_prod (s := Finset.range r) ?_
    intro i hi
    exact tendsto_sub_div i
  have hprod' : (∏ i ∈ Finset.range r, (1 : ℝ)) = (1 : ℝ) := by
    simp
  have hprod'' :
      Filter.Tendsto (fun n : ℕ =>
        ∏ i ∈ Finset.range r, ((n : ℝ) - (i : ℝ)) / (n : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa [hprod'] using hprod
  exact hprod''.congr' hEq.symm

private lemma tendsto_descFactorial_div_pow_lt (k r : ℕ) (hrk : r < k) :
    Filter.Tendsto (fun n : ℕ => (n.descFactorial r : ℝ) / (n : ℝ) ^ k)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hratio := tendsto_descFactorial_div_pow r
  have hp : 0 < k - r := Nat.sub_pos_of_lt hrk
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hinv_pow :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ (k - r))⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    have hpow := hinv.pow (k - r)
    -- rewrite `(n⁻¹)^(k-r)` as `(n^(k-r))⁻¹` and simplify the limit
    simpa [inv_pow, zero_pow (Nat.ne_of_gt hp)] using hpow
  have hEq :
      (fun n : ℕ => (n.descFactorial r : ℝ) / (n : ℝ) ^ k) =ᶠ[Filter.atTop]
        fun n : ℕ =>
          (n.descFactorial r : ℝ) / (n : ℝ) ^ r * ((n : ℝ) ^ (k - r))⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hk : k = r + (k - r) := (Nat.add_sub_of_le (Nat.le_of_lt hrk)).symm
    -- Rewrite using `pow_add` and `div_mul_eq_div_div`.
    have hpow : (n : ℝ) ^ k = (n : ℝ) ^ r * (n : ℝ) ^ (k - r) := by
      calc
        (n : ℝ) ^ k = (n : ℝ) ^ (r + (k - r)) := by
          exact congrArg (fun t : ℕ => (n : ℝ) ^ t) hk
        _ = (n : ℝ) ^ r * (n : ℝ) ^ (k - r) := by
          exact (pow_add (n : ℝ) r (k - r))
    calc
      (n.descFactorial r : ℝ) / (n : ℝ) ^ k
          = (n.descFactorial r : ℝ) / ((n : ℝ) ^ r * (n : ℝ) ^ (k - r)) := by
              simp [hpow]
      _ = (n.descFactorial r : ℝ) / (n : ℝ) ^ r / (n : ℝ) ^ (k - r) := by
              simp [div_mul_eq_div_div]
      _ = (n.descFactorial r : ℝ) / (n : ℝ) ^ r * ((n : ℝ) ^ (k - r))⁻¹ := by
              simp [div_eq_mul_inv, mul_assoc]
  have hmul := (hratio.mul hinv_pow).congr' hEq.symm
  simp at hmul
  exact hmul

private lemma stirling_term_tendsto (m : ℕ → ℝ) (k r : ℕ) (hrle : r ≤ k) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.stirlingSecond k r : ℝ) *
          ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r)
      Filter.atTop
      (nhds (if r = k then m k else 0)) := by
  by_cases hkr : r = k
  · subst r
    have hratio := tendsto_descFactorial_div_pow k
    have hcoef : (Nat.stirlingSecond k k : ℝ) = 1 := by
      simp [Nat.stirlingSecond_self]
    have hconst : Filter.Tendsto (fun _ : ℕ => (m k : ℝ)) Filter.atTop (nhds (m k)) := by
      exact (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (m k : ℝ)) Filter.atTop (nhds (m k)))
    have hmul : Filter.Tendsto
        (fun n : ℕ => ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) * m k)
        Filter.atTop (nhds (1 * m k)) := by
      exact (hratio.mul hconst)
    have hmul2 : Filter.Tendsto
        (fun n : ℕ => (Nat.stirlingSecond k k : ℝ) *
          (((n.descFactorial k : ℝ) / (n : ℝ) ^ k) * m k))
        Filter.atTop (nhds ((Nat.stirlingSecond k k : ℝ) * (1 * m k))) := by
      exact (tendsto_const_nhds.mul hmul)
    simpa [hcoef] using hmul2
  · have hlt : r < k := by
      exact lt_of_le_of_ne hrle hkr
    have hratio := tendsto_descFactorial_div_pow_lt k r hlt
    have hconst : Filter.Tendsto (fun _ : ℕ => (m r : ℝ)) Filter.atTop (nhds (m r)) := by
      exact (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (m r : ℝ)) Filter.atTop (nhds (m r)))
    have hmul : Filter.Tendsto
        (fun n : ℕ =>
          ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r)
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa [zero_mul] using (hratio.mul hconst)
    have hmul2 :
        Filter.Tendsto
          (fun n : ℕ =>
            (Nat.stirlingSecond k r : ℝ) *
              (((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r))
          Filter.atTop (nhds (0 : ℝ)) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hmul)
    simpa [mul_assoc, hkr] using hmul2

/-- Key convergence lemma: For bounded completely monotone m with m(0) = 1,
    the k-th Bernstein moment converges to m(k) as n → ∞.

    This is the computational heart of the Hausdorff moment theorem.
    The proof uses the Bernstein approximation of polynomials. -/
theorem bernsteinMoment_tendsto (m : ℕ → ℝ)
    (_hbnd : ∀ j, m j ∈ Set.Icc 0 1)
    (_hcm : CompletelyMonotone m)
    (_hzero : m 0 = 1) (k : ℕ) :
    Filter.Tendsto (fun n => bernsteinMoment m n k) Filter.atTop (nhds (m k)) := by
  classical
  -- Auxiliary: a power is a linear combination of descending factorials (over ℝ).
  have hpow_real (j : ℕ) :
      (j : ℝ) ^ k =
        ∑ r ∈ Finset.range (k + 1), (Nat.stirlingSecond k r : ℝ) * (j.descFactorial r : ℝ) := by
    exact_mod_cast (pow_eq_sum_stirlingSecond_descFactorial j k)

  -- Bernstein moment as a Stirling-weighted sum of factorial moments.
  have hsum :
      ∀ n : ℕ,
        bernsteinMoment m n k =
          ∑ r ∈ Finset.range (k + 1),
            (Nat.stirlingSecond k r : ℝ) *
              ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r := by
    intro n
    -- Expand definition and substitute the Stirling expansion of `(j : ℝ)^k`.
    -- First, rewrite `bernsteinMoment` as `∑ w_j * (j^k / n^k)`.
    have hdef :
        bernsteinMoment m n k =
          ∑ j : Fin (n + 1),
            bernsteinWeight m n j * (((j : ℝ) ^ k) / (n : ℝ) ^ k) := by
      -- `bernstein.z j = j/n`
      simp [bernsteinMoment, bernstein.z, div_pow]
    -- Substitute the Stirling expansion and swap finite sums.
    -- We keep the algebra explicit to avoid simp loops.
    calc
      bernsteinMoment m n k
          = ∑ j : Fin (n + 1),
              bernsteinWeight m n j * (((j : ℝ) ^ k) / (n : ℝ) ^ k) := hdef
      _ = ∑ j : Fin (n + 1),
            bernsteinWeight m n j *
              ((∑ r ∈ Finset.range (k + 1),
                  (Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ)) / (n : ℝ) ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hpow_real (j : ℕ)]
      _ = ∑ r ∈ Finset.range (k + 1),
            (Nat.stirlingSecond k r : ℝ) *
              ((∑ j : Fin (n + 1),
                  bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) / (n : ℝ) ^ k) := by
            -- Swap sums and factor constants without heavy `simp`.
            -- Write `/ n^k` as multiplication by a constant and move it outside sums.
            -- Then use `sum_comm` to swap the finite sums.
            have hstep :
                ∑ j : Fin (n + 1),
                  bernsteinWeight m n j *
                    ((∑ r ∈ Finset.range (k + 1),
                        (Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ)) /
                      (n : ℝ) ^ k)
                  =
                ∑ j : Fin (n + 1),
                  (∑ r ∈ Finset.range (k + 1),
                      bernsteinWeight m n j *
                        ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                    (n : ℝ) ^ k := by
              -- pull `bernsteinWeight` inside the sum over `r`
              refine Finset.sum_congr rfl ?_
              intro j hj
              -- `w * (∑ r A r) = ∑ r w * A r`
              -- then divide by `n^k`
              simp [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm]
            -- swap sums
            have hswap :
                ∑ j : Fin (n + 1),
                  (∑ r ∈ Finset.range (k + 1),
                      bernsteinWeight m n j *
                        ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                    (n : ℝ) ^ k
                  =
                ∑ r ∈ Finset.range (k + 1),
                  (∑ j : Fin (n + 1),
                      bernsteinWeight m n j *
                        ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                    (n : ℝ) ^ k := by
              -- pull out the constant factor `(n^k)⁻¹` and swap the double sum
              calc
                ∑ j : Fin (n + 1),
                    (∑ r ∈ Finset.range (k + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                      (n : ℝ) ^ k
                    =
                    ∑ j : Fin (n + 1),
                      (∑ r ∈ Finset.range (k + 1),
                          bernsteinWeight m n j *
                            ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) *
                        ((n : ℝ) ^ k)⁻¹ := by
                      simp [div_eq_mul_inv]
                _ = (∑ j : Fin (n + 1),
                      ∑ r ∈ Finset.range (k + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) *
                    ((n : ℝ) ^ k)⁻¹ := by
                      simp [Finset.sum_mul, mul_assoc]
                _ = (∑ r ∈ Finset.range (k + 1),
                      ∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) *
                    ((n : ℝ) ^ k)⁻¹ := by
                      -- swap the double sum explicitly
                      have hcomm :
                          (∑ j : Fin (n + 1),
                              ∑ r ∈ Finset.range (k + 1),
                                bernsteinWeight m n j *
                                  ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ)))
                            =
                          ∑ r ∈ Finset.range (k + 1),
                            ∑ j : Fin (n + 1),
                              bernsteinWeight m n j *
                                ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ)) := by
                            simpa using (Finset.sum_comm : _)
                      -- rewrite with the commuted sum
                      rw [hcomm]
                _ = ∑ r ∈ Finset.range (k + 1),
                      (∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) *
                      ((n : ℝ) ^ k)⁻¹ := by
                      simp [Finset.sum_mul, mul_assoc]
                _ = ∑ r ∈ Finset.range (k + 1),
                      (∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                      (n : ℝ) ^ k := by
                      simp [div_eq_mul_inv]
            -- factor out the Stirling coefficient
            calc
              ∑ j : Fin (n + 1),
                  bernsteinWeight m n j *
                    ((∑ r ∈ Finset.range (k + 1),
                        (Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ)) /
                      (n : ℝ) ^ k)
                  = ∑ j : Fin (n + 1),
                      (∑ r ∈ Finset.range (k + 1),
                          bernsteinWeight m n j *
                            ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                        (n : ℝ) ^ k := hstep
              _ = ∑ r ∈ Finset.range (k + 1),
                    (∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                      (n : ℝ) ^ k := hswap
              _ = ∑ r ∈ Finset.range (k + 1),
                    (Nat.stirlingSecond k r : ℝ) *
                      ((∑ j : Fin (n + 1),
                          bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) /
                        (n : ℝ) ^ k) := by
                  -- pull out the constant coefficient
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  have hfactor :
                      ∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))
                        =
                      (Nat.stirlingSecond k r : ℝ) *
                        ∑ j : Fin (n + 1),
                          bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ) := by
                    calc
                      ∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))
                          =
                        ∑ j : Fin (n + 1),
                          (Nat.stirlingSecond k r : ℝ) *
                            (bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          simp [mul_assoc, mul_left_comm, mul_comm]
                      _ =
                        (Nat.stirlingSecond k r : ℝ) *
                          ∑ j : Fin (n + 1),
                            bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ) := by
                          simp [Finset.mul_sum]
                  -- use `mul_div_assoc` to pull out the coefficient
                  calc
                    (∑ j : Fin (n + 1),
                        bernsteinWeight m n j *
                          ((Nat.stirlingSecond k r : ℝ) * ((j : ℕ).descFactorial r : ℝ))) /
                      (n : ℝ) ^ k
                        = ((Nat.stirlingSecond k r : ℝ) *
                            ∑ j : Fin (n + 1),
                              bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) /
                          (n : ℝ) ^ k := by
                          rw [hfactor]
                    _ = (Nat.stirlingSecond k r : ℝ) *
                          ((∑ j : Fin (n + 1),
                              bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) /
                            (n : ℝ) ^ k) := by
                          exact
                            (mul_div_assoc (Nat.stirlingSecond k r : ℝ)
                              (∑ j : Fin (n + 1),
                                bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ))
                              ((n : ℝ) ^ k))
      _ = ∑ r ∈ Finset.range (k + 1),
            (Nat.stirlingSecond k r : ℝ) *
              (((n.descFactorial r : ℝ) * m r) / (n : ℝ) ^ k) := by
            -- Use the factorial-moment identity.
            refine Finset.sum_congr rfl ?_
            intro r hr
            -- rewrite inner sum
            have hdf := bernsteinWeight_descFactorial_moment (m := m) (n := n) (r := r)
            have hdf' :
                (∑ j : Fin (n + 1),
                    bernsteinWeight m n j * ((j : ℕ).descFactorial r : ℝ)) =
                  (n.descFactorial r : ℝ) * m r := by
              simpa [mul_comm] using hdf
            -- rewrite inner sum using `hdf'`
            simp [hdf']
      _ = ∑ r ∈ Finset.range (k + 1),
            (Nat.stirlingSecond k r : ℝ) *
              ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r := by
            -- move `m r` to the right
            refine Finset.sum_congr rfl ?_
            intro r hr
            -- simple rearrangement without heavy `simp`
            calc
              (Nat.stirlingSecond k r : ℝ) *
                  (((n.descFactorial r : ℝ) * m r) / (n : ℝ) ^ k)
                  =
                (Nat.stirlingSecond k r : ℝ) *
                  (m r * ((n.descFactorial r : ℝ) / (n : ℝ) ^ k)) := by
                    -- commute inside the numerator, then use `mul_div_assoc`
                    have :
                        ((n.descFactorial r : ℝ) * m r) / (n : ℝ) ^ k
                          = m r * ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) := by
                        calc
                          ((n.descFactorial r : ℝ) * m r) / (n : ℝ) ^ k
                              = (m r * (n.descFactorial r : ℝ)) / (n : ℝ) ^ k := by
                                  simp [mul_comm]
                          _ = m r * ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) := by
                                  exact (mul_div_assoc (m r) (n.descFactorial r : ℝ) ((n : ℝ) ^ k))
                    simp [this]
              _ = (Nat.stirlingSecond k r : ℝ) *
                    ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r := by
                    simp [mul_comm, mul_assoc]

  -- Now take the finite sum of termwise limits.
  have hterm :
      ∀ r ∈ Finset.range (k + 1),
        Filter.Tendsto
          (fun n : ℕ =>
            (Nat.stirlingSecond k r : ℝ) *
              ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r)
          Filter.atTop
          (nhds (if r = k then m k else 0)) := by
    intro r hr
    have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    simpa using (stirling_term_tendsto m k r hrle)

  -- Sum the termwise limits.
  have hsum_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range (k + 1),
            (Nat.stirlingSecond k r : ℝ) * ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r)
        Filter.atTop
        (nhds (∑ r ∈ Finset.range (k + 1), if r = k then m k else 0)) := by
    refine
      tendsto_finset_sum (s := Finset.range (k + 1))
        (f := fun r (n : ℕ) =>
          (Nat.stirlingSecond k r : ℝ) * ((n.descFactorial r : ℝ) / (n : ℝ) ^ k) * m r)
        (a := fun r => if r = k then m k else 0) ?_
    exact hterm
  -- Evaluate the finite sum of limits.
  have hsum_lim :
      ∑ r ∈ Finset.range (k + 1), (if r = k then m k else 0) = m k := by
    classical
    -- only the `r = k` term survives
    have hsum' :
        (∑ r ∈ Finset.range (k + 1), (if r = k then m k else 0)) =
          (if k = k then m k else 0) := by
      refine
        (Finset.sum_eq_single (s := Finset.range (k + 1))
          (f := fun r => if r = k then m k else 0) k ?hz ?_)
      · intro r hr hne
        simp [hne]
      · intro hknot
        -- impossible: k is in range (k+1)
        exact (hknot (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim
    simp [hsum']
  -- Rewrite the sum using `hsum`, then evaluate the limit.
  have hsum_tendsto' :
      Filter.Tendsto (fun n => bernsteinMoment m n k)
        Filter.atTop (nhds (∑ r ∈ Finset.range (k + 1), if r = k then m k else 0)) := by
    refine hsum_tendsto.congr' ?_
    exact Filter.Eventually.of_forall (fun n => (hsum n).symm)
  have hsum_tendsto'' :
      Filter.Tendsto (fun n => bernsteinMoment m n k)
        Filter.atTop (nhds (m k)) := by
    simpa [hsum_lim] using hsum_tendsto'
  exact hsum_tendsto''

/-- **Hausdorff Moment Theorem (specialized)**:
    A sequence that is bounded in `[0,1]`, is completely monotone, and starts at `1`
    is the moment sequence of some probability measure on `[0,1]`.

    This is the key result needed for de Finetti's theorem.

    **Proof structure**:
    1. Bernstein weights wₙₖ = C(n,k) Δⁿ⁻ᵏm(k) are non-negative (by complete monotonicity)
    2. Bernstein weights sum to 1 (since m(0) = 1)
    3. Define discrete measures μₙ = Σₖ wₙₖ δ_{k/n}
    4. The space of probability measures on [0,1] is weak-* compact (Prokhorov)
    5. Extract weak-* convergent subsequence μₙᵢ → μ
    6. The limit μ has the required moments: ∫ θ^k dμ = lim ∫ θ^k dμₙᵢ = m(k)

    **Status**: The algebraic infrastructure (steps 1-2) is complete.
    Steps 3-6 require Prokhorov's theorem (not in Mathlib in needed form). -/
theorem hausdorff_moment_exists (m : ℕ → ℝ)
    (hbnd : ∀ k, m k ∈ Set.Icc 0 1)
    (hcm : CompletelyMonotone m)
    (hzero : m 0 = 1) :
    ∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ (Set.Icc 0 1)ᶜ = 0 ∧
      ∀ k, ∫ θ in Set.Icc 0 1, θ ^ k ∂μ = m k := by
  classical
  -- Step 1: define the Bernstein linear functional and its continuous extension.
  let Φlin : ℕ → C(I, ℝ) →ₗ[ℝ] ℝ := fun n =>
    { toFun := bernsteinFunctional m n
      map_add' := by
        intro f g
        simp [bernsteinFunctional, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c f
        simp [bernsteinFunctional, Finset.mul_sum, smul_eq_mul, mul_left_comm] }

  have hbound : ∀ n (f : C(I, ℝ)), ‖Φlin n f‖ ≤ (1 : ℝ) * ‖f‖ := by
    intro n f
    -- `bernsteinFunctional_bound` gives a bound by `‖f‖` on absolute values.
    have h := bernsteinFunctional_bound (m := m) (hcm := hcm) (hzero := hzero) n f
    -- convert `|x| ≤ ‖f‖` to `‖x‖ ≤ 1 * ‖f‖`
    simpa [Real.norm_eq_abs, one_mul] using h

  let Φ : ℕ → C(I, ℝ) →L[ℝ] ℝ := fun n =>
    (Φlin n).mkContinuous 1 (hbound n)

  have hΦ_eq : ∀ n (f : C(I, ℝ)), Φ n f = bernsteinFunctional m n f := by
    intro n f
    rfl

  have hΦ_mem : ∀ n, Φ n ∈ Metric.closedBall (0) (1 : ℝ) := by
    intro n
    -- `‖Φ n‖ ≤ 1`
    have hnorm' : ‖Φ n‖ ≤ (1 : ℝ) := by
      -- `mkContinuous_norm_le` applies to the linear map used to construct `Φ n`.
      have h :=
        LinearMap.mkContinuous_norm_le (f := Φlin n) (C := (1 : ℝ))
          (hC := by norm_num) (h := hbound n)
      simpa [Φ] using h
    -- closed ball criterion
    have hnorm : dist (Φ n) 0 ≤ (1 : ℝ) := by
      -- `dist x 0 = ‖x‖`
      calc
        dist (Φ n) 0 = ‖Φ n - 0‖ := by
          simpa using (dist_eq_norm (a := Φ n) (b := 0))
        _ = ‖Φ n‖ := by simp
        _ ≤ (1 : ℝ) := hnorm'
    simpa [Metric.mem_closedBall] using hnorm

  let u : ℕ → (C(I, ℝ) → ℝ) := fun n => (Φ n : C(I, ℝ) → ℝ)
  let S : Set (C(I, ℝ) → ℝ) :=
    ((↑) : (C(I, ℝ) →L[ℝ] ℝ) → C(I, ℝ) → ℝ) '' Metric.closedBall (0) (1 : ℝ)
  have hScompact : IsCompact S :=
    ContinuousLinearMap.isCompact_image_coe_closedBall (f₀ := (0 : C(I, ℝ) →L[ℝ] ℝ)) (r := 1)

  let F : Filter (C(I, ℝ) → ℝ) := Filter.map u Filter.atTop
  have hS : S ∈ F := by
    -- all `u n` lie in `S`
    have hmem : ∀ n, u n ∈ S := by
      intro n
      refine ⟨Φ n, hΦ_mem n, rfl⟩
    have hmem' : ∀ᶠ n in Filter.atTop, u n ∈ S :=
      Filter.Eventually.of_forall hmem
    simpa [F, Filter.mem_map] using hmem'

  -- Choose an ultrafilter cluster point inside the compact set.
  let U : Ultrafilter (C(I, ℝ) → ℝ) := Ultrafilter.of F
  have hUle : (↑U : Filter _) ≤ F := Ultrafilter.of_le F
  have hUin : S ∈ U := hUle hS
  obtain ⟨x, hxS, hxlim⟩ := hScompact.ultrafilter_le_nhds' U hUin
  -- `x` comes from a continuous linear map with norm ≤ 1.
  rcases hxS with ⟨Φinf, hΦinfmem, rfl⟩

  -- Cluster point of the sequence `u`.
  have hcluster : ClusterPt (Φinf : C(I, ℝ) → ℝ) F := by
    refine (clusterPt_iff_ultrafilter).2 ?_
    exact ⟨U, hUle, hxlim⟩
  have hu : MapClusterPt (Φinf : C(I, ℝ) → ℝ) Filter.atTop u := by
    simpa [MapClusterPt, F, u] using hcluster

  -- Cluster points of a convergent real sequence coincide with the limit.
  have mapClusterPt_eq_of_tendsto :
      ∀ {g : ℕ → ℝ} {x l : ℝ},
        Filter.Tendsto g Filter.atTop (nhds l) →
        MapClusterPt x Filter.atTop g → x = l := by
    intro g x l hg hx
    have hcl : ClusterPt x (Filter.map g Filter.atTop) := by
      simpa [MapClusterPt] using hx
    have hle : Filter.map g Filter.atTop ≤ nhds l := hg
    by_contra hne
    have hdisj : Disjoint (nhds x) (nhds l) := (disjoint_nhds_nhds.2 hne)
    have hbot : nhds x ⊓ nhds l = ⊥ := hdisj.eq_bot
    have hle' : nhds x ⊓ Filter.map g Filter.atTop ≤ nhds x ⊓ nhds l :=
      inf_le_inf_left _ hle
    have hbot' : nhds x ⊓ Filter.map g Filter.atTop = ⊥ := by
      apply le_bot_iff.mp
      simpa [hbot] using hle'
    have hcl' : nhds x ⊓ Filter.map g Filter.atTop ≠ ⊥ := by
      exact (ClusterPt.neBot hcl).ne
    exact (hcl' hbot').elim

  -- Positivity of the limit functional.
  have hposΦ : ∀ f : C(I, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φinf f := by
    intro f hf
    have hcont : ContinuousAt (fun g : C(I, ℝ) → ℝ => g f) Φinf :=
      (continuous_apply f).continuousAt
    have hcl_f : MapClusterPt (Φinf f) Filter.atTop (fun n => (u n) f) := by
      -- evaluation is continuous, so cluster points map under evaluation
      simpa [Function.comp] using
        (MapClusterPt.continuousAt_comp (x := Φinf) (F := Filter.atTop)
          (u := u) (f := fun g : C(I, ℝ) → ℝ => g f) hcont hu)
    have hcl : ClusterPt (Φinf f) (Filter.map (fun n => (u n) f) Filter.atTop) := by
      simpa [MapClusterPt] using hcl_f
    -- all values are nonnegative
    have hnonneg : ∀ n, 0 ≤ (u n) f := by
      intro n
      -- `u n f = bernsteinFunctional m n f`
      have : (u n) f = bernsteinFunctional m n f := by
        simp [u, hΦ_eq]
      -- use positivity of Bernstein functional
      simpa [this] using (bernsteinFunctional_nonneg (m := m) (hcm := hcm) n f hf)
    have hmem : Set.Ici (0 : ℝ) ∈ Filter.map (fun n => (u n) f) Filter.atTop := by
      have hmem' : ∀ᶠ n in Filter.atTop, (u n) f ∈ Set.Ici (0 : ℝ) :=
        Filter.Eventually.of_forall (fun n => hnonneg n)
      simpa [Filter.mem_map] using hmem'
    have hxmem : (Φinf f) ∈ closure (Set.Ici (0 : ℝ)) :=
      (ClusterPt.mem_closure_of_mem (s := Set.Ici (0 : ℝ)) hcl hmem)
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hxmem' : (Φinf f) ∈ Set.Ici (0 : ℝ) := by
      simpa [hclosed.closure_eq] using hxmem
    simpa [Set.mem_Ici] using hxmem'

  -- Build the positive linear functional on `C_c(I, ℝ)`.
  let Λlin : (I →C_c ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => Φinf (f : C(I, ℝ))
      map_add' := by
        intro f g
        change Φinf ((f : C(I, ℝ)) + (g : C(I, ℝ))) =
          Φinf (f : C(I, ℝ)) + Φinf (g : C(I, ℝ))
        exact Φinf.map_add _ _
      map_smul' := by
        intro c f
        change Φinf (c • (f : C(I, ℝ))) = c * Φinf (f : C(I, ℝ))
        exact Φinf.map_smul c (f : C(I, ℝ)) }

  have hΛpos : ∀ f : (I →C_c ℝ), 0 ≤ f → 0 ≤ Λlin f := by
    intro f hf
    have hf' : ∀ x : I, 0 ≤ f x := by
      intro x
      exact hf x
    exact hposΦ (f : C(I, ℝ)) hf'

  let Λ : (I →C_c ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Λlin hΛpos

  -- The representing measure on `I`.
  let μI : Measure I := RealRMK.rieszMeasure Λ

  -- Moment identity on `I`.
  have hmomentI : ∀ k, ∫ x, (x : ℝ) ^ k ∂μI = m k := by
    intro k
    -- Use RMK on the compactly supported monomial.
    let fk : I →C_c ℝ :=
      (CompactlySupportedContinuousMap.continuousMapEquiv (α := I) (β := ℝ)) (monomialFun k)
    have hRMK : ∫ x, fk x ∂μI = Λ fk := by
      dsimp [μI]
      exact RealRMK.integral_rieszMeasure (Λ := Λ) (f := fk)
    -- Identify `fk` and `Λ fk`.
    have hfk : (fun x : I => fk x) = fun x : I => (x : ℝ) ^ k := by
      funext x
      rfl
    have hΛfk : Λ fk = Φinf (monomialFun k) := by
      rfl
    -- Show the limit value `Φinf (monomialFun k) = m k`.
    have hconv : Filter.Tendsto (fun n => bernsteinMoment m n k) Filter.atTop (nhds (m k)) :=
      bernsteinMoment_tendsto m hbnd hcm hzero k
    have hseq : ∀ n, (Φ n) (monomialFun k) = bernsteinMoment m n k := by
      intro n
      simpa [hΦ_eq] using (bernsteinFunctional_monomial m n k)
    have hcont : ContinuousAt (fun g : C(I, ℝ) → ℝ => g (monomialFun k)) Φinf :=
      (continuous_apply (monomialFun k)).continuousAt
    have hcl_mono : MapClusterPt (Φinf (monomialFun k)) Filter.atTop
        (fun n => (u n) (monomialFun k)) := by
      simpa [Function.comp, u] using (MapClusterPt.continuousAt_comp hcont hu)
    have hlim : Φinf (monomialFun k) = m k := by
      -- Use convergence of the Bernstein moments.
      have hconv' : Filter.Tendsto (fun n => (u n) (monomialFun k)) Filter.atTop (nhds (m k)) := by
        -- rewrite using `hseq`
        simpa [u, hseq] using hconv
      exact mapClusterPt_eq_of_tendsto hconv' hcl_mono
    -- Conclude.
    simpa [hfk, hΛfk, hlim] using hRMK

  -- Show the representing measure on `I` has total mass 1.
  have hμI_univ : μI Set.univ = 1 := by
    -- From the moment identity at k = 0.
    have hreal : μI.real Set.univ = 1 := by
      have h := hmomentI 0
      simp [pow_zero, hzero] at h
      exact h
    have hfinite : μI Set.univ ≠ ⊤ := by
      intro htop
      have hzero : μI.real Set.univ = 0 := by
        simp [Measure.real, htop]
      have : (1 : ℝ) = 0 := by
        calc
          (1 : ℝ) = μI.real Set.univ := by simp [hreal]
          _ = 0 := hzero
      exact (one_ne_zero this).elim
    -- Convert `toReal` back to `ENNReal`.
    calc
      μI Set.univ = ENNReal.ofReal (μI.real Set.univ) := (ENNReal.ofReal_toReal hfinite).symm
      _ = 1 := by simp [hreal]

  -- Push the measure to ℝ.
  let μ : Measure ℝ := Measure.map (fun x : I => (x : ℝ)) μI
  have hμprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have hmeas : AEMeasurable (fun x : I => (x : ℝ)) μI := by fun_prop
    simpa [μ, Measure.map_apply, hmeas] using hμI_univ

  have hsupport : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    -- The image of `I` is contained in `[0,1]`.
    have hpre :
        (fun x : I => (x : ℝ)) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = (∅ : Set I) := by
      ext x
      -- `x` already lies in `[0,1]`.
      simp
    have hmeas : AEMeasurable (fun x : I => (x : ℝ)) μI := by fun_prop
    simp [μ, hpre, hmeas]

  refine ⟨μ, hμprob, hsupport, ?_⟩
  intro k
  -- Reduce the integral on `[0,1]` to `μI`.
  have hmap :
      ∫ θ, (θ : ℝ) ^ k ∂μ = ∫ x, (x : ℝ) ^ k ∂μI := by
    -- `Subtype.val` is measurable; use `integral_map`.
    simpa [μ] using
      (MeasureTheory.integral_map (μ := μI)
        (φ := fun x : I => (x : ℝ))
        (f := fun θ : ℝ => θ ^ k)
        (hφ := by fun_prop)
        (hfm := by fun_prop))
  -- Since μ is supported on `[0,1]`, restricting to `Icc` does not change the integral.
  have hrestrict : μ.restrict (Set.Icc (0 : ℝ) 1) = μ := by
    -- `μ`-a.e. points lie in `[0,1]`.
    have hmem : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 := by
      -- from `hsupport`
      have hcomp : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := hsupport
      have hnot : μ {x | x ∉ Set.Icc (0 : ℝ) 1} = 0 := by
        simpa [Set.compl_def] using hcomp
      exact (ae_iff.2 hnot)
    exact Measure.restrict_eq_self_of_ae_mem hmem
  -- Finish.
  calc
    ∫ θ in Set.Icc (0 : ℝ) 1, θ ^ k ∂μ
        = ∫ θ, (θ : ℝ) ^ k ∂μ.restrict (Set.Icc (0 : ℝ) 1) := rfl
    _ = ∫ θ, (θ : ℝ) ^ k ∂μ := by simp [hrestrict]
    _ = ∫ x, (x : ℝ) ^ k ∂μI := hmap
    _ = m k := hmomentI k

end HausdorffTheorem

end Mettapedia.Logic.HausdorffMoment
