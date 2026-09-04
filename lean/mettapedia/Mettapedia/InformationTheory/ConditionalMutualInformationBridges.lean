import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mettapedia.InformationTheory.MutualInformation
import Mettapedia.InformationTheory.ShannonEntropy.Interface

/-!
# Bridges from the finite random-variable divergences to the existing KL and MI carriers

`Mettapedia.InformationTheory.ConditionalMutualInformation` works with raw weight functions and
pushforwards so that conditional mutual information along chains can be stated without
choosing a carrier.  This file identifies its objects with the carriers already in use:

* `klSum_eq_klDivergenceVec`: on probability vectors the divergence sum is the project's
  unified `klDivergenceVec` (and hence the Knuth–Skilling `klDivergence`).
* `klSum_eq_sum_klFun`: with equal total masses the divergence sum is the `klFun`-weighted sum
  used by Mathlib's Kullback–Leibler development; `klFun_nonneg` then gives a second proof of
  Gibbs' inequality (`klSum_nonneg_of_klFun`).
* `mutualInfo_eq_shannonMutualInformationNats`: the mutual information of two `Fin`-valued
  random variables is `JointProb.shannonMutualInformationNats` of their joint law.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Real Finset BigOperators

/-! ## Divergence vectors -/

theorem klSum_eq_klDivergenceVec {n : ℕ} (P Q : ProbVec n)
    (hQ_pos : ∀ i, P.1 i ≠ 0 → 0 < Q.1 i) :
    klSum P.1 Q.1 = klDivergenceVec P Q hQ_pos := by
  unfold klSum klSumOn klDivergenceVec ProbVec.toProbDist
    KnuthSkilling.Information.InformationEntropy.klDivergence
  rfl

/-! ## Mathlib's `klFun` -/

section KLFun

variable {Ω : Type*} [Fintype Ω]

theorem mul_klFun_div (a b : ℝ) (hb : 0 < b) :
    b * _root_.InformationTheory.klFun (a / b) = a * Real.log (a / b) + b - a := by
  unfold _root_.InformationTheory.klFun
  field_simp

/-- With equal total masses, the divergence sum is the `klFun`-weighted sum of Mathlib's
Kullback–Leibler development. -/
theorem klSum_eq_sum_klFun (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hac : ∀ ω, 0 < p ω → 0 < q ω) (hmass : ∑ ω, q ω = ∑ ω, p ω) :
    klSum p q = ∑ ω, q ω * _root_.InformationTheory.klFun (p ω / q ω) := by
  have hterm : ∀ ω, q ω * _root_.InformationTheory.klFun (p ω / q ω) =
      p ω * Real.log (p ω / q ω) + (q ω - p ω) := by
    intro ω
    rcases (hq ω).lt_or_eq with hqpos | hqzero
    · rw [mul_klFun_div _ _ hqpos]
      ring
    · have hq0 : q ω = 0 := hqzero.symm
      have hp0 : p ω = 0 := le_antisymm (not_lt.1 fun h => (hac ω h).ne' hq0) (hp ω)
      rw [hq0, hp0]
      simp
  rw [Finset.sum_congr rfl fun ω _ => hterm ω, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hmass, sub_self, add_zero]
  rfl

/-- Gibbs' inequality re-derived from Mathlib's `klFun_nonneg`. -/
theorem klSum_nonneg_of_klFun (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hac : ∀ ω, 0 < p ω → 0 < q ω) (hmass : ∑ ω, q ω = ∑ ω, p ω) : 0 ≤ klSum p q := by
  rw [klSum_eq_sum_klFun p q hp hq hac hmass]
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hq ω) (_root_.InformationTheory.klFun_nonneg (div_nonneg (hp ω) (hq ω)))

end KLFun

/-! ## Shannon mutual information on `JointProb` -/

section ShannonMI

variable {Ω : Type*} [Fintype Ω]

/-- The joint law of two `Fin`-valued random variables as a `JointProb`. -/
noncomputable def jointProbOf {m n : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (f : Ω → Fin m) (h : Ω → Fin n) : JointProb m n :=
  ⟨law2 p f h, by
    constructor
    · exact fun x => pushforward_nonneg p hp _ x
    · unfold law2
      rw [sum_pushforward, hsum]⟩

theorem mutualInfo_eq_shannonMutualInformationNats {m n : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hsum : ∑ ω, p ω = 1) (f : Ω → Fin m) (h : Ω → Fin n) :
    mutualInfo p f h = JointProb.shannonMutualInformationNats (jointProbOf p hp hsum f h) := by
  unfold mutualInfo klSum klSumOn JointProb.shannonMutualInformationNats
  refine Finset.sum_congr rfl fun x _ => ?_
  have hprod : (JointProb.productOfMarginals (jointProbOf p hp hsum f h)).1 x =
      pushforward p f x.1 * pushforward p h x.2 := by
    show (JointProb.marginalLeft (jointProbOf p hp hsum f h)).1 x.1 *
      (JointProb.marginalRight (jointProbOf p hp hsum f h)).1 x.2 = _
    unfold JointProb.marginalLeft JointProb.marginalRight jointProbOf
    simp only
    rw [sum_law2_right p f h x.1, sum_law2_left p f h x.2]
  rw [hprod]
  rfl

end ShannonMI

end Mettapedia.InformationTheory.FiniteRV
