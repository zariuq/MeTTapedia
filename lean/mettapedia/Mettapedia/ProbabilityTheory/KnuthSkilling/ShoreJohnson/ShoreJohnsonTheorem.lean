import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnson
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonKL

/-!
# Shore–Johnson (1980): the Lean-friendly main theorem we use

Shore–Johnson's axioms SJ1–SJ4 are stated at the level of an *inference procedure*
(`prior` + `constraints` ↦ `posterior`).  Their full paper derives the cross-entropy/KL functional
as the unique objective (up to equivalence) compatible with those axioms.

Our project uses Shore–Johnson in two roles:

1. **System-independence ⇒ logarithm on probabilities.**
   In `.../ShoreJohnson.lean` we formalize a core lemma ("Dirac extraction") showing that an
   SJ4-style additivity over product distributions forces a multiplicative Cauchy equation for
   `q ↦ d(1,q)` on the probability domain `0 < q ≤ 1`, hence (with a measurability gate) a log form.

2. **KL uniqueness (up to scale) inside a ratio-form class.**
   In `.../ShoreJohnsonKL.lean` we formalize a Cauchy/log rigidity theorem on `(0,∞)` and apply it
   to show: if an "atom divergence" has the ratio form `d(w,u)=w*g(w/u)` and `g` satisfies a
   multiplicative Cauchy equation with a measurability gate, then `d` is a constant multiple of
   the KL atom `w*log(w/u)`.  We also give a counterexample showing regularity is necessary.

This file just packages those results under short names; it does **not** attempt to formalize the
full Shore–Johnson Theorem I appendix proof (which uses differentiability/variational arguments).

For a small glue lemma that connects the atom-level KL identity back to the project’s finite
`klDivergence` definition on `ProbDist` (Section 8 layer), see
`Mettapedia/ProbabilityTheory/KnuthSkilling/ShoreJohnsonBridge.lean`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem

open Real

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonKL
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonProof

/-! ## (SJ4 core) `q ↦ d(1,q)` is logarithmic on probabilities -/

theorem d_one_mul_cauchy_Ioc_of_SJ4
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ ≤ 1 → 0 < q₂ → q₂ ≤ 1 → d 1 (q₁ * q₂) = d 1 q₁ + d 1 q₂ :=
  dirac_extraction_cauchy_Ioc d hSJ.regularAtom hSJ.add_over_products

theorem d_one_eq_const_mul_log_of_SJ4
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d)
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = C * log q :=
  ShoreJohnson.d_one_eq_const_mul_log_of_measurable d hSJ hMeas

/-! ## (Ratio-form) KL is forced up to a constant multiple -/

/-- A witness that an atom divergence `d` is in "ratio form": `d(w,u)=w*g(w/u)` for `w,u>0`. -/
structure RatioForm (d : ℝ → ℝ → ℝ) where
  g : ℝ → ℝ
  eq_mul_g_div : ∀ w u : ℝ, 0 < w → 0 < u → d w u = w * g (w / u)

/-- Multiplicative Cauchy equation restricted to the domain `[1,∞)`. -/
def MulCauchyOnIci (g : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → g (x * y) = g x + g y

/-! ### Relationship between Cauchy domain variants -/

/-- `MulCauchyOnPos` (on `(0,∞)`) implies `MulCauchyOnIci` (on `[1,∞)`).
This is immediate since `[1,∞) ⊆ (0,∞)`. -/
theorem MulCauchyOnIci_of_MulCauchyOnPos (g : ℝ → ℝ) (h : MulCauchyOnPos g) :
    MulCauchyOnIci g := fun x y hx hy =>
  h x y (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hy)

/-- **Note on the converse**: `MulCauchyOnIci` does NOT imply `MulCauchyOnPos` in general.
A function could satisfy the Cauchy equation on `[1,∞)` but fail on `(0,1)`.

However, for functions arising from system independence (via Dirac extraction on probability
distributions), the Cauchy equation on `(0,1]` combined with `g(x) + g(1/x) = g(1)` extends
to the full `(0,∞)` domain. This reflection property is a consequence of how the Dirac
extraction argument uses both q and 1/q.

The full extension is not formalized here; we note that `MulCauchyOnPos` is the correct
hypothesis for the rigidity theorems (log uniqueness). -/

theorem ratioForm_mulCauchyOnIci_of_SJ4
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d) (h : RatioForm d) :
    MulCauchyOnIci h.g := by
  intro x y hx hy
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let q₁ : ℝ := 1 / x
  let q₂ : ℝ := 1 / y
  have hq₁_pos : 0 < q₁ := by simpa [q₁] using (one_div_pos.2 hx_pos)
  have hq₂_pos : 0 < q₂ := by simpa [q₂] using (one_div_pos.2 hy_pos)
  have hq₁_le1 : q₁ ≤ 1 := by
    have hle : q₁ * 1 ≤ q₁ * x := mul_le_mul_of_nonneg_left hx (le_of_lt hq₁_pos)
    have hq₁x : q₁ * x = 1 := by
      dsimp [q₁]
      simpa [div_eq_mul_inv, mul_assoc] using (one_div_mul_cancel hx_pos.ne')
    simpa [mul_one, hq₁x] using hle
  have hq₂_le1 : q₂ ≤ 1 := by
    have hle : q₂ * 1 ≤ q₂ * y := mul_le_mul_of_nonneg_left hy (le_of_lt hq₂_pos)
    have hq₂y : q₂ * y = 1 := by
      dsimp [q₂]
      simpa [div_eq_mul_inv, mul_assoc] using (one_div_mul_cancel hy_pos.ne')
    simpa [mul_one, hq₂y] using hle
  have hMul :=
    d_one_mul_cauchy_Ioc_of_SJ4 (d := d) hSJ q₁ q₂ hq₁_pos hq₁_le1 hq₂_pos hq₂_le1
  have h1 : d 1 (q₁ * q₂) = h.g (x * y) := by
    have hq_pos : 0 < q₁ * q₂ := mul_pos hq₁_pos hq₂_pos
    have hq : 1 / (q₁ * q₂) = x * y := by
      simp [q₁, q₂, mul_comm]
    simpa [hq] using h.eq_mul_g_div 1 (q₁ * q₂) one_pos hq_pos
  have h2 : d 1 q₁ = h.g x := by
    have hq : 1 / q₁ = x := by simp [q₁]
    simpa [hq] using h.eq_mul_g_div 1 q₁ one_pos hq₁_pos
  have h3 : d 1 q₂ = h.g y := by
    have hq : 1 / q₂ = y := by simp [q₂]
    simpa [hq] using h.eq_mul_g_div 1 q₂ one_pos hq₂_pos
  simpa [h1, h2, h3] using hMul

theorem ratioForm_eq_const_mul_klAtom_of_measurable
    (d : ℝ → ℝ → ℝ) (h : RatioForm d)
    (hgMul : MulCauchyOnPos h.g)
    (hgMeas : Measurable h.g) :
    ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u := by
  exact ratioForm_eq_const_mul_klAtom d h.g h.eq_mul_g_div hgMul hgMeas

/-! ## Counterexample: without regularity, KL uniqueness fails -/

theorem exists_ratioForm_mulCauchyOnPos_not_const_mul_klAtom :
    ∃ (d : ℝ → ℝ → ℝ) (g : ℝ → ℝ),
      (∀ w u : ℝ, 0 < w → 0 < u → d w u = w * g (w / u)) ∧
      MulCauchyOnPos g ∧
      ¬ ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u :=
  ShoreJohnsonKL.exists_ratioForm_mulCauchyOnPos_not_const_mul_klAtom

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem
