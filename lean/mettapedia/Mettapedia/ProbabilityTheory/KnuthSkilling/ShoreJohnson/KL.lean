import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.CauchyPathology

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shore–Johnson: functional-equation uniqueness for KL / cross-entropy

This file packages the **functional-equation** core that drives Shore–Johnson (1980):

* If a function on positive reals satisfies a multiplicative Cauchy equation
    `g(xy) = g(x) + g(y)` (for `x,y>0`)
  then, **with an explicit regularity gate** (Borel measurability),
  it must be logarithmic: `g(x) = C * log x`.

This is the same rigidity phenomenon used in K&S Appendix C (our `Variational/Main.lean`),
and it explains why any attempt at “KL uniqueness” must make a regularity hypothesis explicit:
without it, Hamel-basis pathologies exist.

We also include an explicit counterexample (already formalized in `CauchyPathology.lean`):
there exists a (non-regular) multiplicative-additive solution not equal to `C * log`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL

open Real

open Mettapedia.ProbabilityTheory.KnuthSkilling.Variational

/-! ## Multiplicative Cauchy on `(0,∞)` ⇒ logarithm (measurable gate) -/

/-- A multiplicative-additive functional equation on positive reals. -/
def MulCauchyOnPos (g : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x + g y

/-- **Main rigidity lemma**: measurable multiplicative-additive functions are logarithmic. -/
theorem mulCauchyOnPos_eq_const_mul_log
    (g : ℝ → ℝ) (hg : MulCauchyOnPos g) (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x := by
  -- Log-coordinates: ψ(t) := g(exp t) is additive on ℝ.
  let ψ : ℝ → ℝ := transformToAdditive g

  have hψ_add : CauchyEquation ψ :=
    cauchyEquation_of_multiplicative g hg

  have hψ_meas : Measurable ψ := by
    -- `t ↦ exp t` is measurable and `g` is measurable.
    exact hMeas.comp Real.continuous_exp.measurable

  obtain ⟨C, hC⟩ := cauchyEquation_measurable_linear ψ hψ_add hψ_meas

  refine ⟨C, ?_⟩
  intro x hx
  -- Evaluate `hC` at `log x`.
  have hx' : Real.exp (Real.log x) = x := Real.exp_log hx
  have : ψ (Real.log x) = C * Real.log x := hC (Real.log x)
  -- Unfold `ψ` and rewrite `exp(log x) = x`.
  dsimp [ψ, transformToAdditive] at this
  simpa [hx'] using this

/-! ## Consequence: ratio-form "atom divergences" are KL up to scale -/

/-- The KL-style atom `w ↦ u ↦ w * log (w/u)` (defined on `w,u > 0`).

**Boundary behavior (Lean conventions)**:
- `klAtom 0 u = 0` for any `u` (since `0 * anything = 0`)
- `klAtom w 0 = w * log(w/0) = w * log 0 = w * 0 = 0` (Lean: `x/0 = 0`, `log 0 = 0`)

The first convention (`0 log 0 = 0`) matches the standard KL divergence convention from
information theory. The second is a "junk value" that only matters when the reference
distribution has zeros (violating absolute continuity).

For the main theorems, we restrict to `w > 0` and `u > 0` where the definition is unambiguous. -/
noncomputable def klAtom (w u : ℝ) : ℝ :=
  w * Real.log (w / u)

/-! ### Boundary lemmas for `klAtom` -/

@[simp] lemma klAtom_zero_left (u : ℝ) : klAtom 0 u = 0 := by simp [klAtom]

lemma klAtom_zero_right (w : ℝ) : klAtom w 0 = 0 := by simp [klAtom, div_zero, Real.log_zero]

lemma klAtom_eq_mul_log_div (w u : ℝ) : klAtom w u = w * Real.log (w / u) := rfl

/-- On the positive domain, `klAtom` is well-behaved: `klAtom w u = w * log(w/u)`.
The hypotheses `hw` and `hu` are for documentation; the identity holds definitionally. -/
lemma klAtom_pos_pos (w u : ℝ) (_hw : 0 < w) (_hu : 0 < u) :
    klAtom w u = w * Real.log (w / u) := rfl

/-- If an atom divergence has the ratio form `d(w,u) = w * g(w/u)`, and `g` satisfies the
multiplicative Cauchy equation with a measurability gate, then `d` is a constant multiple of the
KL atom. -/
theorem ratioForm_eq_const_mul_klAtom
    (d : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hd : ∀ w u : ℝ, 0 < w → 0 < u → d w u = w * g (w / u))
    (hgMul : MulCauchyOnPos g)
    (hgMeas : Measurable g) :
    ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u := by
  rcases mulCauchyOnPos_eq_const_mul_log (g := g) hgMul hgMeas with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro w u hw hu
  have hwu : 0 < w / u := div_pos hw hu
  calc
    d w u = w * g (w / u) := hd w u hw hu
    _ = w * (C * Real.log (w / u)) := by rw [hC (w / u) hwu]
    _ = C * (w * Real.log (w / u)) := by ring
    _ = C * klAtom w u := by rfl

/-! ## Counterexample: without regularity, uniqueness fails -/

open Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples

/-- There exists a multiplicative-additive `g` on `(0,∞)` that is **not** of the form `C * log x`. -/
theorem exists_mulCauchyOnPos_not_const_mul_log :
    ∃ g : ℝ → ℝ, MulCauchyOnPos g ∧ ¬ ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x := by
  refine ⟨Hprime, ?_, ?_⟩
  · intro x y hx hy
    simpa using Hprime_mul x y hx hy
  · intro h
    rcases h with ⟨C, hC⟩
    -- This contradicts the stronger statement `Hprime` is not `B + C log`.
    have : ∃ (B C' : ℝ), ∀ m : ℝ, 0 < m → Hprime m = B + C' * Real.log m := by
      refine ⟨0, C, ?_⟩
      intro m hm
      simpa using (hC m hm)
    exact Hprime_not_B_add_C_log this

/-- A concrete “ratio-form atom divergence” counterexample: without the measurability gate,
the multiplicative Cauchy equation does **not** force the KL atom. -/
theorem exists_ratioForm_mulCauchyOnPos_not_const_mul_klAtom :
    ∃ (d : ℝ → ℝ → ℝ) (g : ℝ → ℝ),
      (∀ w u : ℝ, 0 < w → 0 < u → d w u = w * g (w / u)) ∧
      MulCauchyOnPos g ∧
      ¬ ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u := by
  refine ⟨fun w u => w * Hprime (w / u), Hprime, ?_, ?_, ?_⟩
  · intro w u _ _
    rfl
  · intro x y hx hy
    simpa using Hprime_mul x y hx hy
  · intro h
    rcases h with ⟨C, hC⟩
    have hg : ∀ x : ℝ, 0 < x → Hprime x = C * Real.log x := by
      intro x hx
      -- Specialize the supposed KL identity to `w=1`, `u=1/x`.
      have hxinv : 0 < (1 / x : ℝ) := one_div_pos.2 hx
      have hspec := hC 1 (1 / x) one_pos hxinv
      -- Left: `d 1 (1/x) = Hprime x`.
      -- Right: `C * klAtom 1 (1/x) = C * log x`.
      simpa [klAtom, div_eq_mul_inv] using hspec
    -- Turn `hg` into the stronger statement excluded by `Hprime_not_B_add_C_log`.
    have : ∃ (B C' : ℝ), ∀ m : ℝ, 0 < m → Hprime m = B + C' * Real.log m := by
      refine ⟨0, C, ?_⟩
      intro m hm
      simpa using (hg m hm)
    exact Hprime_not_B_add_C_log this

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL
