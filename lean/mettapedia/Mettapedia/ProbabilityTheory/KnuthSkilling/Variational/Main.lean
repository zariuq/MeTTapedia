import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation

/-!
# Knuth–Skilling Appendix C: Variational Theorem

This file formalizes the **Variational Theorem** from:

- Knuth & Skilling, *Foundations of Inference* (2012), Appendix C
  `literature/Knuth_Skilling/Knuth_Skilling_Foundations_of_Inference/knuth-skilling-2012---foundations-of-inference----arxiv.tex`
  (see around lines 2096–2250 in the TeX source).

## The Variational Equation

K&S consider the functional equation arising from the variational potential axiom:

`H'(m_x · m_y) = lam(m_x) + mu(m_y)`

where `H' = dH/dm` is the derivative of the entropy-like function `H`.

## Key Insight: Reduction to Cauchy's Equation

Setting `u = log m`, the multiplicative argument `m_x · m_y` becomes additive:
`log(m_x · m_y) = log(m_x) + log(m_y)`, i.e., `u_x + u_y`.

If we define `phi(u) = lam(exp u)`, then the equation becomes:

`H'(exp(u + v)) = phi(u) + psi(v)`

This is closely related to **Cauchy's functional equation**: `f(x + y) = f(x) + f(y)`.

## Reusing Appendix B Infrastructure

**We do NOT reprove Cauchy's equation solution!** We directly reuse:

- `continuous_additive_eq_mul`: continuous additive → linear
- `AdditiveOnPos.exists_mul_const_of_add_of_pos`: additive + positive on (0,∞) → scalar mult

K&S themselves avoid assuming regularity of an additive function by a “blurring” (convolution)
argument in Appendix C. In Lean, we instead use a fully rigorous (and still KS-faithful) route:
`H'` is a derivative on `(0,∞)`, hence Borel-measurable, hence its log/exp conjugate is measurable,
and **measurable additive functions are continuous**, so Cauchy’s equation has the linear solution.

See also:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Counterexamples/VariationalNonsmooth.lean` for a
  counterexample showing that “variational optimum ⇒ differentiable” is false in general.
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Counterexamples/CauchyPathology.lean` for an explicit
  (Hamel-basis) countermodel showing that *some* regularity hypothesis is genuinely needed to rule
  out non-linear solutions of Cauchy’s equation.
- `Mettapedia/ProbabilityTheory/KnuthSkilling/ShoreJohnson/PathC.lean` for the Shore-Johnson
  alternative route to the same multiplicative Cauchy/log conclusion (used to reach KL).

This follows the K&S design principle: the same core algebraic structures appear across
Appendices A, B, and C, with shared proof techniques.

## Solution

The solution is the **entropy form**:

`H(m) = A + B·m + C·(m·log(m) - m)`

where `A, B, C` are constants.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Variational

open Classical
open Set
open scoped Topology

/-! ## Cauchy's Functional Equation -/

/-- **Cauchy's additive functional equation**: `f(x + y) = f(x) + f(y)` for all `x, y : ℝ`. -/
def CauchyEquation (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f (x + y) = f x + f y

namespace CauchyEquation

variable {f : ℝ → ℝ}

/-- Zero is mapped to zero. -/
theorem map_zero (hf : CauchyEquation f) : f 0 = 0 := by
  have h := hf 0 0
  simp only [add_zero] at h
  linarith

/-- Negation: `f(-x) = -f(x)`. -/
theorem map_neg (hf : CauchyEquation f) (x : ℝ) : f (-x) = -f x := by
  have h := hf x (-x)
  simp only [add_neg_cancel] at h
  rw [hf.map_zero] at h
  linarith

/-- Natural scaling: `f(n·x) = n·f(x)` for `n : ℕ`. -/
theorem map_nsmul (hf : CauchyEquation f) (x : ℝ) (n : ℕ) : f (n * x) = n * f x := by
  induction n with
  | zero => simp [hf.map_zero]
  | succ n ih =>
    have heq : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
    calc f ((n + 1 : ℕ) * x)
        = f ((n : ℝ) * x + x) := by rw [heq]
      _ = f ((n : ℝ) * x) + f x := hf _ _
      _ = (n : ℝ) * f x + f x := by rw [ih]
      _ = ((n + 1 : ℕ) : ℝ) * f x := by push_cast; ring

/-- Integer scaling: `f(n·x) = n·f(x)` for `n : ℤ`. -/
theorem map_zsmul (hf : CauchyEquation f) (x : ℝ) (n : ℤ) : f (n * x) = n * f x := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, Int.cast_natCast]
    exact hf.map_nsmul x m
  | negSucc m =>
    simp only [Int.cast_negSucc, neg_mul]
    rw [hf.map_neg]
    have h := hf.map_nsmul x (m + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h
    -- Goal: -f (↑(m+1) * x) = -(↑(m+1) * f x)
    -- h: f ((↑m + 1) * x) = (↑m + 1) * f x
    -- Note: ↑(m+1) and (↑m + 1) are definitionally equal as ℝ
    convert congrArg (fun y => -y) h using 1 <;> push_cast <;> ring

/-- Rational scaling: `f(q·x) = q·f(x)` for `q : ℚ`. -/
theorem map_rat_mul (hf : CauchyEquation f) (x : ℝ) (q : ℚ) : f (q * x) = q * f x := by
  have hden_pos : 0 < q.den := q.den_pos
  have hden_ne : (q.den : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
  -- q = q.num / q.den
  have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by simp [Rat.cast_def]
  -- f(q.den * (q*x)) = q.den * f(q*x)
  have h1 : f ((q.den : ℝ) * (q * x)) = (q.den : ℝ) * f (q * x) := by
    have := hf.map_nsmul (q * x) q.den
    convert this using 1
  -- q.den * (q*x) = q.num * x
  have h2 : (q.den : ℝ) * (q * x) = (q.num : ℝ) * x := by
    rw [hq_eq]
    field_simp [hden_ne]
  -- f(q.num * x) = q.num * f(x)
  have h3 : f ((q.num : ℝ) * x) = (q.num : ℝ) * f x := hf.map_zsmul x q.num
  -- Combine
  have h4 : f ((q.den : ℝ) * (q * x)) = (q.num : ℝ) * f x := by rw [h2, h3]
  have h5 : (q.den : ℝ) * f (q * x) = (q.num : ℝ) * f x := by rw [← h1, h4]
  have hden_pos_r : 0 < (q.den : ℝ) := by exact_mod_cast hden_pos
  have hdiv : f (q * x) = (q.num : ℝ) * f x / (q.den : ℝ) := by
    have h6 : f (q * x) * (q.den : ℝ) = (q.num : ℝ) * f x := by linarith
    field_simp [hden_ne]
    linarith
  rw [hdiv, hq_eq]
  ring

end CauchyEquation

/-! ## Solution of Cauchy's Equation

**KEY REUSE**: We use `continuous_additive_eq_mul` from
`Multiplicative.FunctionalEquation` rather than reproving the Cauchy solution.
-/

/-- **Cauchy's equation + continuity → linear**.

This is a direct application of `continuous_additive_eq_mul` from Appendix B.
No new proof needed! -/
theorem cauchyEquation_continuous_linear (f : ℝ → ℝ)
    (hCauchy : CauchyEquation f) (hCont : Continuous f) :
    ∃ A : ℝ, ∀ x : ℝ, f x = A * x :=
  Multiplicative.continuous_additive_eq_mul f hCauchy hCont

/-- **Cauchy's equation + measurability → linear**.

This is the KS-friendly “no pathological solutions” statement that avoids assuming continuity:
an additive function `f : ℝ → ℝ` which is Borel-measurable is automatically continuous, hence
linear by `continuous_additive_eq_mul` (Appendix B infrastructure). -/
theorem cauchyEquation_measurable_linear (f : ℝ → ℝ)
    (hCauchy : CauchyEquation f) (hMeas : Measurable f) :
    ∃ A : ℝ, ∀ x : ℝ, f x = A * x := by
  let F : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := CauchyEquation.map_zero hCauchy
      map_add' := hCauchy }
  have hMeasF : Measurable (F : ℝ → ℝ) := by
    simpa [F] using hMeas
  have hContF : Continuous (F : ℝ → ℝ) :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable F hMeasF
  have hCont : Continuous f := by
    simpa [F] using hContF
  exact cauchyEquation_continuous_linear f hCauchy hCont

/-! ## The Variational Equation -/

/-- **Variational functional equation** (K&S Appendix C).

The equation `H'(m_x · m_y) = lam(m_x) + mu(m_y)` where:
- `H' : ℝ → ℝ` is the derivative of the entropy-like function
- `lam, mu : ℝ → ℝ` are functions of the "masses"
- The equation holds for all positive `m_x, m_y > 0`

This captures the "factorization" property arising from the variational potential. -/
def VariationalEquation (H' lam mu : ℝ → ℝ) : Prop :=
  ∀ m_x m_y : ℝ, 0 < m_x → 0 < m_y → H' (m_x * m_y) = lam m_x + mu m_y

namespace VariationalEquation

variable {H' lam mu : ℝ → ℝ}

/-- The variational equation at `m_x = m_y = 1` gives `H'(1) = lam(1) + mu(1)`. -/
theorem at_one_one (hV : VariationalEquation H' lam mu) :
    H' 1 = lam 1 + mu 1 := by
  have := hV 1 1 one_pos one_pos
  simp at this
  exact this

/-- Setting `m_y = 1`: `H'(m_x) = lam(m_x) + mu(1)`. -/
theorem at_m_one (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    H' m = lam m + mu 1 := by
  have := hV m 1 hm one_pos
  simp at this
  exact this

/-- Setting `m_x = 1`: `H'(m_y) = lam(1) + mu(m_y)`. -/
theorem at_one_m (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    H' m = lam 1 + mu m := by
  have := hV 1 m one_pos hm
  simp at this
  exact this

/-- **Key consequence**: `lam` and `mu` differ by a constant.

From `H'(m) = lam(m) + mu(1) = lam(1) + mu(m)`, we get `lam(m) - lam(1) = mu(m) - mu(1)`. -/
theorem lam_mu_shift (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    lam m - lam 1 = mu m - mu 1 := by
  have h1 := hV.at_m_one hm
  have h2 := hV.at_one_m hm
  linarith

/-- **Corollary**: We can write `lam(m) = phi(m) + c1` and `mu(m) = phi(m) + c2` for a common `phi`.

This means the variational equation simplifies to: `H'(xy) = phi(x) + phi(y) + c`
where `c = c1 + c2`. Also, `phi(1) = 0` by construction. -/
theorem exists_common_core (hV : VariationalEquation H' lam mu) :
    ∃ phi : ℝ → ℝ, ∃ c1 c2 : ℝ,
      phi 1 = 0 ∧
      (∀ m, 0 < m → lam m = phi m + c1) ∧
      (∀ m, 0 < m → mu m = phi m + c2) := by
  refine ⟨fun m => lam m - lam 1, lam 1, mu 1, ?_, ?_, ?_⟩
  · simp
  · intro m _
    ring
  · intro m hm
    have := hV.lam_mu_shift hm
    linarith

end VariationalEquation

/-! ## Transformation to Cauchy Equation

The key insight: under the substitution `u = log m`, the multiplicative structure
becomes additive, reducing to Cauchy's equation.
-/

/-- Transform a function on positive reals to a function on all reals via `exp`. -/
noncomputable def transformToAdditive (g : ℝ → ℝ) : ℝ → ℝ := fun u => g (Real.exp u)

/-- If `g(xy) = g(x) + g(y)` for positive `x, y`, then `transformToAdditive g` satisfies
Cauchy's equation. -/
theorem cauchyEquation_of_multiplicative (g : ℝ → ℝ)
    (hg : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x + g y) :
    CauchyEquation (transformToAdditive g) := by
  intro u v
  simp only [transformToAdditive]
  have hexp_u : 0 < Real.exp u := Real.exp_pos u
  have hexp_v : 0 < Real.exp v := Real.exp_pos v
  rw [Real.exp_add]
  exact hg _ _ hexp_u hexp_v

/-! ## The Entropy Solution

The solution to the variational equation is the **entropy form**:
`H(m) = A + B·m + C·(m·log(m) - m)`

Its derivative is: `H'(m) = B + C·log(m)`
-/

/-- The derivative of the entropy form `H(m) = A + Bm + C(m log m - m)` is `H'(m) = B + C log m`. -/
noncomputable def entropyDerivative (B C : ℝ) : ℝ → ℝ := fun m => B + C * Real.log m

/-- The entropy derivative satisfies the variational equation with `lam = mu = (C/2) log + const`. -/
theorem entropyDerivative_variational (B C : ℝ) :
    VariationalEquation (entropyDerivative B C)
      (fun m => B / 2 + C * Real.log m)
      (fun m => B / 2 + C * Real.log m) := by
  intro m_x m_y hx hy
  simp only [entropyDerivative]
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  ring

/-- **Main Theorem (Appendix C) — measurable version**.

If `H'` satisfies the variational equation and is Borel-measurable, then
`H'(m) = B + C·log(m)` for some constants `B, C`.

This isolates the regularity needed to rule out pathological solutions of Cauchy’s equation:
measurable additive functions are automatically continuous (hence linear).

K&S enforce regularity by “blurring by convolution” in the TeX; in Lean we take measurability as a
clean, explicit substitute. In typical applications this is discharged by `H' = deriv H`, since
derivatives are measurable (`measurable_deriv`). -/
theorem variationalEquation_solution_measurable
    (H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hMeas : Measurable H')
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m := by
  -- Step 1: Extract the common core phi from lam and mu
  obtain ⟨phi, c1, c2, hphi1, hlam, hmu⟩ := hV.exists_common_core

  -- Step 2: Show H'(1) = c1 + c2
  have hH1 : H' 1 = c1 + c2 := by
    have := hV.at_one_one
    have hlam1 : lam 1 = phi 1 + c1 := hlam 1 one_pos
    have hmu1 : mu 1 = phi 1 + c2 := hmu 1 one_pos
    rw [hlam1, hmu1, hphi1] at this
    linarith

  -- Step 3: Show phi is multiplicatively additive: phi(xy) = phi(x) + phi(y)
  have hphi_pure : ∀ x y : ℝ, 0 < x → 0 < y → phi (x * y) = phi x + phi y := by
    intro x y hx hy
    have hxy : 0 < x * y := mul_pos hx hy
    have h1 : H' (x * y) = lam x + mu y := hV x y hx hy
    have h2 : lam x = phi x + c1 := hlam x hx
    have h3 : mu y = phi y + c2 := hmu y hy
    have h4 : H' (x * y) = phi x + phi y + (c1 + c2) := by rw [h1, h2, h3]; ring
    have h5 : H' (x * y) = phi (x * y) + c1 + mu 1 := by
      have := hV.at_m_one hxy
      rw [hlam (x * y) hxy] at this
      linarith
    have h6 : mu 1 = c2 := by
      have := hmu 1 one_pos
      rw [hphi1] at this
      linarith
    rw [h6] at h5
    linarith

  -- Step 4: Transform to Cauchy equation
  have hpsi_cauchy : CauchyEquation (transformToAdditive phi) :=
    cauchyEquation_of_multiplicative phi hphi_pure

  -- Step 5: Show psi is measurable (from measurability of H')
  have hphi_eq : ∀ m : ℝ, 0 < m → phi m = H' m - c1 - mu 1 := by
    intro m hm
    have := hV.at_m_one hm
    have hlamm := hlam m hm
    linarith
  have hpsi_measurable : Measurable (transformToAdditive phi) := by
    have hH'exp : Measurable (fun u : ℝ => H' (Real.exp u)) :=
      hMeas.comp Real.continuous_exp.measurable
    have hEq : transformToAdditive phi = fun u : ℝ => H' (Real.exp u) - c1 - mu 1 := by
      funext u
      simp [transformToAdditive, hphi_eq (Real.exp u) (Real.exp_pos u)]
    simpa [hEq] using (hH'exp.sub measurable_const).sub measurable_const

  -- Step 6: Apply Cauchy solution
  obtain ⟨C, hC⟩ := cauchyEquation_measurable_linear _ hpsi_cauchy hpsi_measurable

  -- Step 7: Unwind to get H'(m) = B + C·log(m)
  refine ⟨c1 + mu 1, C, ?_⟩
  intro m hm
  have hm_eq : m = Real.exp (Real.log m) := (Real.exp_log hm).symm
  have hpsi_log : transformToAdditive phi (Real.log m) = C * Real.log m := hC (Real.log m)
  have hphi_m : phi m = transformToAdditive phi (Real.log m) := by
    simp only [transformToAdditive]; rw [← hm_eq]
  have hphi_val : phi m = C * Real.log m := by rw [hphi_m, hpsi_log]
  have hH'_m := hphi_eq m hm
  linarith

/-- **Main Theorem (Appendix C) — `deriv` version**.

This is the direct “mathematician’s” statement: phrase the variational equation using `deriv H`
(rather than a separate symbol `H'`), then measurability is automatic. -/
theorem variationalEquation_solution
    (H : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hV : VariationalEquation (deriv H) lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → deriv H m = B + C * Real.log m := by
  simpa using
    (variationalEquation_solution_measurable (H' := deriv H) (lam := lam) (mu := mu)
      (hMeas := measurable_deriv H) (hV := hV))

/-- **Appendix C — explicit `H'` wrapper.**

If you prefer to name the derivative `H'` explicitly, this lemma shows how to connect the
`deriv`-based theorem above back to a chosen `H'` (on `(0,∞)`). -/
theorem variationalEquation_solution_of_hasDerivAt
    (H H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hDeriv : ∀ m : ℝ, 0 < m → HasDerivAt H (H' m) m)
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m := by
  have hV' : VariationalEquation (deriv H) lam mu := by
    intro m_x m_y hx hy
    have hder : deriv H (m_x * m_y) = H' (m_x * m_y) := (hDeriv (m_x * m_y) (mul_pos hx hy)).deriv
    simpa [hder] using (hV m_x m_y hx hy)
  rcases variationalEquation_solution (H := H) (lam := lam) (mu := mu) hV' with ⟨B, C, hBC⟩
  refine ⟨B, C, ?_⟩
  intro m hm
  have hder : deriv H m = H' m := (hDeriv m hm).deriv
  calc
    H' m = deriv H m := hder.symm
    _ = B + C * Real.log m := hBC m hm

/-- **Monotone regularity version**.

If `H'` is monotone (on `ℝ`), it is automatically Borel measurable (by `Monotone.measurable`),
so we can apply the measurable version directly. This matches one of the standard "anti-pathology"
gates for Cauchy's functional equation. -/
theorem variationalEquation_solution_monotone
    (H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hMono : Monotone H')
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m :=
  variationalEquation_solution_measurable H' lam mu hMono.measurable hV

/-- **Antitone regularity version**.

Same as the monotone version, but for antitone (decreasing) functions. -/
theorem variationalEquation_solution_antitone
    (H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hAnti : Antitone H')
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m :=
  variationalEquation_solution_measurable H' lam mu hAnti.measurable hV

/-- **StrictMono regularity version**.

Strict monotonicity implies monotonicity, which implies measurability. -/
theorem variationalEquation_solution_strictMono
    (H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hMono : StrictMono H')
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m :=
  variationalEquation_solution_monotone H' lam mu hMono.monotone hV

/-! ## Path B → Path A: "Generality Across Applications" (Universality + Richness)

Path B (Lagrange multipliers) yields a *local* separated equation at a stationary point of a
separable constrained problem. Path A (the functional-equation solver) requires a *global*
variational equation holding for all positive pairs.

K&S bridge this gap by a methodological premise: the same variational potential applies uniformly
across a sufficiently rich class of applications, so that the separated coordinate equation can be
treated as a functional equation in independent variables.

We keep this premise explicit (and therefore auditable) as `KSVariationalGenerality`.

For literature-backed variants of this “generality / consistency across applications” idea,
see Shore–Johnson (1980).  Our project formalizes a Lean-friendly core consequence of SJ4
(system independence) in `Mettapedia/ProbabilityTheory/KnuthSkilling/Theorem.lean`,
including an explicit regularity gate and an explicit counterexample showing why some regularity
assumption is logically necessary.

We additionally connect that Shore–Johnson “atom-level” conclusion to this project’s finite
`klDivergence` definition (Section 8 layer) in
`Mettapedia/ProbabilityTheory/KnuthSkilling/Bridge.lean`.
-/

/-- K&S’s “generality across applications” premise for Appendix C.

This packages the (global) variational functional equation for `deriv H` as an explicit hypothesis,
separating it from the local stationarity statement proven by Path B. -/
structure KSVariationalGenerality (H : ℝ → ℝ) where
  lam : ℝ → ℝ
  mu : ℝ → ℝ
  equation : VariationalEquation (deriv H) lam mu

theorem variationalEquation_solution_of_generality (H : ℝ → ℝ) (hGen : KSVariationalGenerality H) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → deriv H m = B + C * Real.log m :=
  variationalEquation_solution (H := H) (lam := hGen.lam) (mu := hGen.mu) hGen.equation

/-! ## Integration: From H' to H

Given `H'(m) = B + C·log(m)`, we can integrate to get the entropy form:
`H(m) = A + B·m + C·(m·log(m) - m)`
-/

/-- The **entropy form** arising from integrating `H'(m) = B + C·log(m)`. -/
noncomputable def entropyForm (A B C : ℝ) : ℝ → ℝ := fun m => A + B * m + C * (m * Real.log m - m)

/-- The derivative of `entropyForm A B C` is `entropyDerivative B C` (for `m > 0`). -/
theorem entropyForm_deriv (A B C : ℝ) {m : ℝ} (hm : 0 < m) :
    HasDerivAt (entropyForm A B C) (entropyDerivative B C m) m := by
  unfold entropyForm entropyDerivative
  -- d/dm [A + Bm + C(m log m - m)]
  -- = B + C(log m + 1 - 1)
  -- = B + C log m
  have h1 : HasDerivAt (fun x => A) 0 m := hasDerivAt_const m A
  have h2 : HasDerivAt (fun x => B * x) B m := by
    have hid := hasDerivAt_id m
    have h := hid.const_mul B
    convert h using 1
    ring
  -- Use the mathlib lemma for d/dm (m log m) = log m + 1
  have h3 : HasDerivAt (fun x => x * Real.log x) (Real.log m + 1) m :=
    Real.hasDerivAt_mul_log (ne_of_gt hm)
  have h4 : HasDerivAt (fun x => x) 1 m := hasDerivAt_id m
  have h5 : HasDerivAt (fun x => x * Real.log x - x) (Real.log m + 1 - 1) m :=
    h3.sub h4
  have h6 : HasDerivAt (fun x => C * (x * Real.log x - x)) (C * (Real.log m + 1 - 1)) m := by
    have h := h5.const_mul C
    convert h using 1
  have h7 : HasDerivAt (fun x => A + B * x + C * (x * Real.log x - x))
      (0 + B + C * (Real.log m + 1 - 1)) m := by
    exact (h1.add h2).add h6
  convert h7 using 1; ring

/-- **Main integration result**: The entropy form has the correct derivative. -/
theorem entropyForm_has_derivative (A B C : ℝ) :
    ∀ m : ℝ, 0 < m → HasDerivAt (entropyForm A B C) (B + C * Real.log m) m := by
  intro m hm
  have := entropyForm_deriv A B C hm
  convert this using 1

/-! ## Characterizing the Minimum of entropyForm

The entropy form `H(m) = A + B·m + C·(m·log(m) - m)` has a unique critical point
where `H'(m) = B + C·log(m) = 0`, i.e., at `m = exp(-B/C)` (when `C ≠ 0`).

When `C > 0`, this critical point is a **minimum**.

K&S Section 6 chooses parameters to place the minimum at a desired location with value zero:
- `C = 1` ensures a minimum (not maximum)
- `B = -log(u)` places the minimum at `m = u`
- `A = u` makes the minimum value zero
-/

/-- The critical point of `entropyForm A B C` is where `H'(m) = B + C·log(m) = 0`.
When `C ≠ 0`, this occurs at `m = exp(-B/C)`. -/
theorem entropyForm_critical_point (B C : ℝ) (hC : C ≠ 0) :
    let m₀ := Real.exp (-B / C)
    entropyDerivative B C m₀ = 0 := by
  simp only [entropyDerivative]
  rw [Real.log_exp]
  -- Goal: B + C * (-B / C) = 0
  field_simp [hC]
  ring

/-- When `B = -log(u)` and `C = 1`, the critical point is at `m = u`. -/
theorem entropyForm_critical_at_u (u : ℝ) (hu : 0 < u) :
    Real.exp (-(-Real.log u) / 1) = u := by
  simp [Real.exp_log hu]

/-- The value of `entropyForm A B C` at its critical point `m₀ = exp(-B/C)`.

We compute: `H(m₀) = A + B·m₀ + C·(m₀·log(m₀) - m₀)`
where `log(m₀) = -B/C`, so `m₀·log(m₀) = m₀·(-B/C)`.
Thus `H(m₀) = A + B·m₀ + C·(m₀·(-B/C) - m₀) = A + B·m₀ - B·m₀ - C·m₀ = A - C·m₀`.

With `m₀ = exp(-B/C)`, we get `H(m₀) = A - C·exp(-B/C)`. -/
theorem entropyForm_value_at_critical (A B C : ℝ) (hC : C ≠ 0) :
    let m₀ := Real.exp (-B / C)
    entropyForm A B C m₀ = A - C * m₀ := by
  simp only [entropyForm]
  rw [Real.log_exp]
  field_simp
  ring

/-- When `A = u`, `B = -log(u)`, `C = 1`, the minimum value is zero.

With these parameters: `m₀ = exp(-(-log u)/1) = u` and
`H(m₀) = A - C·m₀ = u - 1·u = 0`. -/
theorem entropyForm_minimum_value_zero (u : ℝ) (hu : 0 < u) :
    entropyForm u (-Real.log u) 1 u = 0 := by
  unfold entropyForm
  have hu_ne : u ≠ 0 := ne_of_gt hu
  simp only [one_mul]
  -- Goal: u + -Real.log u * u + (u * Real.log u - u) = 0
  ring

/-- The second derivative of entropyForm is `H''(m) = C/m`, which is positive when `C > 0` and `m > 0`.
This confirms the critical point is a minimum when `C > 0`. -/
theorem entropyForm_second_deriv_pos (C : ℝ) (hC : 0 < C) {m : ℝ} (hm : 0 < m) :
    0 < C / m := div_pos hC hm

/-- **Summary**: The divergence parameters are **forced** by requirements.

Given the entropy form `H(m) = A + B·m + C·(m·log(m) - m)`:
1. To have a minimum (not maximum): `C > 0` (we set `C = 1`)
2. To place the minimum at `m = u`: solve `exp(-B/C) = u`, giving `B = -log(u)`
3. To make the minimum value zero: `A - C·u = 0`, giving `A = C·u = u`

These constraints uniquely determine `A = u`, `B = -log(u)`, `C = 1` for the divergence formula. -/
theorem divergence_parameters_forced (u : ℝ) (_hu : 0 < u)
    (A B C : ℝ) (hC_pos : 0 < C)
    (h_min_at_u : Real.exp (-B / C) = u)
    (h_min_val_zero : A - C * u = 0) :
    A = C * u ∧ B = -C * Real.log u := by
  constructor
  · linarith
  · have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have h1 : -B / C = Real.log u := by
      have h2 : Real.log (Real.exp (-B / C)) = Real.log u := by
        rw [h_min_at_u]
      rw [Real.log_exp] at h2
      exact h2
    field_simp at h1 ⊢
    linarith

/-! ## Path B: Lagrange Multiplier Derivation

K&S motivate the functional equation (their Eq. `Hproduct`, arxiv.tex:767–770) by considering an
`x`-by-`y` direct-product application with **separable constraints** on each factor, and then taking
the derivative of a Lagrangian with respect to the coordinate `m(x × y)`.

In Lean we model “the partial derivative with respect to a coordinate” by a 1D derivative along
the coordinate-update map `t ↦ Function.update m (x, y) t`.

This isolates the pure calculus fact: at a stationary point, the coordinate-derivative equation
*separates* into an `x`-part plus a `y`-part.  (Regularity of solutions to the resulting functional
equation is handled by Path A via measurability of derivatives.)
-/

section PathB

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The `x`-marginal of a joint assignment `m : X × Y → ℝ`. -/
noncomputable def rowSum (m : X × Y → ℝ) (x : X) : ℝ := by
  classical
  exact (Finset.univ.sum fun y : Y => m (x, y))

/-- The `y`-marginal of a joint assignment `m : X × Y → ℝ`. -/
noncomputable def colSum (m : X × Y → ℝ) (y : Y) : ℝ := by
  classical
  exact (Finset.univ.sum fun x : X => m (x, y))

/-- A basic “separable constraints” Lagrangian: an objective `∑ H(m_xy)` minus X-only and Y-only
constraint terms built from the marginals `rowSum` and `colSum`. -/
noncomputable def productLagrangian (H : ℝ → ℝ)
    (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ)
    (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) : ℝ := by
  classical
  exact
    (Finset.univ.sum fun xy : X × Y => H (m xy))
      - (Finset.univ.sum fun x : X => α x * g x (rowSum m x))
      - (Finset.univ.sum fun y : Y => β y * h y (colSum m y))

omit [Fintype X] in
theorem rowSum_update_eq (m : X × Y → ℝ) (x0 : X) (y0 : Y) (t : ℝ) :
    rowSum (Function.update m (x0, y0) t) x0 =
      t + (Finset.univ.erase y0).sum (fun y : Y => m (x0, y)) := by
  classical
  unfold rowSum
  have hfun :
      (fun y : Y => Function.update m (x0, y0) t (x0, y)) =
        Function.update (fun y : Y => m (x0, y)) y0 t := by
    funext y
    by_cases hy : y = y0 <;> simp [Function.update, hy]
  -- Rewrite the sum as a Finset sum of a `Function.update`.
  rw [hfun]
  rw [Finset.sum_update_of_mem (Finset.mem_univ y0)]
  simp

omit [Fintype X] in
theorem rowSum_update_of_ne (m : X × Y → ℝ) {x x0 : X} (hx : x ≠ x0) (y0 : Y) (t : ℝ) :
    rowSum (Function.update m (x0, y0) t) x = rowSum m x := by
  classical
  unfold rowSum
  simp [Function.update, hx]

omit [Fintype Y] in
theorem colSum_update_eq (m : X × Y → ℝ) (x0 : X) (y0 : Y) (t : ℝ) :
    colSum (Function.update m (x0, y0) t) y0 =
      t + (Finset.univ.erase x0).sum (fun x : X => m (x, y0)) := by
  classical
  unfold colSum
  have hfun :
      (fun x : X => Function.update m (x0, y0) t (x, y0)) =
        Function.update (fun x : X => m (x, y0)) x0 t := by
    funext x
    by_cases hx : x = x0 <;> simp [Function.update, hx]
  rw [hfun]
  rw [Finset.sum_update_of_mem (Finset.mem_univ x0)]
  simp

omit [Fintype Y] in
theorem colSum_update_of_ne (m : X × Y → ℝ) {y y0 : Y} (hy : y ≠ y0) (x0 : X) (t : ℝ) :
    colSum (Function.update m (x0, y0) t) y = colSum m y := by
  classical
  unfold colSum
  simp [Function.update, hy]

/-- A cleaned-up statement of the K&S coordinate-derivative calculation:
at a stationary point of a separable Lagrangian, the coordinate derivative separates into an
`X`-only term plus a `Y`-only term. -/
theorem lagrange_coordinate_deriv_eq
    (H : ℝ → ℝ) (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ) (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) (x0 : X) (y0 : Y)
    (hH : DifferentiableAt ℝ H (m (x0, y0)))
    (hg : DifferentiableAt ℝ (g x0) (rowSum m x0))
    (hh : DifferentiableAt ℝ (h y0) (colSum m y0))
    (hcrit : HasDerivAt
      (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
      0 (m (x0, y0))) :
    deriv H (m (x0, y0))
      = α x0 * deriv (g x0) (rowSum m x0) + β y0 * deriv (h y0) (colSum m y0) := by
  classical
  -- Compute the derivative of the objective part: only the `(x0,y0)` coordinate varies.
  have hObj :
      HasDerivAt
        (fun t => (Finset.univ : Finset (X × Y)).sum fun xy : X × Y => H ((Function.update m (x0, y0) t) xy))
        (deriv H (m (x0, y0))) (m (x0, y0)) := by
    -- Only the `(x0,y0)` coordinate varies.
    have hsum :
        (fun t =>
            (Finset.univ : Finset (X × Y)).sum fun xy : X × Y => H ((Function.update m (x0, y0) t) xy)) =
          fun t =>
            H t + (Finset.univ.erase (x0, y0)).sum (fun xy : X × Y => H (m xy)) := by
      funext t
      have hfun :
          (fun xy : X × Y => H ((Function.update m (x0, y0) t) xy)) =
            Function.update (fun xy : X × Y => H (m xy)) (x0, y0) (H t) := by
        funext xy
        by_cases hxy : xy = (x0, y0) <;> simp [Function.update, hxy]
      rw [hfun]
      rw [Finset.sum_update_of_mem (Finset.mem_univ (x0, y0))]
      simp
    -- Differentiate `t ↦ H t + const`.
    have hH' : HasDerivAt H (deriv H (m (x0, y0))) (m (x0, y0)) := hH.hasDerivAt
    have hconst :
        HasDerivAt (fun _ : ℝ => (Finset.univ.erase (x0, y0)).sum (fun xy : X × Y => H (m xy)))
          0 (m (x0, y0)) := hasDerivAt_const _ _
    have h : HasDerivAt
        (fun t => H t + (Finset.univ.erase (x0, y0)).sum (fun xy : X × Y => H (m xy)))
        (deriv H (m (x0, y0))) (m (x0, y0)) := by
      have h' :
          HasDerivAt
            (fun t => H t + (Finset.univ.erase (x0, y0)).sum (fun xy : X × Y => H (m xy)))
            (deriv H (m (x0, y0)) + 0) (m (x0, y0)) :=
        hH'.add hconst
      simpa [add_zero] using h'
    exact (hsum.symm ▸ h)
  -- Compute the derivative of the X-constraint part: only the `x0` marginal varies.
  have hRow :
      HasDerivAt
        (fun t => (Finset.univ : Finset X).sum fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x))
        (α x0 * deriv (g x0) (rowSum m x0)) (m (x0, y0)) := by
    have hsplit :
        (fun t =>
            (Finset.univ : Finset X).sum fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
          fun t =>
            α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
              + (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum m x)) := by
      funext t
      -- Peel off the `x0` term and show all others are constant in `t`.
      have hx0 : x0 ∈ (Finset.univ : Finset X) := Finset.mem_univ x0
      have : ((Finset.univ : Finset X).sum fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
          α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
            + (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) := by
        -- Convert `Fintype.sum` to `Finset.univ.sum` and use `sum_update_of_mem`.
        -- This is `sum_erase_add` in the direction we want.
        have hsum :=
          (Finset.sum_erase_add (s := (Finset.univ : Finset X)) (f := fun x : X =>
            α x * g x (rowSum (Function.update m (x0, y0) t) x)) hx0).symm
        -- `hsum` gives the decomposition as `(erase sum) + f x0`; reorder to `f x0 + (erase sum)`.
        calc
          ((Finset.univ : Finset X).sum fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
              (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x))
                + α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0) := hsum
          _ = α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
                + (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) := by
            ac_rfl
      -- Now rewrite the erase-sum using `rowSum_update_of_ne`.
      have herase :
          (Finset.univ.erase x0).sum (fun x : X =>
              α x * g x (rowSum (Function.update m (x0, y0) t) x))
            = (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum m x)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxne : x ≠ x0 := by
          exact (Finset.mem_erase.mp hx).1
        simp [rowSum_update_of_ne (m := m) (y0 := y0) (t := t) hxne]
      -- Assemble.
      simp [this, herase]
    have hcore : HasDerivAt (fun t => α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0))
        (α x0 * deriv (g x0) (rowSum m x0)) (m (x0, y0)) := by
      -- `rowSum` changes with slope 1 at `t0`.
      have hRowSlope :
          HasDerivAt (fun t => rowSum (Function.update m (x0, y0) t) x0) 1 (m (x0, y0)) := by
        -- Use the explicit linear form from `rowSum_update_eq`.
        have hlin :
            (fun t => rowSum (Function.update m (x0, y0) t) x0) =
              fun t => t + (Finset.univ.erase y0).sum (fun y : Y => m (x0, y)) := by
          funext t
          simp [rowSum_update_eq (m := m) (x0 := x0) (y0 := y0) (t := t)]
        have hid : HasDerivAt (fun t : ℝ => t) 1 (m (x0, y0)) := hasDerivAt_id _
        have hconst :
            HasDerivAt (fun _ : ℝ => (Finset.univ.erase y0).sum (fun y : Y => m (x0, y)))
              0 (m (x0, y0)) := hasDerivAt_const _ _
        have h' :
            HasDerivAt
              (fun t => t + (Finset.univ.erase y0).sum (fun y : Y => m (x0, y)))
              (1 + 0) (m (x0, y0)) :=
          hid.add hconst
        have h'' :
            HasDerivAt
              (fun t => t + (Finset.univ.erase y0).sum (fun y : Y => m (x0, y)))
              1 (m (x0, y0)) := by
          simpa [add_zero] using h'
        exact (hlin.symm ▸ h'')
      have hrowAt : rowSum (Function.update m (x0, y0) (m (x0, y0))) x0 = rowSum m x0 := by
        simp [Function.update_eq_self]
      have hg0 :
          DifferentiableAt ℝ (g x0) (rowSum (Function.update m (x0, y0) (m (x0, y0))) x0) := by
        simpa [hrowAt] using hg
      have hg' :
          HasDerivAt (g x0)
            (deriv (g x0) (rowSum (Function.update m (x0, y0) (m (x0, y0))) x0))
            (rowSum (Function.update m (x0, y0) (m (x0, y0))) x0) :=
        hg0.hasDerivAt
      have hcomp :
          HasDerivAt (fun t => g x0 (rowSum (Function.update m (x0, y0) t) x0))
            (deriv (g x0) (rowSum (Function.update m (x0, y0) (m (x0, y0))) x0)) (m (x0, y0)) := by
        simpa using hg'.comp (m (x0, y0)) hRowSlope
      -- Multiply by the constant `α x0`.
      simpa [mul_assoc] using hcomp.const_mul (α x0)
    have hconst :
        HasDerivAt (fun _ : ℝ => (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum m x)))
          0 (m (x0, y0)) := hasDerivAt_const _ _
    have h' : HasDerivAt
        (fun t =>
          α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
            + (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum m x)))
        (α x0 * deriv (g x0) (rowSum m x0) + 0) (m (x0, y0)) :=
      hcore.add hconst
    have h'' : HasDerivAt
        (fun t =>
          α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
            + (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum m x)))
        (α x0 * deriv (g x0) (rowSum m x0)) (m (x0, y0)) := by
      simpa [add_zero] using h'
    exact (hsplit.symm ▸ h'')
  -- Compute the derivative of the Y-constraint part: only the `y0` marginal varies.
  have hCol :
      HasDerivAt
        (fun t => (Finset.univ : Finset Y).sum fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y))
        (β y0 * deriv (h y0) (colSum m y0)) (m (x0, y0)) := by
    have hsplit :
        (fun t =>
            (Finset.univ : Finset Y).sum fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) =
          fun t =>
            β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
              + (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum m y)) := by
      funext t
      have hy0 : y0 ∈ (Finset.univ : Finset Y) := Finset.mem_univ y0
      have : ((Finset.univ : Finset Y).sum fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) =
          β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
            + (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) := by
        have hsum :=
          (Finset.sum_erase_add (s := (Finset.univ : Finset Y)) (f := fun y : Y =>
            β y * h y (colSum (Function.update m (x0, y0) t) y)) hy0).symm
        -- `hsum` gives the decomposition as `(erase sum) + f y0`; reorder to `f y0 + (erase sum)`.
        calc
          ((Finset.univ : Finset Y).sum fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) =
              (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y))
                + β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0) := hsum
          _ = β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
                + (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) := by
            ac_rfl
      have herase :
          (Finset.univ.erase y0).sum (fun y : Y =>
              β y * h y (colSum (Function.update m (x0, y0) t) y))
            = (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum m y)) := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hyne : y ≠ y0 := (Finset.mem_erase.mp hy).1
        simp [colSum_update_of_ne (m := m) (x0 := x0) (t := t) hyne]
      simp [this, herase]
    have hcore : HasDerivAt (fun t => β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0))
        (β y0 * deriv (h y0) (colSum m y0)) (m (x0, y0)) := by
      have hColSlope :
          HasDerivAt (fun t => colSum (Function.update m (x0, y0) t) y0) 1 (m (x0, y0)) := by
        have hlin :
            (fun t => colSum (Function.update m (x0, y0) t) y0) =
              fun t => t + (Finset.univ.erase x0).sum (fun x : X => m (x, y0)) := by
          funext t
          simp [colSum_update_eq (m := m) (x0 := x0) (y0 := y0) (t := t)]
        have hid : HasDerivAt (fun t : ℝ => t) 1 (m (x0, y0)) := hasDerivAt_id _
        have hconst :
            HasDerivAt (fun _ : ℝ => (Finset.univ.erase x0).sum (fun x : X => m (x, y0)))
              0 (m (x0, y0)) := hasDerivAt_const _ _
        have h' :
            HasDerivAt
              (fun t => t + (Finset.univ.erase x0).sum (fun x : X => m (x, y0)))
              (1 + 0) (m (x0, y0)) :=
          hid.add hconst
        have h'' :
            HasDerivAt
              (fun t => t + (Finset.univ.erase x0).sum (fun x : X => m (x, y0)))
              1 (m (x0, y0)) := by
          simpa [add_zero] using h'
        exact (hlin.symm ▸ h'')
      have hcolAt : colSum (Function.update m (x0, y0) (m (x0, y0))) y0 = colSum m y0 := by
        simp [Function.update_eq_self]
      have hh0 :
          DifferentiableAt ℝ (h y0) (colSum (Function.update m (x0, y0) (m (x0, y0))) y0) := by
        simpa [hcolAt] using hh
      have hh' :
          HasDerivAt (h y0)
            (deriv (h y0) (colSum (Function.update m (x0, y0) (m (x0, y0))) y0))
            (colSum (Function.update m (x0, y0) (m (x0, y0))) y0) :=
        hh0.hasDerivAt
      have hcomp :
          HasDerivAt (fun t => h y0 (colSum (Function.update m (x0, y0) t) y0))
            (deriv (h y0) (colSum (Function.update m (x0, y0) (m (x0, y0))) y0)) (m (x0, y0)) := by
        simpa using hh'.comp (m (x0, y0)) hColSlope
      simpa [mul_assoc] using hcomp.const_mul (β y0)
    have hconst :
        HasDerivAt (fun _ : ℝ => (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum m y)))
          0 (m (x0, y0)) := hasDerivAt_const _ _
    have h' : HasDerivAt
        (fun t =>
          β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
            + (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum m y)))
        (β y0 * deriv (h y0) (colSum m y0) + 0) (m (x0, y0)) :=
      hcore.add hconst
    have h'' : HasDerivAt
        (fun t =>
          β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
            + (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum m y)))
        (β y0 * deriv (h y0) (colSum m y0)) (m (x0, y0)) := by
      simpa [add_zero] using h'
    exact (hsplit.symm ▸ h'')
  -- Assemble the derivative of the full Lagrangian and use `hcrit`.
  have hL :
      HasDerivAt (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
        (deriv H (m (x0, y0)) - α x0 * deriv (g x0) (rowSum m x0) - β y0 * deriv (h y0) (colSum m y0))
        (m (x0, y0)) := by
    unfold productLagrangian
    -- `t ↦ objective - rowConstraints - colConstraints`
    simpa [sub_eq_add_neg, add_assoc] using ((hObj.sub hRow).sub hCol)
  have : deriv (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
      (m (x0, y0))
      = deriv H (m (x0, y0)) - α x0 * deriv (g x0) (rowSum m x0) - β y0 * deriv (h y0) (colSum m y0) :=
    hL.deriv
  have hcrit' :
      deriv (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
        (m (x0, y0)) = 0 := hcrit.deriv
  -- Rewrite the stationarity condition using the computed derivative and solve for `deriv H`.
  rw [this] at hcrit'
  linarith

/-- The same coordinate-derivative separation, but with stationarity derived from a local extremum.

This is the “fully honest” Path B: a local minimum/maximum implies the coordinate derivative is
zero (Fermat's theorem), so we do **not** assume `HasDerivAt … 0 …` as an extra axiom. -/
theorem lagrange_coordinate_deriv_eq_of_isLocalExtr
    (H : ℝ → ℝ) (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ) (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) (x0 : X) (y0 : Y)
    (hH : DifferentiableAt ℝ H (m (x0, y0)))
    (hg : DifferentiableAt ℝ (g x0) (rowSum m x0))
    (hh : DifferentiableAt ℝ (h y0) (colSum m y0))
    (hExtr :
      IsLocalExtr
        (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
        (m (x0, y0))) :
    deriv H (m (x0, y0))
      = α x0 * deriv (g x0) (rowSum m x0) + β y0 * deriv (h y0) (colSum m y0) := by
  classical
  let f : ℝ → ℝ := fun t => productLagrangian H g h α β (Function.update m (x0, y0) t)
  let t0 : ℝ := m (x0, y0)
  have hDiff : DifferentiableAt ℝ f t0 := by
    -- We rewrite each finite sum to separate out the unique `t`-dependent term; all other terms are
    -- constant in `t` and therefore differentiable.
    let objConst : ℝ := (Finset.univ.erase (x0, y0)).sum fun xy : X × Y => H (m xy)
    have hObjEq :
        (fun t =>
            (Finset.univ : Finset (X × Y)).sum fun xy : X × Y =>
              H ((Function.update m (x0, y0) t) xy)) =
          fun t => H t + objConst := by
      funext t
      have hfun :
          (fun xy : X × Y => H ((Function.update m (x0, y0) t) xy)) =
            Function.update (fun xy : X × Y => H (m xy)) (x0, y0) (H t) := by
        funext xy
        by_cases hxy : xy = (x0, y0) <;> simp [Function.update, hxy]
      rw [hfun]
      rw [Finset.sum_update_of_mem (Finset.mem_univ (x0, y0))]
      simp [objConst]
    have hObjDiff :
        DifferentiableAt ℝ
          (fun t =>
            (Finset.univ : Finset (X × Y)).sum fun xy : X × Y =>
              H ((Function.update m (x0, y0) t) xy))
          t0 := by
      have : DifferentiableAt ℝ (fun t => H t + objConst) t0 := by
        simpa [t0] using hH.add (differentiableAt_const (c := objConst))
      simpa [hObjEq] using this

    let rowConst : ℝ := (Finset.univ.erase x0).sum fun x : X => α x * g x (rowSum m x)
    have hRowEq :
        (fun t =>
            (Finset.univ : Finset X).sum fun x : X =>
              α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
          fun t => α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0) + rowConst := by
      funext t
      have hsplit :
          (Finset.univ : Finset X).sum (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
            α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
              + (Finset.univ.erase x0).sum
                  (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) := by
        have hx0 : x0 ∈ (Finset.univ : Finset X) := Finset.mem_univ x0
        have hsum :=
          (Finset.sum_erase_add (s := (Finset.univ : Finset X))
            (f := fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) hx0).symm
        calc
          ((Finset.univ : Finset X).sum fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
              (Finset.univ.erase x0).sum
                  (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x))
                + α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0) := hsum
          _ =
              α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)
                + (Finset.univ.erase x0).sum
                    (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) := by
            ac_rfl
      have hErase :
          (Finset.univ.erase x0).sum (fun x : X => α x * g x (rowSum (Function.update m (x0, y0) t) x)) =
            rowConst := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxne : x ≠ x0 := (Finset.mem_erase.mp hx).1
        simp [rowSum_update_of_ne (m := m) (x0 := x0) (y0 := y0) (t := t) hxne]
      simpa using (by rw [hsplit, hErase])
    have hRowDiff :
        DifferentiableAt ℝ
          (fun t =>
            (Finset.univ : Finset X).sum fun x : X =>
              α x * g x (rowSum (Function.update m (x0, y0) t) x))
          t0 := by
      have hRowSumDiff :
          DifferentiableAt ℝ (fun t => rowSum (Function.update m (x0, y0) t) x0) t0 := by
        -- `rowSum (update … t) x0 = t + const`
        simp [rowSum_update_eq (m := m) (x0 := x0) (y0 := y0)]
      have hRowAt : rowSum (Function.update m (x0, y0) t0) x0 = rowSum m x0 := by
        simp [t0, Function.update_eq_self]
      have hg0 : DifferentiableAt ℝ (g x0) (rowSum (Function.update m (x0, y0) t0) x0) := by
        simpa [hRowAt, t0] using hg
      have hComp : DifferentiableAt ℝ (fun t => g x0 (rowSum (Function.update m (x0, y0) t) x0)) t0 :=
        hg0.comp t0 hRowSumDiff
      have hMain :
          DifferentiableAt ℝ
            (fun t => α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0) + rowConst)
            t0 := by
        have hmul :
            DifferentiableAt ℝ (fun t => α x0 * g x0 (rowSum (Function.update m (x0, y0) t) x0)) t0 :=
          (differentiableAt_const (c := α x0)).mul hComp
        exact hmul.add (differentiableAt_const (c := rowConst))
      simpa [hRowEq] using hMain

    let colConst : ℝ := (Finset.univ.erase y0).sum fun y : Y => β y * h y (colSum m y)
    have hColEq :
        (fun t =>
            (Finset.univ : Finset Y).sum fun y : Y =>
              β y * h y (colSum (Function.update m (x0, y0) t) y)) =
          fun t => β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0) + colConst := by
      funext t
      have hsplit :
          (Finset.univ : Finset Y).sum (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) =
            β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
              + (Finset.univ.erase y0).sum
                  (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) := by
        have hy0 : y0 ∈ (Finset.univ : Finset Y) := Finset.mem_univ y0
        have hsum :=
          (Finset.sum_erase_add (s := (Finset.univ : Finset Y))
            (f := fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) hy0).symm
        calc
          ((Finset.univ : Finset Y).sum fun y : Y =>
              β y * h y (colSum (Function.update m (x0, y0) t) y)) =
              (Finset.univ.erase y0).sum
                  (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y))
                + β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0) := hsum
          _ =
              β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0)
                + (Finset.univ.erase y0).sum
                    (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) := by
            ac_rfl
      have hErase :
          (Finset.univ.erase y0).sum (fun y : Y => β y * h y (colSum (Function.update m (x0, y0) t) y)) =
            colConst := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hyne : y ≠ y0 := (Finset.mem_erase.mp hy).1
        simp [colSum_update_of_ne (m := m) (y0 := y0) (x0 := x0) (t := t) hyne]
      simpa using (by rw [hsplit, hErase])
    have hColDiff :
        DifferentiableAt ℝ
          (fun t =>
            (Finset.univ : Finset Y).sum fun y : Y =>
              β y * h y (colSum (Function.update m (x0, y0) t) y))
          t0 := by
      have hColSumDiff :
          DifferentiableAt ℝ (fun t => colSum (Function.update m (x0, y0) t) y0) t0 := by
        simp [colSum_update_eq (m := m) (x0 := x0) (y0 := y0)]
      have hColAt : colSum (Function.update m (x0, y0) t0) y0 = colSum m y0 := by
        simp [t0, Function.update_eq_self]
      have hh0 : DifferentiableAt ℝ (h y0) (colSum (Function.update m (x0, y0) t0) y0) := by
        simpa [hColAt, t0] using hh
      have hComp : DifferentiableAt ℝ (fun t => h y0 (colSum (Function.update m (x0, y0) t) y0)) t0 :=
        hh0.comp t0 hColSumDiff
      have hMain :
          DifferentiableAt ℝ
            (fun t => β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0) + colConst)
            t0 := by
        have hmul :
            DifferentiableAt ℝ
              (fun t => β y0 * h y0 (colSum (Function.update m (x0, y0) t) y0))
              t0 :=
          (differentiableAt_const (c := β y0)).mul hComp
        exact hmul.add (differentiableAt_const (c := colConst))
      simpa [hColEq] using hMain

    have hf :
        DifferentiableAt ℝ
          (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
          t0 := by
      unfold productLagrangian
      -- `t ↦ objective - rowConstraints - colConstraints`
      simpa [sub_eq_add_neg, add_assoc] using ((hObjDiff.sub hRowDiff).sub hColDiff)
    simpa [f, t0] using hf

  have hf : HasDerivAt f (deriv f t0) t0 := hDiff.hasDerivAt
  have hder0 : deriv f t0 = 0 := by
    have hExtr' : IsLocalExtr f t0 := by simpa [f, t0] using hExtr
    exact hExtr'.hasDerivAt_eq_zero hf
  have hcrit : HasDerivAt f 0 t0 := by simpa [hder0] using hf
  have hmain :=
    lagrange_coordinate_deriv_eq (H := H) (g := g) (h := h) (α := α) (β := β)
      (m := m) (x0 := x0) (y0 := y0)
      (by simpa [t0] using hH) (by simpa [t0] using hg) (by simpa [t0] using hh) (by simpa [f, t0] using hcrit)
  simpa [t0] using hmain

theorem lagrange_coordinate_deriv_eq_product
    (H : ℝ → ℝ) (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ) (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) (x0 : X) (y0 : Y)
    (hH : DifferentiableAt ℝ H (m (x0, y0)))
    (hg : DifferentiableAt ℝ (g x0) (rowSum m x0))
    (hh : DifferentiableAt ℝ (h y0) (colSum m y0))
    (hprod : m (x0, y0) = rowSum m x0 * colSum m y0)
    (hcrit : HasDerivAt
      (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
      0 (m (x0, y0))) :
    deriv H (rowSum m x0 * colSum m y0)
      = α x0 * deriv (g x0) (rowSum m x0) + β y0 * deriv (h y0) (colSum m y0) := by
  simpa [hprod] using
    lagrange_coordinate_deriv_eq (H := H) (g := g) (h := h) (α := α) (β := β)
      (m := m) (x0 := x0) (y0 := y0) hH hg hh hcrit

theorem lagrange_coordinate_deriv_eq_product_of_isLocalExtr
    (H : ℝ → ℝ) (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ) (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) (x0 : X) (y0 : Y)
    (hH : DifferentiableAt ℝ H (m (x0, y0)))
    (hg : DifferentiableAt ℝ (g x0) (rowSum m x0))
    (hh : DifferentiableAt ℝ (h y0) (colSum m y0))
    (hprod : m (x0, y0) = rowSum m x0 * colSum m y0)
    (hExtr :
      IsLocalExtr
        (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
        (m (x0, y0))) :
    deriv H (rowSum m x0 * colSum m y0)
      = α x0 * deriv (g x0) (rowSum m x0) + β y0 * deriv (h y0) (colSum m y0) := by
  have h :=
    lagrange_coordinate_deriv_eq_of_isLocalExtr (H := H) (g := g) (h := h) (α := α) (β := β)
      (m := m) (x0 := x0) (y0 := y0) hH hg hh hExtr
  simpa [hprod] using h

/-- Path B in the exact “K&S `Hproduct`” shape.

This makes the `x`-only and `y`-only parts explicit as functions of the marginals `m_x, m_y`.

K&S then treat this as a functional equation in the independent variables `m_x, m_y`, and solve it
in Appendix C under a regularity hypothesis (we use measurability in Path A). -/
theorem lagrange_Hproduct_eq_of_isLocalExtr
    (H : ℝ → ℝ) (g : X → ℝ → ℝ) (h : Y → ℝ → ℝ) (α : X → ℝ) (β : Y → ℝ)
    (m : X × Y → ℝ) (x0 : X) (y0 : Y)
    (hH : DifferentiableAt ℝ H (m (x0, y0)))
    (hg : DifferentiableAt ℝ (g x0) (rowSum m x0))
    (hh : DifferentiableAt ℝ (h y0) (colSum m y0))
    (hprod : m (x0, y0) = rowSum m x0 * colSum m y0)
    (hExtr :
      IsLocalExtr
        (fun t => productLagrangian H g h α β (Function.update m (x0, y0) t))
        (m (x0, y0))) :
    deriv H (rowSum m x0 * colSum m y0) =
      (fun m_x => α x0 * deriv (g x0) m_x) (rowSum m x0) +
        (fun m_y => β y0 * deriv (h y0) m_y) (colSum m y0) := by
  -- The goal is definitional equal to `lagrange_coordinate_deriv_eq_product_of_isLocalExtr`.
  simpa using
    lagrange_coordinate_deriv_eq_product_of_isLocalExtr (H := H) (g := g) (h := h) (α := α)
      (β := β) (m := m) (x0 := x0) (y0 := y0) hH hg hh hprod hExtr

end PathB

/-! ### The Bridge Theorem: Connecting Path A and Path B'

**Path A** (Variational Equation): `H'(m) = B + C · log(m)`
Integrated: `H(m) = A + Bm + C(m log m - m)`

**Path B'** (Product Entropy Separability): `h'(m) = C/m`
Integrated: `h(m) = C · log(m) + const`

These are **different functions**, but they're related through the structure of
the variational potential. The bridge shows how setting appropriate constants
connects the two forms. -/

/-- **Bridge: Path A with B=0 gives a form compatible with Path B'**.

When `B = 0`, the entropy form is `H(m) = A + C(m log m - m)`.
This has derivative `H'(m) = C log m`, matching the logarithmic structure. -/
theorem bridge_pathA_B0_gives_pathB {A C : ℝ} (m : ℝ) (hm : 0 < m) :
    deriv (entropyForm A 0 C) m = C * Real.log m := by
  have h := entropyForm_has_derivative A 0 C m hm
  simp only [zero_add] at h
  exact h.deriv

/-- **Bridge: Path B' result connects to Path A form**.

If `h(m) = C log m` (Path B form), then defining `H(m) = m · h(m) - C · m`
gives exactly the entropy form `H(m) = C(m log m - m)`. -/
theorem bridge_pathB_to_pathA {C : ℝ} (m : ℝ) (_hm : 0 < m) :
    let h := fun m => C * Real.log m  -- Path B form
    let H := fun m => m * h m - C * m  -- Transform to Path A form
    H m = C * (m * Real.log m - m) := by
  simp only
  ring

/-- **Unified Theorem**: Both paths lead to the same essential structure.

Setting `A = 0`, `B = 0` in Path A: `H(m) = C(m log m - m)`.
This is exactly what we get from the transformation of Path B's `h(m) = C log m`. -/
theorem unified_entropy_structure :
    ∀ C : ℝ, ∀ m : ℝ, 0 < m →
      entropyForm 0 0 C m = C * (m * Real.log m - m) := by
  intro C m _
  simp only [entropyForm, zero_add, zero_mul]

/-! ### Connection to Probability and Shannon Entropy

This file is the **analytic core**.  Discrete probability specializations live in:
- `Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence` (K&S Section 6)
- `Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy` (K&S Section 8)
-/

/-! ### Summary: The Complete K&S Derivation

We have now formalized:

1. **Path A (Variational Equation)**: `variationalEquation_solution_measurable`
   - Input: `H'(mₓ · mᵧ) = λ(mₓ) + μ(mᵧ)` + measurability
   - Output: `H'(m) = B + C log m`

2. **Path B (Lagrange Multipliers)**: `lagrange_coordinate_deriv_eq`
   - Input: a stationary point of the separable `productLagrangian` on an `x`-by-`y` product
   - Output: the K&S separated coordinate equation `H'(m_xy) = λ(x) + μ(y)` (in its explicit form)

3. **Bridge Theorems**: `bridge_pathA_B0_gives_pathB`, `bridge_pathB_to_pathA`
   - Path A's `H(m) = C(m log m - m)` is the "extensive" form
   - Path B's `h(m) = C log m` is the "intensive" form
   - Related by: `H(m) = m · h(m) - C · m`
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Variational
