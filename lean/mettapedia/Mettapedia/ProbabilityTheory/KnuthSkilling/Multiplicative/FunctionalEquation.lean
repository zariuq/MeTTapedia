import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Rat

/-!
# Knuth–Skilling Appendix B: Product Theorem

This file formalizes the **Product Theorem** from:

- Knuth & Skilling, *Foundations of Inference* (2012), Appendix B
  `literature/Knuth_Skilling/Knuth_Skilling_Foundations_of_Inference/knuth-skilling-2012---foundations-of-inference----arxiv.tex`
  (see around lines 1965–2090 in the TeX source).

K&S consider the functional **product equation** (TeX eq. (1972))

`Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ, η))`,

where `τ, ξ, η` are “independent real variables” (formalized here as `∀ τ ξ η : ℝ, ...`)
and `Ψ` is positive. They claim the positive solutions are exactly exponentials:

`Ψ(x) = C * exp (A * x)` with `0 < C`.

## Explicit regularity assumptions

The TeX proof uses `≈` steps (density / “arbitrarily close”) and boundedness heuristics.
To keep the statement honest and the proof robust, we assume the regrading `Ψ` is:

- `Continuous Ψ`
- `StrictMono Ψ`

This matches the intended “order-preserving scale” interpretation.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative

open Classical
open Set
open scoped Topology

/-! ## The product equation (Appendix B) -/

/-- K&S Appendix B product equation (TeX eq. (1972)). -/
def ProductEquation (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ) : Prop :=
  ∀ τ ξ η : ℝ, Ψ (τ + ξ) + Ψ (τ + η) = Ψ (τ + ζ ξ η)

namespace ProductEquation

variable {Ψ : ℝ → ℝ} {ζ : ℝ → ℝ → ℝ}

/-- Special case `τ = 0`: `Ψ ξ + Ψ η = Ψ (ζ ξ η)`. -/
theorem tau0 (h : ProductEquation Ψ ζ) (ξ η : ℝ) :
    Ψ ξ + Ψ η = Ψ (ζ ξ η) := by
  simpa using h 0 ξ η

/-- The “2-term recurrence” extracted from the product equation (TeX eq. (1991)):

for `a := ζ 0 0`, we have `Ψ (τ + a) = 2 * Ψ τ`. -/
theorem shift_two_mul (h : ProductEquation Ψ ζ) (τ : ℝ) :
    Ψ (τ + ζ 0 0) = 2 * Ψ τ := by
  have hτ := h τ 0 0
  -- `Ψ(τ)+Ψ(τ) = Ψ(τ+a)`
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using hτ.symm

end ProductEquation

/-! ## Additive actions on `(0,∞)` -/

namespace AdditiveOnPos

/-- If `f` is additive on positive reals and maps positive reals to positive reals, then
it is strictly increasing on `(0,∞)`. -/
theorem strictMonoOn_of_add_of_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    (hpos : ∀ {u : ℝ}, 0 < u → 0 < f u) :
    StrictMonoOn f (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hdiff : 0 < b - a := sub_pos.mpr hab
  have hsplit : f b = f a + f (b - a) := by
    -- `b = a + (b-a)`
    calc
      f b = f (a + (b - a)) := by simp [add_sub_cancel]
      _ = f a + f (b - a) := hadd ha hdiff
  have hf_diff : 0 < f (b - a) := hpos hdiff
  have : f a < f a + f (b - a) := lt_add_of_pos_right _ hf_diff
  simpa [hsplit] using this

/-- If `f` is additive on positive reals, then scaling the input by a positive natural scales
the output by the same natural. -/
theorem map_natMul
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    {u : ℝ} (hu : 0 < u) :
    ∀ n : ℕ, f ((n.succ : ℝ) * u) = (n.succ : ℝ) * f u := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hnpos : 0 < ((n.succ : ℝ) * u) := by
      have : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact mul_pos this hu
    have hmul : ((n.succ.succ : ℝ) * u) = ((n.succ : ℝ) * u + u) := by
      -- `(n+2)u = (n+1)u + u`
      simp [Nat.cast_succ, add_mul, add_assoc, add_left_comm, add_comm]
    calc
      f ((n.succ.succ : ℝ) * u)
          = f (((n.succ : ℝ) * u) + u) := by
              simpa using congrArg f hmul
      _ = f ((n.succ : ℝ) * u) + f u := hadd hnpos hu
      _ = (n.succ : ℝ) * f u + f u := by
          simpa using congrArg (fun t => t + f u) ih
      _ = (n.succ.succ : ℝ) * f u := by
        simp [Nat.cast_succ, add_mul, add_assoc, add_left_comm, add_comm]

/-- `map_natMul` with the natural-multiplier provided explicitly (requiring `0 < n`). -/
theorem map_natMul_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    {u : ℝ} (hu : 0 < u) (n : ℕ) (hn : 0 < n) :
    f ((n : ℝ) * u) = (n : ℝ) * f u := by
  cases n with
  | zero => cases hn
  | succ n =>
    simpa using map_natMul f hadd hu n

/-- **Scaling lemma**: an additive, positive function on `(0,∞)` is multiplication by a constant.

This is a standard “Cauchy + monotone” argument, but restricted to positive reals.
-/
theorem exists_mul_const_of_add_of_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    (hpos : ∀ {u : ℝ}, 0 < u → 0 < f u) :
    ∃ c : ℝ, 0 < c ∧ ∀ {u : ℝ}, 0 < u → f u = c * u := by
  classical
  let c : ℝ := f 1
  have hc : 0 < c := by simpa [c] using hpos (u := (1 : ℝ)) (by norm_num)
  have hmono : StrictMonoOn f (Ioi (0 : ℝ)) :=
    strictMonoOn_of_add_of_pos f hadd hpos

  -- First: compute `f` on positive rationals using the `m/n` normal form.
  have hrat : ∀ q : ℚ, 0 < (q : ℝ) → f (q : ℝ) = c * (q : ℝ) := by
    intro q hq
    -- Represent `q` as `(m : ℕ) / (n : ℕ)` in ℝ, using `natAbs` since `q > 0`.
    have hq_pos : 0 < q := by exact_mod_cast hq
    have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
    let m : ℕ := q.num.natAbs
    let n : ℕ := q.den
    have hn_pos : 0 < n := q.den_pos
    have hn_posR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_posR
    have hm_pos : 0 < m := by
      have hne : q.num ≠ 0 := ne_of_gt hnum_pos
      have : 0 < q.num.natAbs := (Int.natAbs_pos).2 hne
      simpa [m] using this

    have hq_cast : (q : ℝ) = (m : ℝ) / (n : ℝ) := by
      -- `Rat.cast_def` gives `q = q.num / q.den`; rewrite the numerator using `natAbs`
      have hnum_cast : (q.num : ℝ) = (m : ℝ) := by
        have : (q.num : ℤ) = (m : ℤ) := by
          -- `q.num ≥ 0` since `q > 0`, so `natAbs` is the underlying nat.
          simpa [m] using (Int.natAbs_of_nonneg (le_of_lt hnum_pos)).symm
        simpa using congrArg (fun z : ℤ => (z : ℝ)) this
      calc
        (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by simp [Rat.cast_def]
        _ = (q.num : ℝ) / (n : ℝ) := by simp [n]
        _ = (m : ℝ) / (n : ℝ) := by simp [hnum_cast]

    -- Let `u = 1/n`. Then `f(1) = n * f(u)` and `f(m/n) = m * f(u)`.
    let u : ℝ := (1 : ℝ) / (n : ℝ)
    have hu : 0 < u := by
      exact div_pos (by norm_num) hn_posR

    have h_one : f ((n : ℝ) * u) = (n : ℝ) * f u :=
      map_natMul_pos f hadd hu n hn_pos
    have hnu : (n : ℝ) * u = (1 : ℝ) := by
      simp [u, div_eq_mul_inv, hn_ne]
    have h1 : f 1 = (n : ℝ) * f u := by
      simpa [hnu] using h_one
    have h_u : f u = c / (n : ℝ) := by
      have hmul : f u * (n : ℝ) = c := by
        -- rewrite `f 1 = n * f u` as `f u * n = f 1`
        simpa [c, mul_comm, mul_left_comm, mul_assoc] using h1.symm
      exact (eq_div_iff hn_ne).2 hmul

    have h_m : f ((m : ℝ) * u) = (m : ℝ) * f u :=
      map_natMul_pos f hadd hu m hm_pos

    calc
      f (q : ℝ) = f ((m : ℝ) * u) := by
        simp [hq_cast, u, div_eq_mul_inv]
      _ = (m : ℝ) * f u := h_m
      _ = (m : ℝ) * (c / (n : ℝ)) := by simp [h_u]
      _ = c * ((m : ℝ) / (n : ℝ)) := by ring
      _ = c * (q : ℝ) := by simp [hq_cast]

  refine ⟨c, hc, ?_⟩
  intro u hu
  -- Upper bound: `f u ≤ c*u` using rational approximations from above.
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hfu_le : f u ≤ c * u := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    have hδ : 0 < ε / c := div_pos hε hc
    have h_u_lt : u < u + ε / c := lt_add_of_pos_right _ hδ
    rcases exists_rat_btwn h_u_lt with ⟨p, hup, hpu⟩
    have hp_pos : 0 < (p : ℝ) := lt_trans hu hup
    have hfup : f u ≤ f (p : ℝ) := le_of_lt (hmono hu hp_pos hup)
    have hfp : f (p : ℝ) = c * (p : ℝ) := hrat p hp_pos
    have h1 : f u ≤ c * (p : ℝ) := by simpa [hfp] using hfup
    have h2 : c * (p : ℝ) < c * u + ε := by
      have hmul : c * (p : ℝ) < c * (u + ε / c) := mul_lt_mul_of_pos_left hpu hc
      field_simp [hc_ne] at hmul
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact lt_of_le_of_lt h1 h2
  -- Lower bound: `c*u ≤ f u` using rational approximations from below (ensuring positivity).
  have hcu_le : c * u ≤ f u := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    have hδ_pos : 0 < ε / c := div_pos hε hc
    have hu2_pos : 0 < u / 2 := half_pos hu
    let δ : ℝ := min (u / 2) (ε / c)
    have hδ : 0 < δ := lt_min hu2_pos hδ_pos
    have hδ_le_u2 : δ ≤ u / 2 := min_le_left _ _
    have hδ_le_eps : δ ≤ ε / c := min_le_right _ _
    have hδ_lt_u : δ < u := by
      have hu2_lt_u : u / 2 < u := by linarith
      exact lt_of_le_of_lt hδ_le_u2 hu2_lt_u
    have h_lower_lt : u - δ < u := sub_lt_self u hδ
    rcases exists_rat_btwn h_lower_lt with ⟨q, huq, hqu⟩
    have hq_pos : 0 < (q : ℝ) := by
      have hlower_pos : 0 < u - δ := sub_pos.mpr hδ_lt_u
      exact lt_trans hlower_pos huq
    have hfq_le : f (q : ℝ) ≤ f u := by
      have hfq_lt : f (q : ℝ) < f u := hmono hq_pos hu hqu
      exact le_of_lt hfq_lt
    have hfq : f (q : ℝ) = c * (q : ℝ) := hrat q hq_pos
    have h_u_minus : u - ε / c < (q : ℝ) := by
      have : u - ε / c ≤ u - δ := sub_le_sub_left hδ_le_eps u
      exact lt_of_le_of_lt this huq
    have h_u_lt : u < (q : ℝ) + ε / c := by linarith
    have hmul : c * u < c * ((q : ℝ) + ε / c) := mul_lt_mul_of_pos_left h_u_lt hc
    have hmul' : c * u < c * (q : ℝ) + ε := by
      field_simp [hc_ne] at hmul
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    have : c * u < f (q : ℝ) + ε := by simpa [hfq] using hmul'
    exact lt_of_lt_of_le this (add_le_add_right hfq_le _)

  exact le_antisymm hfu_le hcu_le

end AdditiveOnPos

/-! ## Main theorem: exponentiality (Appendix B) -/

open Filter

/-- A convenient Cauchy lemma: a continuous additive `φ : ℝ → ℝ` is linear. -/
theorem continuous_additive_eq_mul (φ : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, φ (x + y) = φ x + φ y)
    (hcont : Continuous φ) :
    ∃ A : ℝ, ∀ x : ℝ, φ x = A * x := by
  let f_add : ℝ →+ ℝ :=
    { toFun := φ
      map_zero' := by
        have h := hadd 0 0
        have : φ 0 + 0 = φ 0 + φ 0 := by simpa using h
        have : 0 = φ 0 := add_left_cancel this
        simpa using this.symm
      map_add' := by intro x y; simpa using hadd x y }
  have hf_add_cont : Continuous f_add := by
    simpa [f_add] using hcont
  let f_lin : ℝ →L[ℝ] ℝ := f_add.toRealLinearMap hf_add_cont
  refine ⟨f_lin 1, ?_⟩
  intro x
  have hsmul := f_lin.map_smul x (1 : ℝ)
  have : f_lin x = x * f_lin 1 := by simpa [smul_eq_mul] using hsmul
  simpa [f_add, f_lin, mul_comm, mul_left_comm, mul_assoc] using this

/-- K&S Appendix B Product Theorem: exponential is the unique solution.

If `Ψ` is positive, continuous, strictly monotone, and satisfies the product equation,
then `Ψ x = C * exp (A * x)` for some `C > 0`.

This is a standard functional equations result. The hypotheses `Continuous Ψ` and
`StrictMono Ψ` are **not** extra assumptions in K&S - they are **derived** from the
order isomorphism `Θ : PosReal ≃o ℝ` established in Appendix A:
- `Psi_continuous`: order isomorphisms on ℝ are continuous
- `Psi_strictMono`: order isomorphisms are strictly monotone

See `Multiplicative.Main` for the assembled result. -/
theorem productEquation_solution_of_continuous_strictMono
    {Ψ : ℝ → ℝ} {ζ : ℝ → ℝ → ℝ}
    (hEq : ProductEquation Ψ ζ)
    (hPos : ∀ x : ℝ, 0 < Ψ x)
    (hCont : Continuous Ψ)
    (hMono : StrictMono Ψ) :
    ∃ (C A : ℝ), 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  classical
  -- Extract the constant shift `a` with `Ψ(x+a)=2Ψ(x)`.
  let a : ℝ := ζ 0 0
  have hshift : ∀ τ : ℝ, Ψ (τ + a) = 2 * Ψ τ := by
    intro τ
    simpa [a] using ProductEquation.shift_two_mul (Ψ := Ψ) (ζ := ζ) hEq τ

  -- Positivity of `a` (since `Ψ` is strictly increasing).
  have ha_pos : 0 < a := by
    have h0 : 0 < Ψ 0 := hPos 0
    have hΨ0_lt_Ψa : Ψ 0 < Ψ a := by
      have hΨa : Ψ a = 2 * Ψ 0 := by simpa [a, zero_add] using (hshift 0)
      have hlt : Ψ 0 < 2 * Ψ 0 := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa [one_mul] using (mul_lt_mul_of_pos_right this h0)
      simpa [hΨa] using hlt
    exact (hMono.lt_iff_lt).1 hΨ0_lt_Ψa

  let C : ℝ := Ψ 0
  have hC_pos : 0 < C := hPos 0

  -- Surjectivity `Ψ : ℝ → (0,∞)` (needed to build a global inverse in the proof).
  have hsurj : Function.Surjective fun x : ℝ => (⟨Ψ x, hPos x⟩ : Ioi (0 : ℝ)) := by
    intro y
    rcases y with ⟨y, hy⟩
    -- Find `N` with `C / 2^N < y`.
    have hN : ∃ N : ℕ, C / (2 : ℝ) ^ N < y := by
      have hx : 0 < y / C := div_pos hy hC_pos
      rcases exists_pow_lt_of_lt_one (x := y / C) hx (y := (1 / 2 : ℝ)) (by norm_num) with
        ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have hpow : (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N := by simp [one_div, inv_pow]
      have hC_ne : C ≠ 0 := ne_of_gt hC_pos
      have hN' : (1 / (2 : ℝ) ^ N) < y / C := by simpa [hpow] using hN
      have hmul : (1 / (2 : ℝ) ^ N) * C < y := by
        have h := mul_lt_mul_of_pos_right hN' hC_pos
        simpa [div_mul_cancel, hC_ne] using h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    -- Find `M` with `y < 2^M * C`.
    have hM : ∃ M : ℕ, y < (2 : ℝ) ^ M * C := by
      have hx : 0 < y / C := div_pos hy hC_pos
      rcases pow_unbounded_of_one_lt (R := ℝ) (x := y / C) (y := (2 : ℝ)) (by norm_num) with
        ⟨M, hM⟩
      refine ⟨M, ?_⟩
      -- `y / C < 2^M` iff `y < (2^M) * C` since `0 < C`.
      simpa using (div_lt_iff₀ hC_pos).1 hM

    rcases hN with ⟨N, hN⟩
    rcases hM with ⟨M, hM⟩

    -- Compute values at `-(N*a)` and `(M*a)` using the shift law.
    have hC_mul (n : ℕ) : Ψ ((n : ℝ) * a) = (2 : ℝ) ^ n * C := by
      induction n with
      | zero => simp [C, a]
      | succ n ih =>
        have hstep : Ψ (((n : ℝ) * a) + a) = 2 * Ψ ((n : ℝ) * a) := hshift ((n : ℝ) * a)
        have hmul : ((n.succ : ℝ) * a) = (n : ℝ) * a + a := by
          simp [Nat.cast_succ, add_mul, add_comm]
        calc
          Ψ ((n.succ : ℝ) * a)
              = 2 * Ψ ((n : ℝ) * a) := by simpa [hmul.symm] using hstep
          _ = 2 * ((2 : ℝ) ^ n * C) := by simp [ih]
          _ = (2 : ℝ) ^ n.succ * C := by
            simp [pow_succ, mul_left_comm, mul_comm]

    have hC_div (n : ℕ) : Ψ (-(n : ℝ) * a) = C / (2 : ℝ) ^ n := by
      induction n with
      | zero => simp [C]
      | succ n ih =>
        -- Use `Ψ(τ+a)=2Ψ(τ)` at `τ := -(n+1)*a`.
        have hrec : Ψ ((-(n.succ : ℝ) * a) + a) = 2 * Ψ (-(n.succ : ℝ) * a) :=
          hshift (-(n.succ : ℝ) * a)
        have hmul : (-(n : ℝ) * a) = (-(n.succ : ℝ) * a) + a := by
          simp [Nat.cast_succ, add_mul, add_comm]
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        have hstep : Ψ (-(n.succ : ℝ) * a) = Ψ (-(n : ℝ) * a) / 2 := by
          -- rewrite `Ψ(-n*a) = 2 * Ψ(-(n+1)*a)` and divide by 2
          have hrec' : Ψ (-(n : ℝ) * a) = 2 * Ψ (-(n.succ : ℝ) * a) := by
            simpa [hmul] using hrec
          apply (eq_div_iff h2).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using hrec'.symm
        -- complete the induction step
        calc
          Ψ (-(n.succ : ℝ) * a)
              = Ψ (-(n : ℝ) * a) / 2 := hstep
          _ = (C / (2 : ℝ) ^ n) / 2 := by
            simpa using congrArg (fun t : ℝ => t / 2) ih
          _ = C / (2 : ℝ) ^ n.succ := by
            simp [pow_succ, div_eq_mul_inv, mul_left_comm, mul_comm]

    let xL : ℝ := - (N : ℝ) * a
    let xU : ℝ := (M : ℝ) * a
    have hxL : Ψ xL < y := by
      have hxL_eq : Ψ xL = C / (2 : ℝ) ^ N := by simpa [xL] using hC_div N
      simpa [hxL_eq] using hN
    have hxU : y < Ψ xU := by simpa [xU, hC_mul M] using hM
    have hxL_le_xU : xL ≤ xU := by
      have hxL_lt_xU : xL < xU := by
        have hNM : -(N : ℝ) < (M : ℝ) := by
          by_cases hN0 : N = 0
          · subst hN0
            have hCy : C < y := by simpa [pow_zero] using hN
            have hM0 : M ≠ 0 := by
              intro hM0
              subst hM0
              have : y < C := by simpa [pow_zero, one_mul] using hM
              exact (not_lt_of_gt hCy) this
            have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hM0)
            simpa using hMpos
          · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
            have hneg : -(N : ℝ) < 0 := neg_neg_of_pos (by exact_mod_cast hNpos)
            have hM0 : 0 ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
            exact lt_of_lt_of_le hneg hM0
        have hmul := mul_lt_mul_of_pos_right hNM ha_pos
        simpa [xL, xU] using hmul
      exact le_of_lt hxL_lt_xU

    have hy_mem : y ∈ Icc (Ψ xL) (Ψ xU) := ⟨le_of_lt hxL, le_of_lt hxU⟩
    have hy_img : y ∈ Ψ '' Icc xL xU :=
      (intermediate_value_Icc hxL_le_xU (hCont.continuousOn)) hy_mem
    rcases hy_img with ⟨x, hxIcc, hx⟩
    refine ⟨x, ?_⟩
    ext
    simpa using hx

  -- Build the order isomorphism `Ψ : ℝ ≃o (0,∞)`.
  let Ψpos : ℝ → Ioi (0 : ℝ) := fun x => ⟨Ψ x, hPos x⟩
  have hΨpos_mono : StrictMono Ψpos := by
    intro x y hxy
    exact hMono hxy
  let ΨIso : ℝ ≃o Ioi (0 : ℝ) := StrictMono.orderIsoOfSurjective _ hΨpos_mono hsurj

  -- Define the translate action on positive reals: `T τ(u) = Ψ(τ + Ψ^{-1}(u))`.
  let T : ℝ → ℝ → ℝ := fun τ u =>
    if hu : 0 < u then Ψ (τ + ΨIso.symm ⟨u, hu⟩) else 0

  have hT_pos : ∀ τ u : ℝ, 0 < u → 0 < T τ u := by
    intro τ u hu
    simp [T, hu, hPos]

  have hT_add : ∀ τ : ℝ, ∀ {u v : ℝ}, 0 < u → 0 < v → T τ (u + v) = T τ u + T τ v := by
    intro τ u v hu hv
    have huv : 0 < u + v := add_pos hu hv
    -- Let `ξ,η` be the unique preimages of `u,v`.
    set ξ : ℝ := ΨIso.symm ⟨u, hu⟩
    set η : ℝ := ΨIso.symm ⟨v, hv⟩
    have hξ : Ψ ξ = u := by
      have hsub : ΨIso ξ = ⟨u, hu⟩ := ΨIso.apply_symm_apply ⟨u, hu⟩
      exact congrArg Subtype.val hsub
    have hη : Ψ η = v := by
      have hsub : ΨIso η = ⟨v, hv⟩ := ΨIso.apply_symm_apply ⟨v, hv⟩
      exact congrArg Subtype.val hsub
    -- Compute the preimage of `u+v` using the `τ=0` product equation.
    have hsum : Ψ (ζ ξ η) = u + v := by
      have := ProductEquation.tau0 (Ψ := Ψ) (ζ := ζ) hEq ξ η
      simpa [hξ, hη, add_comm, add_left_comm, add_assoc] using this.symm
    have hpre : ΨIso.symm ⟨u + v, huv⟩ = ζ ξ η := by
      -- apply `ΨIso` to both sides and use injectivity
      apply ΨIso.injective
      -- ΨIso (ΨIso.symm ⟨u+v, huv⟩) = ⟨u+v, huv⟩
      rw [ΨIso.apply_symm_apply]
      -- Need: ΨIso (ζ ξ η) = ⟨u+v, huv⟩, i.e., ⟨Ψ(ζ ξ η), _⟩ = ⟨u+v, huv⟩
      ext
      -- Goal: ↑⟨u+v, huv⟩ = ↑(ΨIso (ζ ξ η)), i.e., u+v = Ψ(ζ ξ η)
      simpa [Ψpos, ΨIso] using hsum.symm
    -- Now unfold `T` and use the product equation at general `τ`.
    simp only [T, hu, hv, huv, dif_pos, ξ, η, hpre]
    -- Goal: Ψ (τ + ζ ξ η) = Ψ (τ + ξ) + Ψ (τ + η)
    -- This is the product equation hEq applied at τ, ξ, η
    exact (hEq τ ξ η).symm

  -- `T τ` is additive and positive on `(0,∞)`, hence it is scalar multiplication.
  have hT_scale : ∀ τ : ℝ, ∃ k : ℝ, 0 < k ∧ ∀ {u : ℝ}, 0 < u → T τ u = k * u := by
    intro τ
    exact AdditiveOnPos.exists_mul_const_of_add_of_pos (f := T τ) (hadd := hT_add τ)
      (hpos := fun hu => hT_pos τ _ hu)

  -- Use the scaling at `u = C = Ψ 0` to identify `k = Ψ τ / C`.
  have h_mul : ∀ τ x : ℝ, Ψ (τ + x) = (Ψ τ / C) * Ψ x := by
    intro τ x
    rcases hT_scale τ with ⟨k, hkpos, hk⟩
    have hC : 0 < C := hC_pos
    have hkC : T τ C = k * C := hk (u := C) hC
    have hk0 : T τ (Ψ x) = k * Ψ x := hk (u := Ψ x) (hPos x)
    -- `T τ C = Ψ(τ+0)` and `T τ (Ψ x) = Ψ(τ+x)`.
    have hTC : T τ C = Ψ τ := by
      simp only [T, C, hC, dif_pos]
      -- Need: ΨIso.symm ⟨Ψ 0, hPos 0⟩ = 0
      have h0 : ΨIso.symm ⟨Ψ 0, hPos 0⟩ = 0 := by
        apply ΨIso.symm_apply_apply
      simp [h0]
    have hTx : T τ (Ψ x) = Ψ (τ + x) := by
      simp only [T, hPos x, dif_pos]
      -- Need: ΨIso.symm ⟨Ψ x, hPos x⟩ = x
      have hx : ΨIso.symm ⟨Ψ x, hPos x⟩ = x := by
        apply ΨIso.symm_apply_apply
      simp [hx]
    -- solve for `k`
    have hkval : k = Ψ τ / C := by
      have heq : k * C = Ψ τ := by rw [← hTC, hkC]
      field_simp [ne_of_gt hC] at heq ⊢
      linarith
    -- substitute
    calc Ψ (τ + x)
        = T τ (Ψ x) := hTx.symm
      _ = k * Ψ x := hk0
      _ = (Ψ τ / C) * Ψ x := by rw [hkval]

  -- Normalize and take logs to solve the multiplicative Cauchy equation.
  let Φ : ℝ → ℝ := fun x => Ψ x / C
  have hΦ_pos : ∀ x, 0 < Φ x := by
    intro x
    exact div_pos (hPos x) hC_pos
  have hΦ_mul : ∀ x y, Φ (x + y) = Φ x * Φ y := by
    intro x y
    have hmul := h_mul x y
    -- Ψ(x+y) = (Ψ x / C) * Ψ y
    -- Φ(x+y) = Ψ(x+y) / C = (Ψ x / C) * Ψ y / C = (Ψ x / C) * (Ψ y / C) = Φ x * Φ y
    simp [Φ]
    rw [hmul]
    simp [mul_div_assoc]

  let φ : ℝ → ℝ := fun x => Real.log (Φ x)
  have hφ_add : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    have hx : 0 < Φ x := hΦ_pos x
    have hy : 0 < Φ y := hΦ_pos y
    -- `log(uv) = log u + log v` for `u,v ≠ 0`
    have hx0 : Φ x ≠ 0 := ne_of_gt hx
    have hy0 : Φ y ≠ 0 := ne_of_gt hy
    calc
      φ (x + y) = Real.log (Φ (x + y)) := rfl
      _ = Real.log (Φ x * Φ y) := by simp [hΦ_mul x y]
      _ = Real.log (Φ x) + Real.log (Φ y) := Real.log_mul hx0 hy0
      _ = φ x + φ y := rfl
  have hφ_cont : Continuous φ := by
    -- `Φ` is continuous as quotient of continuous functions; `log` is continuous on positive reals.
    have hΦ_cont : Continuous Φ := hCont.div_const C
    refine Real.continuousOn_log.comp_continuous hΦ_cont ?_
    intro x
    -- `Φ x ∈ {0}ᶜ` because `Φ x > 0`
    have : Φ x ≠ 0 := ne_of_gt (hΦ_pos x)
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using this

  rcases continuous_additive_eq_mul φ hφ_add hφ_cont with ⟨A, hA⟩
  refine ⟨C, A, hC_pos, ?_⟩
  intro x
  -- `Φ x = exp(Ax)` so `Ψ x = C * exp(Ax)`.
  have : φ x = A * x := hA x
  have : Φ x = Real.exp (A * x) := by
    have hx : 0 < Φ x := hΦ_pos x
    -- `exp (log t) = t` for positive `t`.
    have : Real.exp (Real.log (Φ x)) = Real.exp (A * x) := by simpa [φ] using congrArg Real.exp this
    simpa [Real.exp_log hx, φ] using this
  -- conclude: `Ψ x = C * Φ x`
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hdiv : Ψ x / C = Real.exp (A * x) := by simpa [Φ] using this
  have : Ψ x = Real.exp (A * x) * C := (div_eq_iff hC_ne).1 hdiv
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

end Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative
