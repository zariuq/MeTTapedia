import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonObjective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonConstraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonAppendixTheoremI

/-!
# Shore–Johnson → KL (Path C glue)

This file packages a **clean, explicit assumption bundle** for the Shore–Johnson → KL path.
It does **not** attempt to re-prove Shore–Johnson's Appendix theorem; instead it makes every
extra hypothesis explicit and then composes the already formalized functional-equation lemmas.

The intended story is:

1. SJ1–SJ3 + regularity + expected-value constraint language ⇒ objective is equivalent to
   a separable sum of atom terms (Shore–Johnson Theorem I/II).
   In Lean this is captured by `ShoreJohnsonAppendixTheoremI.SJAppendixAssumptions`, which
   makes the Appendix regularity/richness hypotheses explicit and derives the sum-form
   equivalence `ObjEquivEV F (ofAtom d)`.
2. SJ4 (system independence) + regularity ⇒ logarithmic functional equation on the ratio
   kernel (Shore–Johnson Theorem III).
3. Hence the objective is KL up to scale.

Steps (1) and (2) are not fully formalized here; the point is to **keep them explicit** as
assumptions while still providing a rigorously composable KL conclusion.

Concrete discharge note:
- The Appendix-style regularity axiom “`StationaryEV g p q cs ↔ IsMinimizer (ofAtom d) p cs q`”
  is *not* vacuous: for the KL atom `d := klAtom` and kernel `g := gKL` (i.e. `log (w/u)`),
  it is proven (sorry-free) as
  `Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixKL.stationaryEV_iff_isMinimizer_ofAtom_klAtom`.

What we *do* provide (in addition to the atom-level `log` / `klAtom` identities) is an
**inference-level** corollary: once an inference operator `I` is realized by some objective `F`
and `F` is objective-equivalent to an atom-sum objective `ofAtom d`, then the atom-level KL
identity implies that `I` is realized (for **positive priors**) by minimizing a constant multiple
of the KL atom objective.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonPathC

open Classical
open Finset BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonKL
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixTheoremI
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonProof

/-! ## Path C: explicit assumption bundle -/

structure SJPathCAssumptions where
  /-- Inference operator (SJ1–SJ4 live here). -/
  I : ShoreJohnsonInference.InferenceMethod
  /-- Objective functional realizing inference on expected-value constraint sets. -/
  F : ObjectiveFunctional
  /-- Atom divergence used for the sum-form objective `ofAtom d`. -/
  d : ℝ → ℝ → ℝ
  /-- Bridge hypothesis: inference is realized by `F` (restricted to expected-value constraints). -/
  realizesEV : RealizesEV I F
  /-- Appendix-style regularity/richness assumptions yielding the sum-form equivalence. -/
  appendix : SJAppendixAssumptions F d
  /-- Interior regime hypothesis: inferred posteriors (for the EV constraint language) lie in the
  positive simplex, so the Appendix-style stationarity conditions are meaningful. -/
  inferPos :
    ∀ {n : ℕ} (p : ProbDist n) (cs : ShoreJohnsonConstraints.EVConstraintSet n) (q : ProbDist n),
      I.Infer p (ShoreJohnsonConstraints.toConstraintSet cs) q → ∀ i, 0 < q.p i
  /-- Regularity: `d(0, x) = 0` for all `x`.
  NOTE: Previously this was bundled with system independence via `SJSystemIndependenceAtom`.
  We now separate regularity from the (too strong) universal additivity requirement, since
  `klAtom` only satisfies the positivity-restricted version `SJSystemIndependenceAtomPos`. -/
  regularAtom : RegularAtom d
  /-- Ratio-form hypothesis: `d(w,u)=w*g(w/u)` for `w,u>0`. -/
  ratio : ShoreJohnsonTheorem.RatioForm d
  /-- Multiplicative Cauchy equation for the ratio kernel on `(0,∞)`. -/
  gMul : MulCauchyOnPos ratio.g
  /-- Regularity gate excluding Hamel-basis pathologies. -/
  gMeas : Measurable ratio.g
  /-- Regularity gate for the probability-domain log conclusion. -/
  d1Meas : Measurable (d 1)

/-! ## Deriving Cauchy equation for d(1,·) from ratio form + MulCauchyOnPos -/

/-- From `RatioForm` and `MulCauchyOnPos`, derive the multiplicative Cauchy equation for `d(1, ·)`. -/
theorem d_one_cauchy_of_ratioForm_mulCauchyOnPos (d : ℝ → ℝ → ℝ) (ratio : ShoreJohnsonTheorem.RatioForm d)
    (gMul : MulCauchyOnPos ratio.g) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ ≤ 1 → 0 < q₂ → q₂ ≤ 1 → d 1 (q₁ * q₂) = d 1 q₁ + d 1 q₂ := by
  intro q₁ q₂ hq₁_pos _hq₁_le1 hq₂_pos _hq₂_le1
  -- d(1, q) = g(1/q) for q > 0 (from ratio form)
  have h1 : d 1 q₁ = ratio.g q₁⁻¹ := by
    have := ratio.eq_mul_g_div 1 q₁ one_pos hq₁_pos
    simp only [one_mul, one_div] at this
    exact this
  have h2 : d 1 q₂ = ratio.g q₂⁻¹ := by
    have := ratio.eq_mul_g_div 1 q₂ one_pos hq₂_pos
    simp only [one_mul, one_div] at this
    exact this
  have hprod_pos : 0 < q₁ * q₂ := mul_pos hq₁_pos hq₂_pos
  have h3 : d 1 (q₁ * q₂) = ratio.g (q₁ * q₂)⁻¹ := by
    have := ratio.eq_mul_g_div 1 (q₁ * q₂) one_pos hprod_pos
    simp only [one_mul, one_div] at this
    exact this
  -- (q₁*q₂)⁻¹ = q₁⁻¹ * q₂⁻¹
  have hrecip : (q₁ * q₂)⁻¹ = q₁⁻¹ * q₂⁻¹ := by rw [mul_inv_rev, mul_comm]
  -- g(q₁⁻¹ * q₂⁻¹) = g(q₁⁻¹) + g(q₂⁻¹) by MulCauchyOnPos
  have hq₁_inv_pos : 0 < q₁⁻¹ := inv_pos.mpr hq₁_pos
  have hq₂_inv_pos : 0 < q₂⁻¹ := inv_pos.mpr hq₂_pos
  have hg_cauchy := gMul q₁⁻¹ q₂⁻¹ hq₁_inv_pos hq₂_inv_pos
  -- Combine
  calc d 1 (q₁ * q₂)
      = ratio.g (q₁ * q₂)⁻¹ := h3
    _ = ratio.g (q₁⁻¹ * q₂⁻¹) := by rw [hrecip]
    _ = ratio.g q₁⁻¹ + ratio.g q₂⁻¹ := hg_cauchy
    _ = d 1 q₁ + d 1 q₂ := by rw [← h1, ← h2]

/-! ## KL conclusion under explicit assumptions -/

theorem pathC_log_on_probabilities (h : SJPathCAssumptions) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → h.d 1 q = C * Real.log q := by
  -- Derive Cauchy equation for d(1, ·) from ratio form + MulCauchyOnPos
  have hCauchy := d_one_cauchy_of_ratioForm_mulCauchyOnPos h.d h.ratio h.gMul
  -- Apply the general Cauchy → log theorem
  exact mul_cauchy_Ioc_eq_const_mul_log (h.d 1) hCauchy h.d1Meas

theorem pathC_klAtom (h : SJPathCAssumptions) :
    ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → h.d w u = C * klAtom w u := by
  exact ratioForm_eq_const_mul_klAtom_of_measurable h.d h.ratio h.gMul h.gMeas

/-! ## From atom-level KL to objective-level KL -/

theorem sum_d_eq_const_mul_klAtom_of_posPrior {n : ℕ}
    (d : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u)
    (hReg : RegularAtom d)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (q : ProbDist n) :
    (∑ i : Fin n, d (q.p i) (p.p i)) = ∑ i : Fin n, C * klAtom (q.p i) (p.p i) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hqi : q.p i = 0
  · simpa [hqi, klAtom] using (hReg (p.p i))
  · have hq_pos : 0 < q.p i :=
      lt_of_le_of_ne (q.nonneg i) (Ne.symm hqi)
    have hp_pos : 0 < p.p i := hp i
    simp [hC (q.p i) (p.p i) hq_pos hp_pos, klAtom]

theorem isMinimizer_ofAtom_iff_ofAtom_const_mul_klAtom_of_posPrior {n : ℕ}
    (d : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u)
    (hReg : RegularAtom d)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (S : ShoreJohnsonInference.ConstraintSet n) (q : ProbDist n) :
    IsMinimizer (ofAtom d) p S q ↔ IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p S q := by
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hq_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q
    have hq'_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q'
    dsimp [ofAtom] at hle
    -- Transport the inequality through the pointwise `d = C * klAtom` identities.
    have hle' :
        (∑ i : Fin n, C * klAtom (q.p i) (p.p i)) ≤ ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := by
      calc
        (∑ i : Fin n, C * klAtom (q.p i) (p.p i))
            = ∑ i : Fin n, d (q.p i) (p.p i) := by simpa using hq_eq.symm
        _ ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := hle
        _ = ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := by simpa using hq'_eq
    simpa [ofAtom] using hle'
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hq_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q
    have hq'_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q'
    dsimp [ofAtom] at hle
    have hle' :
        (∑ i : Fin n, d (q.p i) (p.p i)) ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := by
      calc
        (∑ i : Fin n, d (q.p i) (p.p i))
            = ∑ i : Fin n, C * klAtom (q.p i) (p.p i) := by simpa using hq_eq
        _ ≤ ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := hle
        _ = ∑ i : Fin n, d (q'.p i) (p.p i) := by simpa using hq'_eq.symm
    simpa [ofAtom] using hle'

/-! ## Inference-level conclusion (for positive priors) -/

theorem pathC_infer_iff_isMinimizer_ofAtom_const_mul_klAtom_of_posPrior (h : SJPathCAssumptions) :
    ∃ C : ℝ, ∀ {n : ℕ} (p : ProbDist n) (cs : ShoreJohnsonConstraints.EVConstraintSet n)
      (q : ProbDist n), (∀ i, 0 < p.p i) →
      (h.I.Infer p (ShoreJohnsonConstraints.toConstraintSet cs) q ↔
        (∀ i, 0 < q.p i) ∧
          IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (ShoreJohnsonConstraints.toConstraintSet cs) q) := by
  rcases pathC_klAtom h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n p cs q hp
  have hInferF :
      h.I.Infer p (ShoreJohnsonConstraints.toConstraintSet cs) q ↔
        IsMinimizer h.F p (ShoreJohnsonConstraints.toConstraintSet cs) q :=
    h.realizesEV.infer_iff_minimizer_ev p cs q
  have hKl :
      IsMinimizer (ofAtom h.d) p (ShoreJohnsonConstraints.toConstraintSet cs) q ↔
        IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (ShoreJohnsonConstraints.toConstraintSet cs) q :=
    isMinimizer_ofAtom_iff_ofAtom_const_mul_klAtom_of_posPrior
      h.d C hC h.regularAtom p hp (ShoreJohnsonConstraints.toConstraintSet cs) q
  constructor
  · intro hInfer
    have hqPos : ∀ i, 0 < q.p i := h.inferPos p cs q hInfer
    have hMinF : IsMinimizer h.F p (ShoreJohnsonConstraints.toConstraintSet cs) q := hInferF.1 hInfer
    have hq_mem : q ∈ ShoreJohnsonConstraints.toConstraintSet cs := hMinF.1
    have hMinD : IsMinimizer (ofAtom h.d) p (ShoreJohnsonConstraints.toConstraintSet cs) q :=
      (isMinimizer_iff_isMinimizer_ofAtom_of_pos h.appendix p hp cs q hq_mem hqPos).1 hMinF
    have hMinKl : IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p
        (ShoreJohnsonConstraints.toConstraintSet cs) q := (hKl.1 hMinD)
    exact ⟨hqPos, hMinKl⟩
  · rintro ⟨hqPos, hMinKl⟩
    have hq_mem : q ∈ ShoreJohnsonConstraints.toConstraintSet cs := hMinKl.1
    have hMinD : IsMinimizer (ofAtom h.d) p (ShoreJohnsonConstraints.toConstraintSet cs) q :=
      (hKl.2 hMinKl)
    have hMinF : IsMinimizer h.F p (ShoreJohnsonConstraints.toConstraintSet cs) q :=
      (isMinimizer_iff_isMinimizer_ofAtom_of_pos h.appendix p hp cs q hq_mem hqPos).2 hMinD
    exact (hInferF.2 hMinF)

/-! ### Specialized statement for expected-value constraint sets -/

theorem pathC_infer_ev_iff_isMinimizer_ofAtom_const_mul_klAtom_of_posPrior (h : SJPathCAssumptions) :
    ∃ C : ℝ, ∀ {n : ℕ} (p : ProbDist n) (cs : ShoreJohnsonConstraints.EVConstraintSet n)
      (q : ProbDist n), (∀ i, 0 < p.p i) →
      (h.I.Infer p (ShoreJohnsonConstraints.toConstraintSet cs) q ↔
        (∀ i, 0 < q.p i) ∧
          IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (ShoreJohnsonConstraints.toConstraintSet cs) q) := by
  exact pathC_infer_iff_isMinimizer_ofAtom_const_mul_klAtom_of_posPrior h

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonPathC
