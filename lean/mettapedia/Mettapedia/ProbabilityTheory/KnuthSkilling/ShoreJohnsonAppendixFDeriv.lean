import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Shore–Johnson Appendix: Fréchet derivative helpers for `shift2`

This file provides a small amount of multivariate-calculus infrastructure for the Shore–Johnson
Appendix proof.

We keep it separate from `ShoreJohnsonAppendix.lean` so the core `shift2`/`shift2Prob` machinery
can remain 1D-derivative-based, while later work can opt-in to a cleaner `HasFDerivAt` story.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix

open Classical
open scoped BigOperators

/-! ## `shift2` as an affine map -/

theorem shift2_eq_add_smul {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j) :
    shift2 q i j t = q + (t - q i) • (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) := by
  funext k
  by_cases hki : k = i
  · -- `Pi.single i 1 i = 1` and `Pi.single j 1 i = 0` since `i ≠ j`.
    simp [shift2, hki, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_eq_add_neg]
  · by_cases hkj : k = j
    · have hji : j ≠ i := ne_comm.mp hij
      -- `Pi.single j 1 j = 1` and `Pi.single i 1 j = 0` since `j ≠ i`.
      simp [shift2, hkj, hji, Pi.single_eq_same, sub_eq_add_neg]
      ac_rfl
    · -- Outside the shifted coordinates, both sides are `q k`.
      simp [shift2, hki, hkj, Pi.single_eq_of_ne]

/-! ## Fréchet derivative of `shift2` -/

theorem hasFDerivAt_shift2 {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t₀ : ℝ) (hij : i ≠ j) :
    HasFDerivAt (fun t : ℝ => shift2 q i j t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)))
      t₀ := by
  -- Use the affine form and the chain rule.
  have hshift :
      (fun t : ℝ => shift2 q i j t) =
        fun t : ℝ => q + (t - q i) • (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) := by
    funext t
    simp [shift2_eq_add_smul (q := q) (i := i) (j := j) (t := t) hij]
  -- Derivative of `t ↦ t - q i` is `id`.
  have hsub : HasFDerivAt (fun t : ℝ => t - q i) (.id ℝ ℝ) t₀ :=
    hasFDerivAt_sub_const (x := t₀) (q i)
  -- The map `t ↦ t • v` is linear, hence its derivative is itself.
  let v : Fin n → ℝ := Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)
  have hsmul : HasFDerivAt ((1 : ℝ →L[ℝ] ℝ).smulRight v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) (t₀ - q i) := by
    simpa using (ContinuousLinearMap.hasFDerivAt (e := (1 : ℝ →L[ℝ] ℝ).smulRight v) (x := t₀ - q i))
  have hcomp :
      HasFDerivAt (fun t : ℝ => (t - q i) • v)
        (((1 : ℝ →L[ℝ] ℝ).smulRight v).comp (.id ℝ ℝ)) t₀ := by
    simpa [v] using hsmul.comp t₀ hsub
  have hadd :
      HasFDerivAt (fun t : ℝ => q + (t - q i) • v)
        (((1 : ℝ →L[ℝ] ℝ).smulRight v).comp (.id ℝ ℝ)) t₀ := by
    -- `q` is constant in `t`, so adding it doesn't change the derivative.
    simpa [v] using (hasFDerivAt_const q t₀).add hcomp
  -- Clean up the `comp id` and rewrite back to `shift2`.
  simpa [hshift, v, ContinuousLinearMap.comp_id] using hadd

/-- Compose a Fréchet-derivative for `F` with the `shift2` curve. -/
theorem hasDerivAt_comp_shift2_of_hasFDerivAt {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (q : Fin n → ℝ) (i j : Fin n) (t₀ : ℝ) (hij : i ≠ j)
    (L : (Fin n → ℝ) →L[ℝ] ℝ)
    (hF : HasFDerivAt F L (shift2 q i j t₀)) :
    HasDerivAt (fun t : ℝ => F (shift2 q i j t))
      (L (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))) t₀ := by
  have hshift := hasFDerivAt_shift2 (q := q) (i := i) (j := j) (t₀ := t₀) hij
  have hcomp :
      HasFDerivAt (fun t : ℝ => F (shift2 q i j t))
        (L.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))))
        t₀ := hF.comp t₀ hshift
  have hder := hcomp.hasDerivAt
  -- `((L.comp A) 1) = L (A 1)` and `(smulRight v) 1 = v`.
  simpa using hder

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
