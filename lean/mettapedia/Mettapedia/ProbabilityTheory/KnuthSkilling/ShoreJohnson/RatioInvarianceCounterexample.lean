import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Counterexample: quadratic loss is not ratio-invariant

This file shows that the ratio-invariant derivative axiom excludes quadratic loss.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.RatioInvarianceCounterexample

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

/-- Quadratic atom loss. -/
noncomputable def quadAtom (w u : ℝ) : ℝ :=
  (w - u) ^ 2

/-- Derivative of the quadratic atom with respect to its first argument. -/
noncomputable def quadAtomDeriv (q p : ℝ) : ℝ :=
  2 * (q - p)

lemma hasDerivAt_quadAtom (q p : ℝ) :
    HasDerivAt (fun t => quadAtom t p) (quadAtomDeriv q p) q := by
  have h : HasDerivAt (fun t => t - p) 1 q := (hasDerivAt_id q).sub_const p
  have hpow := h.pow 2
  -- `h.pow 2` gives derivative `2 * (q - p) ^ 1 * 1`.
  simpa [quadAtom, quadAtomDeriv, pow_one, mul_one, mul_assoc, mul_left_comm, mul_comm] using hpow

lemma hasDerivAt_quadAtom_pos (q p : ℝ) (_hq : 0 < q) (_hp : 0 < p) :
    HasDerivAt (fun t => quadAtom t p) (quadAtomDeriv q p) q := by
  simpa using hasDerivAt_quadAtom q p

theorem not_derivRatioInvariant_quadAtom :
    ¬ DerivRatioInvariant (ofAtom quadAtom)
        ⟨(ExtractGRegularity.ofAtom quadAtom quadAtomDeriv hasDerivAt_quadAtom_pos).has_shift2_deriv⟩ := by
  intro hRatio
  -- Choose explicit positive distributions with matching ratios on two coordinates.
  let a1 : ℝ := 1 / 8
  let a2 : ℝ := 1 / 4
  let b : ℝ := 1 / 4
  have ha1 : 0 < a1 := by norm_num [a1]
  have ha2 : 0 < a2 := by norm_num [a2]
  have hb : 0 < b := by norm_num [b]
  have hsum1 : a1 + b < 1 := by norm_num [a1, b]
  have hsum2 : a2 + b < 1 := by norm_num [a2, b]
  have hsumq1 : 2 * a1 + b < 1 := by norm_num [a1, b]
  have hsumq2 : 2 * a2 + b < 1 := by norm_num [a2, b]

  let p1 : ProbDist 3 :=
    GradientSeparability.probDist3 a1 b ha1 hb hsum1
  let q1 : ProbDist 3 :=
    GradientSeparability.probDist3 (2 * a1) b (by nlinarith [ha1]) hb hsumq1
  let p2 : ProbDist 3 :=
    GradientSeparability.probDist3 a2 b ha2 hb hsum2
  let q2 : ProbDist 3 :=
    GradientSeparability.probDist3 (2 * a2) b (by nlinarith [ha2]) hb hsumq2

  have hp1 : ∀ k, 0 < p1.p k := by
    simpa [p1] using
      (GradientSeparability.probDist3_pos a1 b ha1 hb hsum1)
  have hq1 : ∀ k, 0 < q1.p k := by
    simpa [q1] using
      (GradientSeparability.probDist3_pos (2 * a1) b (by nlinarith [ha1]) hb hsumq1)
  have hp2 : ∀ k, 0 < p2.p k := by
    simpa [p2] using
      (GradientSeparability.probDist3_pos a2 b ha2 hb hsum2)
  have hq2 : ∀ k, 0 < q2.p k := by
    simpa [q2] using
      (GradientSeparability.probDist3_pos (2 * a2) b (by nlinarith [ha2]) hb hsumq2)

  have hij : (0 : Fin 3) ≠ 1 := by decide

  have hratio_i : q1.p 0 / p1.p 0 = q2.p 0 / p2.p 0 := by
    simp [p1, q1, p2, q2, GradientSeparability.probDist3, a1, a2, b]
  have hratio_j : q1.p 1 / p1.p 1 = q2.p 1 / p2.p 1 := by
    simp [p1, q1, p2, q2, GradientSeparability.probDist3, a1, a2, b]

  let hExtract :=
    ExtractGRegularity.ofAtom quadAtom quadAtomDeriv hasDerivAt_quadAtom_pos
  let hDiff : HasShift2Deriv (ofAtom quadAtom) := ⟨hExtract.has_shift2_deriv⟩
  have hEqChoose :=
    hRatio (p := p1) (q := q1) (p' := p2) (q' := q2)
      (i := 0) (j := 1) (i' := 0) (j' := 1)
      (hij := hij) (hi'j' := hij)
      (hp := hp1) (hq := hq1) (hp' := hp2) (hq' := hq2)
      hratio_i hratio_j

  have hL1 := shift2_deriv_ofAtom quadAtom quadAtomDeriv hasDerivAt_quadAtom_pos p1 q1 0 1 hij hp1 hq1
  have hL2 := shift2_deriv_ofAtom quadAtom quadAtomDeriv hasDerivAt_quadAtom_pos p2 q2 0 1 hij hp2 hq2

  have hChoose1 :
      Classical.choose (hDiff.deriv_exists p1 q1 0 1 hij hp1 hq1) =
        quadAtomDeriv (q1.p 0) (p1.p 0) - quadAtomDeriv (q1.p 1) (p1.p 1) := by
    have hSpec := Classical.choose_spec (hDiff.deriv_exists p1 q1 0 1 hij hp1 hq1)
    exact HasDerivAt.unique hSpec hL1

  have hChoose2 :
      Classical.choose (hDiff.deriv_exists p2 q2 0 1 hij hp2 hq2) =
        quadAtomDeriv (q2.p 0) (p2.p 0) - quadAtomDeriv (q2.p 1) (p2.p 1) := by
    have hSpec := Classical.choose_spec (hDiff.deriv_exists p2 q2 0 1 hij hp2 hq2)
    exact HasDerivAt.unique hSpec hL2

  have hVal1 :
      quadAtomDeriv (q1.p 0) (p1.p 0) - quadAtomDeriv (q1.p 1) (p1.p 1) = (1 / 4 : ℝ) := by
    simp [quadAtomDeriv, p1, q1, GradientSeparability.probDist3, a1, b]
    norm_num
  have hVal2 :
      quadAtomDeriv (q2.p 0) (p2.p 0) - quadAtomDeriv (q2.p 1) (p2.p 1) = (1 / 2 : ℝ) := by
    simp [quadAtomDeriv, p2, q2, GradientSeparability.probDist3, a2, b]
    norm_num

  have hEq' :
      (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
    calc
      (1 / 4 : ℝ)
          = quadAtomDeriv (q1.p 0) (p1.p 0) - quadAtomDeriv (q1.p 1) (p1.p 1) := hVal1.symm
      _ = Classical.choose (hDiff.deriv_exists p1 q1 0 1 hij hp1 hq1) := by
            simp [hChoose1]
      _ = Classical.choose (hDiff.deriv_exists p2 q2 0 1 hij hp2 hq2) := hEqChoose
      _ = quadAtomDeriv (q2.p 0) (p2.p 0) - quadAtomDeriv (q2.p 1) (p2.p 1) := by
            simp [hChoose2]
      _ = (1 / 2 : ℝ) := hVal2
  norm_num at hEq'

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.RatioInvarianceCounterexample
