import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy Inequalities for Binary Prediction (Hutter 2005, Lemma 3.11s)

Hutter's Chapter 3 uses a small collection of "distances" between the next-step predictive
distributions of `μ` and a predictor `ξ`, and relates them by a set of entropy inequalities.

This file formalizes the core inequality used in the convergence pipeline:

* (Lemma 3.11s, binary case) **squared distance is bounded by relative entropy**.

We work in the binary setting (`|X| = 2`) and represent a distribution by a single number
`y ∈ (0,1)` meaning `P(true) = y` and `P(false) = 1-y`.

The definitions here are purely analytic; later files connect them to conditional probabilities
derived from `PrefixMeasure`s.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

namespace Entropy

/-- The binary "entropy core" function `φ(y) = y log y + (1-y) log(1-y)`. -/
abbrev phi (y : ℝ) : ℝ :=
  y * Real.log y + (1 - y) * Real.log (1 - y)

/-- Formal derivative of `phi` on `(0,1)`: `φ'(y) = log y - log(1-y)`. -/
abbrev phiDeriv (y : ℝ) : ℝ :=
  Real.log y - Real.log (1 - y)

/-- Formal second derivative of `phi` on `(0,1)`: `φ''(y) = 1/y + 1/(1-y)`. -/
abbrev phiDeriv2 (y : ℝ) : ℝ :=
  y⁻¹ + (1 - y)⁻¹

/-- Binary relative entropy `d(y||z)` written as a Bregman divergence of `phi`.

For `0 < z < 1` this agrees with the usual formula
`y log (y/z) + (1-y) log ((1-y)/(1-z))`.
-/
abbrev klBinary (y z : ℝ) : ℝ :=
  phi y - phi z - (y - z) * phiDeriv z

/-- Squared distance between binary probability vectors `(1-y,y)` and `(1-z,z)`.
This is Hutter's `s` for `|X| = 2`. -/
abbrev sqDistBinary (y z : ℝ) : ℝ :=
  (y - z) ^ 2 + ((1 - y) - (1 - z)) ^ 2

lemma sqDistBinary_eq_two_mul (y z : ℝ) : sqDistBinary y z = 2 * (y - z) ^ 2 := by
  simp [sqDistBinary]
  ring

/-- A calculus lemma used for Lemma 3.11s: `y*(1-y) ≤ 1/4` (true for all real `y`). -/
lemma mul_one_sub_le_quarter (y : ℝ) : y * (1 - y) ≤ (1 / 4 : ℝ) := by
  have hsq : 0 ≤ (y - (1 / 2 : ℝ)) ^ 2 := by nlinarith
  nlinarith

/-- `HasDerivWithinAt` for `phi` on `(0,1)`. -/
lemma hasDerivWithinAt_phi {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt phi (phiDeriv y) (Set.Ioo (0 : ℝ) 1) y := by
  have hy0 : y ≠ 0 := ne_of_gt hy.1
  have hyne1 : y ≠ 1 := ne_of_lt hy.2
  have hy1 : 1 - y ≠ 0 := by
    intro h
    have : (1 : ℝ) = y := sub_eq_zero.mp h
    exact hyne1 (by simpa using this.symm)
  have h1 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log y + 1) y :=
    Real.hasDerivAt_mul_log hy0
  have hsub : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
  have h2 :
      HasDerivAt (fun y : ℝ => ((1 : ℝ) - y) * Real.log ((1 : ℝ) - y))
        (-(Real.log ((1 : ℝ) - y) + 1)) y := by
      have hmul :
          HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log ((1 : ℝ) - y) + 1) ((1 : ℝ) - y) :=
        Real.hasDerivAt_mul_log hy1
      change
        HasDerivAt ((fun t : ℝ => t * Real.log t) ∘ (fun y : ℝ => (1 : ℝ) - y))
          (-(Real.log ((1 : ℝ) - y) + 1)) y
      simpa [Function.comp, mul_assoc, mul_comm, mul_left_comm, neg_add] using hmul.comp y hsub
  have hsum : HasDerivAt phi ((Real.log y + 1) + (-(Real.log ((1 : ℝ) - y) + 1))) y := by
    exact h1.add h2
  have : HasDerivWithinAt phi ((Real.log y + 1) - (Real.log ((1 : ℝ) - y) + 1)) (Set.Ioo (0 : ℝ) 1)
        y := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum.hasDerivWithinAt
  simpa [phiDeriv, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this

/-- `HasDerivWithinAt` for `phiDeriv` on `(0,1)`. -/
lemma hasDerivWithinAt_phiDeriv {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt phiDeriv (phiDeriv2 y) (Set.Ioo (0 : ℝ) 1) y := by
  have hy0 : y ≠ 0 := ne_of_gt hy.1
  have hyne1 : y ≠ 1 := ne_of_lt hy.2
  have hy1 : 1 - y ≠ 0 := by
    intro h
    have : (1 : ℝ) = y := sub_eq_zero.mp h
    exact hyne1 (by simpa using this.symm)
  have hlog : HasDerivAt (fun y : ℝ => Real.log y) (y⁻¹) y :=
    Real.hasDerivAt_log hy0
  have hsub : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
  have hlog2 :
      HasDerivAt (fun y : ℝ => Real.log ((1 : ℝ) - y)) (((1 : ℝ) - y)⁻¹ * (-1)) y := by
    have := (Real.hasDerivAt_log hy1)
    change
      HasDerivAt (Real.log ∘ (fun y : ℝ => (1 : ℝ) - y))
        (((1 : ℝ) - y)⁻¹ * (-1)) y
    simpa [Function.comp, mul_assoc, mul_comm, mul_left_comm] using this.comp y hsub
  have h : HasDerivAt phiDeriv (y⁻¹ - (((1 : ℝ) - y)⁻¹ * (-1))) y := by
    exact hlog.sub hlog2
  have : HasDerivAt phiDeriv (y⁻¹ + ((1 : ℝ) - y)⁻¹) y := by
    simpa [mul_assoc, sub_eq_add_neg] using h
  simpa [phiDeriv2] using this.hasDerivWithinAt

/-- The function used to prove Lemma 3.11s: `f(y) = KL(y||z) - s(y,z)`. -/
abbrev f (z : ℝ) (y : ℝ) : ℝ :=
  klBinary y z - sqDistBinary y z

/-- Formal derivative of `f z` on `(0,1)`. -/
abbrev fDeriv (z : ℝ) (y : ℝ) : ℝ :=
  phiDeriv y - phiDeriv z - 4 * (y - z)

/-- Formal second derivative of `f z` on `(0,1)`. -/
abbrev fDeriv2 (y : ℝ) : ℝ :=
  phiDeriv2 y - 4

lemma hasDerivWithinAt_sqDistBinary {z y : ℝ} :
    HasDerivWithinAt (fun y : ℝ => sqDistBinary y z) (4 * (y - z)) (Set.Ioo (0 : ℝ) 1) y := by
  have hsimp : (fun y : ℝ => sqDistBinary y z) = fun y => 2 * (y - z) ^ 2 := by
    funext y
    simp [sqDistBinary_eq_two_mul]
  have hsub : HasDerivAt (fun y : ℝ => y - z) (1 : ℝ) y := by
    simpa using (hasDerivAt_id y).sub_const z
  have hpow : HasDerivAt (fun y : ℝ => (y - z) ^ 2) (2 * (y - z)) y := by
    change HasDerivAt ((fun y : ℝ => y - z) ^ 2) (2 * (y - z)) y
    simpa using (hsub.pow 2)
  have hmul : HasDerivAt (fun y : ℝ => 2 * (y - z) ^ 2) (2 * (2 * (y - z))) y :=
    HasDerivAt.const_mul (2 : ℝ) hpow
  have hmul' : HasDerivAt (fun y : ℝ => 2 * (y - z) ^ 2) (4 * (y - z)) y := by
    convert hmul using 1
    ring
  simpa [hsimp] using hmul'.hasDerivWithinAt

lemma hasDerivWithinAt_klBinary {z y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun y : ℝ => klBinary y z) (phiDeriv y - phiDeriv z) (Set.Ioo (0 : ℝ) 1) y := by
  unfold klBinary
  have hphi : HasDerivWithinAt phi (phiDeriv y) (Set.Ioo (0 : ℝ) 1) y := hasDerivWithinAt_phi (y := y) hy
  have hconst : HasDerivWithinAt (fun _y : ℝ => phi z) 0 (Set.Ioo (0 : ℝ) 1) y :=
    (hasDerivAt_const y (phi z)).hasDerivWithinAt
  have hsub1 : HasDerivWithinAt (fun y : ℝ => phi y - phi z) (phiDeriv y) (Set.Ioo (0 : ℝ) 1) y := by
    exact hphi.sub_const (phi z)
  have hlin :
      HasDerivWithinAt (fun y : ℝ => (y - z) * phiDeriv z) (phiDeriv z) (Set.Ioo (0 : ℝ) 1) y := by
    have hsub : HasDerivAt (fun y : ℝ => y - z) (1 : ℝ) y := by
      simpa using (hasDerivAt_id y).sub_const z
    have hmul : HasDerivAt (fun y : ℝ => (y - z) * phiDeriv z) (1 * phiDeriv z) y := by
      simpa [mul_assoc] using hsub.mul_const (phiDeriv z)
    simpa using hmul.hasDerivWithinAt
  have hsub2 :
      HasDerivWithinAt (fun y : ℝ => (phi y - phi z) - (y - z) * phiDeriv z)
        (phiDeriv y - phiDeriv z) (Set.Ioo (0 : ℝ) 1) y :=
    hsub1.sub hlin
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using hsub2

lemma hasDerivWithinAt_f {z y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (f z) (fDeriv z y) (Set.Ioo (0 : ℝ) 1) y := by
  unfold f
  have hkl :
      HasDerivWithinAt (fun y : ℝ => klBinary y z) (phiDeriv y - phiDeriv z) (Set.Ioo (0 : ℝ) 1) y :=
    hasDerivWithinAt_klBinary (z := z) (y := y) hy
  have hsq : HasDerivWithinAt (fun y : ℝ => sqDistBinary y z) (4 * (y - z)) (Set.Ioo (0 : ℝ) 1) y :=
    hasDerivWithinAt_sqDistBinary (z := z) (y := y)
  have h := hkl.sub hsq
  exact h

/-- `HasDerivWithinAt` for `fDeriv z` on `(0,1)`. -/
lemma hasDerivWithinAt_fDeriv {z y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fDeriv z) (fDeriv2 y) (Set.Ioo (0 : ℝ) 1) y := by
  unfold fDeriv fDeriv2
  have hphi : HasDerivWithinAt phiDeriv (phiDeriv2 y) (Set.Ioo (0 : ℝ) 1) y :=
    hasDerivWithinAt_phiDeriv (y := y) hy
  have hconst : HasDerivWithinAt (fun _y : ℝ => phiDeriv z) 0 (Set.Ioo (0 : ℝ) 1) y :=
    (hasDerivAt_const y (phiDeriv z)).hasDerivWithinAt
  have hsub1 :
      HasDerivWithinAt (fun y : ℝ => phiDeriv y - phiDeriv z) (phiDeriv2 y) (Set.Ioo (0 : ℝ) 1) y := by
    exact hphi.sub_const (phiDeriv z)
  have hlin : HasDerivWithinAt (fun y : ℝ => 4 * (y - z)) (4 : ℝ) (Set.Ioo (0 : ℝ) 1) y := by
    have hsub : HasDerivAt (fun y : ℝ => y - z) (1 : ℝ) y := by
      simpa using (hasDerivAt_id y).sub_const z
    have hmul : HasDerivAt (fun y : ℝ => 4 * (y - z)) (4 * 1) y :=
      HasDerivAt.const_mul (4 : ℝ) hsub
    simpa using hmul.hasDerivWithinAt
  have h := hsub1.sub hlin
  exact h

/-- Lemma 3.11s (binary case): squared distance is bounded by relative entropy.

This is the `|X|=2` specialization of Hutter's `s < d` inequality. -/
theorem sqDistBinary_le_klBinary {y z : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    sqDistBinary y z ≤ klBinary y z := by
  -- Work with `f z y = klBinary y z - sqDistBinary y z`.
  have hcont : ContinuousOn (f z) (Set.Ioo (0 : ℝ) 1) := by
    have h : Continuous (f z) := by
      unfold f klBinary phi sqDistBinary
      fun_prop
    exact h.continuousOn
  have hconv : ConvexOn ℝ (Set.Ioo (0 : ℝ) 1) (f z) := by
    refine
      convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Ioo (0 : ℝ) 1) (f := f z) (f' := fDeriv z)
        (f'' := fDeriv2) (convex_Ioo (0 : ℝ) 1) hcont ?_ ?_ ?_
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hx
      simpa using hasDerivWithinAt_f (z := z) (y := x) hx'
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hx
      simpa using hasDerivWithinAt_fDeriv (z := z) (y := x) hx'
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hx
      have hx0 : 0 < x := hx'.1
      have hx1 : x < 1 := hx'.2
      have hxmul_pos : 0 < x * (1 - x) := by
        have h1x : 0 < 1 - x := sub_pos.2 hx1
        exact mul_pos hx0 h1x
      have hle : x * (1 - x) ≤ (1 / 4 : ℝ) := mul_one_sub_le_quarter x
      have hinv : (4 : ℝ) ≤ (x * (1 - x))⁻¹ := by
        have := one_div_le_one_div_of_le hxmul_pos hle
        simpa [one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
      have hx1' : (1 - x) ≠ 0 := by
        intro h
        have : (1 : ℝ) = x := sub_eq_zero.mp h
        exact (ne_of_lt hx1) (by simpa using this.symm)
      have hphi2 : phiDeriv2 x = (x * (1 - x))⁻¹ := by
        unfold phiDeriv2
        field_simp [hx0.ne', hx1']
        ring
      have : 0 ≤ fDeriv2 x := by
        unfold fDeriv2
        have : (4 : ℝ) ≤ phiDeriv2 x := by simpa [hphi2] using hinv
        linarith
      simpa using this
  have hzmem : z ∈ interior (Set.Ioo (0 : ℝ) 1) := by
    simpa [interior_Ioo] using hz
  have hderiv0 : derivWithin (f z) (Set.Ioi z) z = 0 := by
    have hz_nhds : Set.Ioo (0 : ℝ) 1 ∈ nhds z :=
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).mem_nhds hz
    have hDerivAt : HasDerivAt (f z) (fDeriv z z) z :=
      (hasDerivWithinAt_f (z := z) (y := z) hz).hasDerivAt hz_nhds
    have hwithin : HasDerivWithinAt (f z) (fDeriv z z) (Set.Ioi z) z :=
      hDerivAt.hasDerivWithinAt
    have hEq : derivWithin (f z) (Set.Ioi z) z = fDeriv z z :=
      hwithin.derivWithin (uniqueDiffWithinAt_Ioi z)
    have h0 : fDeriv z z = 0 := by
      unfold fDeriv
      ring
    simpa [h0] using hEq
  have hmin : IsMinOn (f z) (Set.Ioo (0 : ℝ) 1) z :=
    hconv.isMinOn_of_rightDeriv_eq_zero hzmem hderiv0
  have hfz : f z z = 0 := by
    unfold f klBinary sqDistBinary
    simp [phi]
  have hfy : 0 ≤ f z y := by
    have hmin' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f z z ≤ f z x := (isMinOn_iff).1 hmin
    have hzy : f z z ≤ f z y := hmin' y (by simpa using hy)
    simpa [hfz] using hzy
  unfold f at hfy
  linarith

/-- A closed-interval variant of `sqDistBinary_le_klBinary` in the first argument.

This is convenient when connecting the inequality to conditional probabilities, which may take the
boundary values `0` and `1`. -/
theorem sqDistBinary_le_klBinary_Icc_left {y z : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Ioo (0 : ℝ) 1) : sqDistBinary y z ≤ klBinary y z := by
  -- Let `g(y) = klBinary y z - sqDistBinary y z`. We know `g ≥ 0` on `(0,1)` from the previous theorem.
  let g : ℝ → ℝ := fun y => klBinary y z - sqDistBinary y z
  have hg_cont : Continuous g := by
    have : Continuous (f z) := by
      unfold f klBinary phi sqDistBinary
      fun_prop
    simpa [g, f] using this
  have hClosed : IsClosed {y : ℝ | 0 ≤ g y} :=
    (isClosed_Ici.preimage hg_cont)
  have hIn : Set.Ioo (0 : ℝ) 1 ⊆ {y : ℝ | 0 ≤ g y} := by
    intro y hy'
    have : sqDistBinary y z ≤ klBinary y z := sqDistBinary_le_klBinary (y := y) (z := z) hy' hz
    dsimp [g]
    linarith
  have hy_cl : y ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    -- `closure (0,1) = [0,1]`.
    have : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
      closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)
    simpa [this] using hy
  have : y ∈ {y : ℝ | 0 ≤ g y} := by
    have : closure (Set.Ioo (0 : ℝ) 1) ⊆ {y : ℝ | 0 ≤ g y} :=
      closure_minimal hIn hClosed
    exact this hy_cl
  dsimp [g] at this
  linarith

end Entropy

end Mettapedia.Logic.UniversalPrediction
