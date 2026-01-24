import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Shore–Johnson: two-block transport lemmas

This module collects structural lemmas about the two-block embedding and its interaction
with `shift2`.  It is meant to be a clean, reusable bridge between the constraint language
and the Appendix calculus, in a style suitable for eventual mathlib inclusion.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TwoBlock

open Classical
open scoped BigOperators
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer
open _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective

theorem shift2_twoBlock_inr
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i j : Fin n) (k : Fin m) (t : ℝ) :
    shift2 (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) t
        (inrFin (n := n) (m := m) k) =
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inrFin (n := n) (m := m) k) := by
  have hki :
      inrFin (n := n) (m := m) k ≠ inlFin (n := n) (m := m) i := by
    intro h
    exact (_root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints.inlFin_ne_inrFin
      (n := n) (m := m) i k) h.symm
  have hkj :
      inrFin (n := n) (m := m) k ≠ inlFin (n := n) (m := m) j := by
    intro h
    exact (_root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints.inlFin_ne_inrFin
      (n := n) (m := m) j k) h.symm
  simp [shift2, hki, hkj]

theorem shift2_twoBlock_inl
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i j k : Fin n) (t : ℝ) :
    shift2 (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) t
        (inlFin (n := n) (m := m) k) =
      (if k = i then t
      else if k = j then
        w * P₁.p i + w * P₁.p j - t
      else
        w * P₁.p k) := by
  classical
  by_cases hki : k = i
  · subst hki
    simp [shift2]
  · by_cases hkj : k = j
    · have hij : i ≠ j := by
        intro h
        apply hki
        exact hkj.trans h.symm
      simp [shift2, hkj, inlFin_eq_inlFin, twoBlock_apply_inl]
    · simp [shift2, hki, hkj, inlFin_eq_inlFin, twoBlock_apply_inl]

theorem sum_twoBlock_left
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) :
    (∑ i : Fin n,
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p (inlFin (n := n) (m := m) i)) = w := by
  classical
  calc
    (∑ i : Fin n,
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p (inlFin (n := n) (m := m) i))
        = ∑ i : Fin n, w * P₁.p i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [twoBlock_apply_inl]
    _ = w * (∑ i : Fin n, P₁.p i) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := w) (f := fun i => P₁.p i)).symm
    _ = w := by simp [P₁.sum_one]

theorem sum_twoBlock_right
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) :
    (∑ i : Fin m,
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p (inrFin (n := n) (m := m) i)) = (1 - w) := by
  classical
  calc
    (∑ i : Fin m,
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p (inrFin (n := n) (m := m) i))
        = ∑ i : Fin m, (1 - w) * P₂.p i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [twoBlock_apply_inr]
    _ = (1 - w) * (∑ i : Fin m, P₂.p i) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := (1 - w)) (f := fun i => P₂.p i)).symm
    _ = (1 - w) := by simp [P₂.sum_one]

theorem twoBlock_pos_inl_of_pos
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i : Fin n)
    (hpos : ∀ k, 0 < P₁.p k) :
    0 < (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
      (inlFin (n := n) (m := m) i) := by
  have : 0 < w * P₁.p i := mul_pos hw0 (hpos i)
  simpa [twoBlock_apply_inl] using this

theorem twoBlock_pos_inr_of_pos
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i : Fin m)
    (hpos : ∀ k, 0 < P₂.p k) :
    0 < (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
      (inrFin (n := n) (m := m) i) := by
  have h1w : 0 < 1 - w := sub_pos.mpr hw1
  have : 0 < (1 - w) * P₂.p i := mul_pos h1w (hpos i)
  simpa [twoBlock_apply_inr] using this

theorem shift2_twoBlock_inl_scaled
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i j k : Fin n) (u : ℝ) :
    shift2 (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) (w * u)
        (inlFin (n := n) (m := m) k) =
      w * (shift2 P₁.p i j u k) := by
  classical
  by_cases hki : k = i
  · subst hki
    simp [shift2]
  · by_cases hkj : k = j
    · have hij : i ≠ j := by
        intro h
        apply hki
        exact hkj.trans h.symm
      -- Both sides simplify to `w * (P₁.p i + P₁.p j - u)`.
      simp [shift2, hkj, inlFin_eq_inlFin, twoBlock_apply_inl]
      ring_nf
    · simp [shift2, hki, hkj, inlFin_eq_inlFin, twoBlock_apply_inl]

theorem satisfies_liftLeftScaled_twoBlock_iff
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (c : EVConstraint n) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (liftLeftScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂) ↔
      satisfies c P₁ := by
  have hwne : w ≠ 0 := ne_of_gt hw0
  constructor
  · intro hsat
    have hEq :
        w * (∑ i : Fin n, P₁.p i * c.coeff i) = w * c.rhs := by
      exact (satisfies_liftLeftScaled_of_twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        c P₁ P₂).1 hsat
    have hsum : (∑ i : Fin n, P₁.p i * c.coeff i) = c.rhs :=
      mul_left_cancel₀ hwne hEq
    simpa [satisfies] using hsum
  · intro hsat
    have hEq : w * (∑ i : Fin n, P₁.p i * c.coeff i) = w * c.rhs := by
      simpa [satisfies] using congrArg (fun x => w * x) hsat
    exact (satisfies_liftLeftScaled_of_twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
      c P₁ P₂).2 hEq

theorem satisfies_liftRightScaled_twoBlock_iff
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (c : EVConstraint m) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (liftRightScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂) ↔
      satisfies c P₂ := by
  have h1w_pos : 0 < 1 - w := sub_pos.mpr hw1
  have h1w_ne : 1 - w ≠ 0 := ne_of_gt h1w_pos
  constructor
  · intro hsat
    have hEq :
        (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i) = (1 - w) * c.rhs := by
      exact (satisfies_liftRightScaled_of_twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        c P₁ P₂).1 hsat
    have hsum : (∑ i : Fin m, P₂.p i * c.coeff i) = c.rhs :=
      mul_left_cancel₀ h1w_ne hEq
    simpa [satisfies] using hsum
  · intro hsat
    have hEq : (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i) = (1 - w) * c.rhs := by
      simpa [satisfies] using congrArg (fun x => (1 - w) * x) hsat
    exact (satisfies_liftRightScaled_of_twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
      c P₁ P₂).2 hEq

theorem hasDerivAt_comp_mul_left {f : ℝ → ℝ} {w x L : ℝ}
    (hf : HasDerivAt f L (w * x)) :
    HasDerivAt (fun u : ℝ => f (w * u)) (w * L) x := by
  have hmul : HasDerivAt (fun u : ℝ => u * w) w x := by
    simpa using (hasDerivAt_mul_const (c := w) (x := x))
  have hmul' : HasDerivAt (fun u : ℝ => w * u) w x := by
    simpa [mul_comm] using hmul
  -- Composition gives derivative `L * w`, which equals `w * L` over `ℝ`.
  simpa [mul_comm, mul_left_comm, mul_assoc] using (hf.comp x hmul')

theorem hasDerivAt_shift2ProbClamp_scaled
    {F : ObjectiveFunctional} {n : ℕ} (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j) (w u0 : ℝ)
    (hqi : q.p i = w * u0) {L : ℝ}
    (h : HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)) :
    HasDerivAt (fun u => F.D (shift2ProbClamp q i j hij (w * u)) p) (w * L) u0 := by
  have hf :
      HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (w * u0) := by
    simpa [hqi] using h
  simpa using (hasDerivAt_comp_mul_left (f := fun t => F.D (shift2ProbClamp q i j hij t) p)
    (w := w) (x := u0) (L := L) hf)

theorem shift2ProbClamp_twoBlock_inl_of_mem
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (i j : Fin n) (hij : i ≠ j) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ P₁.p i + P₁.p j) :
    shift2ProbClamp
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
        (by
          intro h
          exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h))
        (w * u) =
      ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        (shift2Prob P₁ i j hij u hu0 hu1) P₂ := by
  -- Reduce to coordinate equality.
  apply ProbDist.ext
  intro k
  classical
  -- Show the clamp is identity at `w*u` for the two-block distribution.
  have hw0' : 0 ≤ w := le_of_lt hw0
  have ht0 : 0 ≤ w * u := mul_nonneg hw0' hu0
  have ht1 : w * u ≤
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
        (inlFin (n := n) (m := m) i) +
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
        (inlFin (n := n) (m := m) j) := by
    -- Right side is `w * (P₁.p i + P₁.p j)`.
    have hsum :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
            (inlFin (n := n) (m := m) i) +
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
            (inlFin (n := n) (m := m) j)
          = w * (P₁.p i + P₁.p j) := by
      calc
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
            (inlFin (n := n) (m := m) i) +
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
            (inlFin (n := n) (m := m) j)
            = w * P₁.p i + w * P₁.p j := by
                simp [twoBlock_apply_inl]
        _ = w * (P₁.p i + P₁.p j) := by
                ring
    -- Now use `hu1`.
    have : w * u ≤ w * (P₁.p i + P₁.p j) :=
      mul_le_mul_of_nonneg_left hu1 hw0'
    simpa [hsum] using this
  have hclamp :
      shift2Clamp
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) (w * u) = w * u :=
    shift2Clamp_eq_of_mem
      (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
      (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
      (t := w * u) ht0 ht1
  -- Also clamp is identity for the left block at `u`.
  have hclamp_left : shift2Clamp P₁ i j u = u :=
    shift2Clamp_eq_of_mem (q := P₁) (i := i) (j := j) (t := u) hu0 hu1
  -- Split by block membership.
  cases h : (finSumFinEquiv (m := n) (n := m)).symm k with
  | inl k₁ =>
      have hk : k = inlFin (n := n) (m := m) k₁ := by
        simpa [inlFin] using congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
      subst hk
      -- Left block: use scaled shift2 formula.
      simp [shift2ProbClamp_apply, hclamp, shift2_twoBlock_inl_scaled, twoBlock_apply_inl, shift2Prob]
  | inr k₂ =>
      have hk : k = inrFin (n := n) (m := m) k₂ := by
        simpa [inrFin] using congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
      subst hk
      -- Right block: shift2 does not change right coordinates.
      simp [shift2ProbClamp_apply, hclamp, shift2_twoBlock_inr, twoBlock_apply_inr, shift2Prob]

theorem shift2ProbClamp_eq_shift2Prob_of_mem
    {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) :
    shift2ProbClamp q i j hij t = shift2Prob q i j hij t ht0 ht1 := by
  apply ProbDist.ext
  intro k
  have hclamp : shift2Clamp q i j t = t := shift2Clamp_eq_of_mem q i j t ht0 ht1
  simp [shift2ProbClamp_apply, shift2Prob, hclamp]

theorem hasDerivAt_twoBlock_left_shift2ProbClamp
    {F : ObjectiveFunctional} {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (p : ProbDist (n + m))
    (i j : Fin n) (hij : i ≠ j) (u0 : ℝ)
    (hqi :
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
        (inlFin (n := n) (m := m) i) = w * u0)
    (hu0 : 0 < u0) (hu1 : u0 < P₁.p i + P₁.p j)
    {L : ℝ}
    (h :
      HasDerivAt
        (fun t =>
          F.D
            (shift2ProbClamp
              (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
              (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
              (by
                intro h'
                exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) t)
            p)
        L (w * u0)) :
    HasDerivAt
      (fun u =>
        F.D
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
            (shift2ProbClamp P₁ i j hij u) P₂) p)
      (w * L) u0 := by
  -- First scale the parameter in the `shift2ProbClamp` curve.
  have h' :
      HasDerivAt
        (fun t =>
          F.D
            (shift2ProbClamp
              (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
              (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
              (by
                intro h'
                exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) t)
            p)
        L
        ((ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
          (inlFin (n := n) (m := m) i)) := by
    simpa [hqi] using h
  have hscaled :
      HasDerivAt
        (fun u =>
          F.D
            (shift2ProbClamp
              (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
              (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
              (by
                intro h'
                exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) (w * u))
            p)
        (w * L) u0 :=
    hasDerivAt_shift2ProbClamp_scaled
      (p := p)
      (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
      (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
      (hij := by
        intro h'
        exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h'))
      (w := w) (u0 := u0) (hqi := hqi) h'
  -- Show the two curves are eventually equal near `u0`.
  have hEvent : ∀ᶠ u in nhds u0, 0 ≤ u ∧ u ≤ P₁.p i + P₁.p j := by
    have hIcc : Set.Icc (0 : ℝ) (P₁.p i + P₁.p j) ∈ nhds u0 :=
      Icc_mem_nhds hu0 hu1
    refine Filter.eventually_of_mem hIcc ?_
    intro u hu
    exact ⟨hu.1, hu.2⟩
  have hEq :
      (fun u =>
        F.D
          (shift2ProbClamp
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
            (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
            (by
              intro h'
              exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) (w * u))
          p)
        =ᶠ[nhds u0]
      (fun u =>
        F.D
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
            (shift2ProbClamp P₁ i j hij u) P₂) p) := by
    refine hEvent.mono ?_
    intro u hu
    have hclamp :
        shift2ProbClamp
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
            (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
            (by
              intro h'
              exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) (w * u)
          =
          ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
            (_root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix.shift2Prob
              P₁ i j hij u hu.1 hu.2) P₂ :=
      shift2ProbClamp_twoBlock_inl_of_mem
        (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := P₁) (P₂ := P₂)
        (i := i) (j := j) (hij := hij) (u := u) (hu0 := hu.1) (hu1 := hu.2)
    have hclamp' :
        _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix.shift2Prob
            P₁ i j hij u hu.1 hu.2
          =
          shift2ProbClamp P₁ i j hij u :=
      (shift2ProbClamp_eq_shift2Prob_of_mem (q := P₁) (i := i) (j := j) (hij := hij)
        (t := u) (ht0 := hu.1) (ht1 := hu.2)).symm
    -- Rewrite by the pointwise equality.
    simp [hclamp, hclamp']
  exact hscaled.congr_of_eventuallyEq hEq.symm

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TwoBlock
